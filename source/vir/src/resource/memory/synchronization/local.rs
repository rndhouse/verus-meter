//! Local mutex ownership and the normal-return interval of a blocking lock.
//! Both Ok and Poisoned own the acquisition. Neither outcome establishes a
//! payload invariant, and blocking retains the caller's entire pre-call footprint.

use super::{Acquisition, Instance, Operation};
use crate::ast::*;
use crate::resource::memory::{
    accounting::Accounting,
    analysis::Analysis,
    heap::{Owner, OwnerSlot},
    model::unsupported,
    paths,
    transfer::checked,
};

/// An interval belongs to one instance. Its occurrence binder is local to
/// the checked body, including its worker and enclosing source loop visits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in super::super) struct Interval {
    pub(in super::super) instance: Instance,
    pub(in super::super) acquisition: Acquisition,
}

/// Dynamic visits to one checked native constructor or acquisition. Worker
/// publication coordinates precede the enclosing loops of the actor itself.
#[derive(Clone)]
pub(in super::super) struct Occurrence {
    pub(in super::super) site: super::super::concurrency::sites::Binding<Operation>,
    pub(in super::super) actor: Option<super::super::workers::WorkerId>,
    pub(in super::super) coordinates: Vec<(u64, Expr)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum Owned {
    Mutex(Instance),
    Guard(Interval),
    /// A try-lock Result or Err value owns the acquisition only on acquiring paths.
    Attempt(Interval),
}

impl Owned {
    pub(in super::super) fn interval(self) -> Option<Interval> {
        match self {
            Self::Guard(interval) | Self::Attempt(interval) => Some(interval),
            Self::Mutex(_) => None,
        }
    }
}

/// Entering a potentially blocking acquire and ending an acquisition are
/// observations even when no allocation occurs at the transition.
#[derive(Clone, Copy, Default)]
pub(in super::super) enum Boundary {
    Wait(Interval),
    Attempt(Interval),
    #[default]
    Live,
    Release(Interval),
    /// Complete pre-cleanup storage under every source-permitted field order.
    UnorderedCleanup,
}

#[derive(Clone, Default)]
pub(in super::super) struct Condition {
    pub(in super::super) held: Vec<Interval>,
    pub(in super::super) boundary: Boundary,
}

impl Owner {
    pub(in super::super) fn mutex_instance(&self) -> Option<Instance> {
        match self.synchronization {
            Some(Owned::Mutex(instance)) => Some(instance),
            _ => None,
        }
    }
}

impl Analysis<'_> {
    fn synchronization_occurrence(&self, expr: &Expr, op: Operation) -> Result<Occurrence, VirErr> {
        let site = self
            .concurrency
            .synchronization_sites
            .get(&expr.span.id)
            .filter(|site| site.operation == op && site.anchor == expr.span.id)
            .ok_or_else(|| {
                unsupported(
                    &expr.span,
                    "a synchronization effect without its executable primitive call",
                )
            })?;
        let local = self.local_occurrences(&expr.span)?;
        if !local.iter().map(|(site, _)| *site).eq(site.iterations.iter().map(|visit| visit.site)) {
            return Err(unsupported(
                &expr.span,
                "a synchronization site without its local loop occurrence",
            ));
        }
        let mut coordinates = self
            .current_worker
            .and_then(|actor| self.growth.worker_occurrences.get(&actor))
            .cloned()
            .unwrap_or_default();
        coordinates.extend(local);
        Ok(Occurrence { site: site.clone(), actor: self.current_worker, coordinates })
    }

    fn mutex_receiver(&self, argument: &Expr) -> Option<Instance> {
        match &argument.x {
            ExprX::ReadPlace(place, _) => {
                let typ = paths::referent(&place.typ);
                if let Some((name, path)) = paths::place(place, typ)
                    && let Some(owner) = self.heap.root(&name).and_then(|root| root.at(&path))
                {
                    if self.layouts.mutex_payload(typ).is_some() {
                        return owner.mutex_instance();
                    }
                    if let TypX::Decorate(TypDecoration::Arc, _, payload) = &**typ
                        && self.layouts.mutex_payload(payload).is_some()
                    {
                        return self.heap.shared.mutex_instance(owner.shared?);
                    }
                }
                // Autoderef can retain the borrowed Arc as the operand of a
                // temporary reference. Follow that borrow to its canonical root.
                if let PlaceX::Temporary(value) = &place.x {
                    return self.mutex_receiver(value);
                }
                None
            }
            ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. }
                if attrs.resource_intrinsic
                    == Some(ResourceIntrinsic::Concurrency(
                        super::super::concurrency::Operation::ArcBorrow,
                    )) =>
            {
                let [source] = args.as_slice() else { return None };
                self.mutex_receiver(source)
            }
            _ => None,
        }
    }

    pub(in super::super) fn synchronization_owner(
        &mut self,
        expr: &Expr,
    ) -> Result<Option<Owner>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(None);
        };
        let Some(ResourceIntrinsic::Synchronization(operation)) = attrs.resource_intrinsic else {
            return Ok(None);
        };
        let [argument] = args.as_slice() else {
            return Err(unsupported(&expr.span, "this synchronization operation signature"));
        };
        match operation {
            Operation::MutexNew => {
                let payload = self
                    .layouts
                    .mutex_payload(&expr.typ)
                    .filter(|payload| crate::ast_util::types_equal(payload, &argument.typ))
                    .ok_or_else(|| {
                        unsupported(&expr.span, "inconsistent standard mutex payload")
                    })?;
                // The destination already pays for the mutex state and inline payload.
                // Preserve the original allocation tree under the single protected root.
                self.initialize_expr(argument)?;
                let instance = Instance::Fresh(Accounting::fresh_allocation());
                let mut owner =
                    Owner { synchronization: Some(Owned::Mutex(instance)), ..Owner::default() };
                let slot = if self.layouts.owner(payload) {
                    let mut child = self.result_owner.take().ok_or_else(|| {
                        unsupported(&expr.span, "mutex construction without its payload ownership")
                    })?;
                    self.freeze_owner_geometry(argument, &mut child);
                    owner.children.insert(OwnerSlot::Contents, child);
                    Some(OwnerSlot::Contents)
                } else {
                    None
                };
                self.transitions.operation(
                    &expr.span,
                    checked::Operation::MutexNew {
                        payload: argument.clone(),
                        slot,
                        instance,
                        occurrence: self.synchronization_occurrence(expr, operation)?,
                    },
                );

                Ok(Some(owner))
            }
            Operation::MutexLock | Operation::MutexTryLock => {
                let instance = self.mutex_receiver(argument).ok_or_else(|| {
                    unsupported(&expr.span, "a lock without a checked mutex instance")
                })?;
                self.discard(argument)?;
                let interval =
                    Interval { instance, acquisition: Acquisition(Accounting::fresh_allocation()) };
                let contract = operation.acquisition_contract().expect("native lock");
                self.storage.acquire_interval(&expr.span, interval, contract)?;
                self.transitions.operation(
                    &expr.span,
                    checked::Operation::MutexLock {
                        receiver: argument.clone(),
                        interval,
                        occurrence: self.synchronization_occurrence(expr, operation)?,
                    },
                );
                Ok(Some(Owner {
                    synchronization: Some(if contract.may_block() {
                        Owned::Guard(interval)
                    } else {
                        Owned::Attempt(interval)
                    }),
                    ..Owner::default()
                }))
            }
            _ => Ok(None),
        }
    }
}

impl crate::resource::memory::accounting::Point {
    /// Only checked source binders in this actor can constrain its footprint.
    pub(in super::super) fn validate(
        &self,
        intervals: &std::collections::BTreeSet<Interval>,
    ) -> Result<(), VirErr> {
        let changed = match self.condition.boundary {
            Boundary::Wait(interval)
            | Boundary::Attempt(interval)
            | Boundary::Release(interval) => Some(interval),
            Boundary::Live | Boundary::UnorderedCleanup => None,
        };
        if changed.is_some_and(|interval| self.condition.held.contains(&interval))
            || self
                .condition
                .held
                .iter()
                .copied()
                .chain(changed)
                .any(|interval| !intervals.contains(&interval))
        {
            return Err(unsupported(
                &self.span,
                "a footprint without its local acquisition occurrence",
            ));
        }
        Ok(())
    }
}

impl Condition {
    pub(in super::super) fn diagnostic(
        &self,
        span: &crate::messages::Span,
        footprint: &crate::resource::memory::Footprint,
    ) -> Option<VirErrAs> {
        let phase = match self.boundary {
            Boundary::Attempt(_) => "before a mutex acquisition attempt",
            Boundary::Wait(_) => "while waiting for the mutex",
            Boundary::Release(_) => "at mutex release",
            Boundary::UnorderedCleanup => "during unordered capture or aggregate cleanup",
            Boundary::Live => return None,
        };
        let cost = crate::resource::memory::contracts::constant(&footprint.total())
            .map_or_else(|| "symbolic storage".to_string(), |bytes| format!("{bytes} live bytes"));
        Some(VirErrAs::Note(crate::messages::note(span, format!("memory {phase}: {cost}"))))
    }
}
