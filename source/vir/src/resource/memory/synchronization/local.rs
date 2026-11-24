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

/// A mutex construction or acquisition retains its checked native operation.
pub(in super::super) type Occurrence =
    super::super::workers::SourceVisit<super::super::concurrency::sites::Binding<Operation>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum Owned {
    Mutex(Instance),
    Guard(Interval),
    /// A try-lock Result or Err value owns the acquisition only on acquiring paths.
    Attempt(Interval),
    /// The executable Option discriminant controls this guard's release duty.
    GuardOption(super::optional::GuardOption),
}

/// Source borrows are views only. A guard view and a payload view retain the
/// same acquisition and never duplicate ownership or its storage.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in super::super) enum View {
    Mutex(Instance),
    Guard(Interval),
    Payload(Interval),
    /// A shared borrow of the initialized cell, issued by a verified reader.
    ReadPayload(u64),
}

impl Owned {
    pub(in super::super) fn interval(self) -> Option<Interval> {
        match self {
            Self::Guard(interval) | Self::Attempt(interval) => Some(interval),
            Self::GuardOption(tag) => tag.interval(),
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
    /// The caller owns its acquisitions at this native spawn or join.
    Worker(super::super::workers::states::Phase),
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
        Ok(self.source_visit(site.clone(), local))
    }

    /// Resolve a reference to an already known mutex. Stored references retain
    /// identity but never take ownership of the acquisition or protected bytes.
    pub(in super::super) fn synchronization_place(&self, place: &Place) -> Option<View> {
        let typ = paths::referent(&place.typ);
        if let Some((name, path)) = paths::place(place, typ) {
            if path.is_empty()
                && let Some(view) = self.slots.get(&name).and_then(|v| v.synchronization_view)
            {
                return Some(view);
            }
            if let Some(owner) = self.heap.root(&name).and_then(|root| root.at(&path)) {
                match owner.synchronization {
                    Some(Owned::Mutex(instance)) => return Some(View::Mutex(instance)),
                    Some(Owned::Guard(interval)) if self.layouts.guard_owner(typ) => {
                        return Some(View::Guard(interval));
                    }
                    _ => {}
                }
                if let TypX::Decorate(TypDecoration::Arc, _, payload) = &**typ
                    && self.layouts.mutex_payload(payload).is_some()
                {
                    return self.heap.shared.mutex_instance(owner.shared?).map(View::Mutex);
                }
            }
        }
        match &place.x {
            PlaceX::Temporary(value) => self.synchronization_view(value),
            PlaceX::DerefMut(base) => self.synchronization_place(base),
            _ => None,
        }
    }

    pub(in super::super) fn synchronization_view(&self, argument: &Expr) -> Option<View> {
        match &argument.x {
            ExprX::ReadPlace(place, _)
            | ExprX::BorrowMut(place)
            | ExprX::TwoPhaseBorrowMut(place) => self.synchronization_place(place),
            ExprX::Call { target: CallTarget::Fun(_, target, _, _, attrs), args, .. } => {
                let [source] = args.as_slice() else { return None };
                if self
                    .layouts
                    .template_sources
                    .get(target)
                    .and_then(|f| f.x.attrs.resource_template.as_ref())
                    .is_some_and(|s| s.method == super::WorkspaceMethod::Borrow)
                    && let Some(super::rw_payload::Location::Reader(id)) = self.rw_receiver(source)
                {
                    return Some(View::ReadPayload(id));
                }
                match attrs.resource_intrinsic {
                    Some(ResourceIntrinsic::Concurrency(
                        super::super::concurrency::Operation::ArcBorrow,
                    )) => self.synchronization_view(source),
                    Some(ResourceIntrinsic::Synchronization(
                        Operation::GuardBorrow | Operation::GuardBorrowMut,
                    )) => {
                        let View::Guard(interval) = self.synchronization_view(source)? else {
                            return None;
                        };
                        Some(View::Payload(interval))
                    }
                    _ => None,
                }
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
                    self.protect_vector_length(argument, &mut child);
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
                let Some(View::Mutex(instance)) = self.synchronization_view(argument) else {
                    return Err(unsupported(&expr.span, "a lock without a checked mutex instance"));
                };
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
            Boundary::Live | Boundary::UnorderedCleanup | Boundary::Worker(_) => None,
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
            Boundary::Worker(phase) => phase.description(),
            Boundary::Live => return None,
        };
        let cost = crate::resource::memory::contracts::constant(&footprint.total())
            .map_or_else(|| "symbolic storage".to_string(), |bytes| format!("{bytes} live bytes"));
        Some(VirErrAs::Note(crate::messages::note(span, format!("memory {phase}: {cost}"))))
    }
}
