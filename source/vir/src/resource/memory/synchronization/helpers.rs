//! Substitute executable synchronization identities at a synchronous call.
//! Each local acquisition retains its callee binder and the enclosing call visit.
//! A borrowed guard names the caller's acquisition for its entire Rust borrow.

use super::{
    Acquisition, Instance,
    local::{Boundary, Condition, Interval, Owned, View},
    parameters::Parameter,
};
use crate::{
    ast::*,
    messages::Span,
    resource::memory::{
        accounting::Accounting,
        analysis::Analysis,
        heap::Owner,
        lifetime::Value,
        model::unsupported,
        summary::FunctionSummary,
        workers::{SourceVisit, WorkerId},
    },
};
use std::collections::{BTreeMap, BTreeSet};

/// An instantiated edge in the checked call graph. The original callee owns the
/// primitive site and its local loop coordinates; this site binds the outer visit.
#[derive(Clone)]
pub(in super::super) struct Call {
    visit: SourceVisit<u64>,
    instances: BTreeMap<Instance, Instance>,
    intervals: BTreeMap<Interval, Interval>,
    /// Formal incoming intervals are supplied by a real caller guard.
    incoming: BTreeSet<Interval>,
    borrowed: BTreeSet<Interval>,
    /// Residual disjointness requirements on the caller's own formal inputs.
    pub(in super::super) distinct_inputs: BTreeSet<(usize, usize)>,
    /// Actual acquisitions through which the body or a nested call accessed protected data.
    pub(in super::super) payload_borrows: BTreeSet<Interval>,
    /// A sole release in the callee, instantiated at this call even when the
    /// caller is another helper operating on a formal mutex parameter.
    closed: Option<(usize, Interval)>,
    /// Closed helper updates whose release uses the callee's checked output forest.
    published: bool,
    /// The native operation permits a non-acquiring result on these intervals.
    attempts: BTreeSet<Interval>,
}

impl Call {
    pub(in super::super) fn instantiate(
        analysis: &Analysis<'_>,
        expr: &Expr,
        summary: &FunctionSummary,
        values: &[Option<Value>],
        owners: &[Option<Owner>],
    ) -> Result<Option<Box<Self>>, VirErr> {
        let effects = summary
            .effects
            .as_ref()
            .ok_or_else(|| unsupported(&expr.span, "a call without checked body effects"))?;
        let inputs = &effects.ownership.synchronization_inputs;
        if inputs.0.is_empty()
            && !effects.ownership.locks_mutex()
            && summary.synchronized_result.is_none()
        {
            return Ok(None);
        }
        let mut call = Self {
            visit: analysis.source_visit(expr.span.id, analysis.local_occurrences(&expr.span)?),
            instances: BTreeMap::new(),
            intervals: BTreeMap::new(),
            incoming: inputs.intervals(),
            borrowed: BTreeSet::new(),
            distinct_inputs: BTreeSet::new(),
            closed: None,
            published: false,
            attempts: BTreeSet::new(),
            payload_borrows: BTreeSet::new(),
        };
        for (&index, &(parameter, formal)) in &inputs.0 {
            let actual = match parameter {
                Parameter::Mutex | Parameter::Guard => {
                    owners[index].as_ref().and_then(|o| o.synchronization)
                }
                Parameter::BorrowMutex | Parameter::BorrowGuard => {
                    match values[index].as_ref().and_then(|v| v.synchronization_view) {
                        Some(View::Mutex(id)) => Some(Owned::Mutex(id)),
                        Some(View::Guard(id)) => Some(Owned::Guard(id)),
                        _ => None,
                    }
                }
            };
            let (formal, actual) = match (formal, actual) {
                (Owned::Mutex(formal), Some(Owned::Mutex(actual))) => (formal, actual),
                (Owned::Guard(formal), Some(Owned::Guard(actual)))
                    if analysis.storage.holds_interval(actual) =>
                {
                    if parameter == Parameter::BorrowGuard {
                        call.borrowed.insert(actual);
                    }
                    call.intervals.insert(formal, actual);
                    (formal.instance, actual.instance)
                }
                _ => {
                    return Err(unsupported(
                        &expr.span,
                        "a helper argument without its required mutex or live guard identity",
                    ));
                }
            };
            call.instances.insert(formal, actual);
        }
        for &(left, right) in &effects.ownership.distinct_payload_inputs {
            let actual = |i| {
                call.instances.get(&Instance::Input(i)).copied().ok_or_else(|| {
                    unsupported(&expr.span, "a protected ownership requirement without an instance")
                })
            };
            let (left, right) = (actual(left)?, actual(right)?);
            if left == right {
                return Err(unsupported(
                    &expr.span,
                    "aliased protected payloads with independent helper updates",
                ));
            }
            if let (Instance::Input(a), Instance::Input(b)) = (left, right) {
                call.distinct_inputs.insert((a.min(b), a.max(b)));
            }
        }
        for profile in &summary.profiles {
            if let Boundary::Wait(interval) | Boundary::Attempt(interval) =
                profile.condition.boundary
            {
                if !call.intervals.contains_key(&interval) {
                    let instance = call.instance(interval.instance, &expr.span)?;
                    call.intervals.insert(
                        interval,
                        Interval {
                            instance,
                            acquisition: Acquisition(Accounting::fresh_allocation()),
                        },
                    );
                }
                if matches!(profile.condition.boundary, Boundary::Attempt(_)) {
                    call.attempts.insert(interval);
                }
            }
        }
        for formal in effects.ownership.payload_borrows() {
            let actual = call.intervals.get(&formal).ok_or_else(|| {
                unsupported(&expr.span, "a protected helper access without its acquisition")
            })?;
            call.payload_borrows.insert(*actual);
        }
        if let Some(Owned::Mutex(instance)) = summary.synchronized_result {
            call.instance(instance, &expr.span)?;
        }
        if let Some((parameter, formal)) = summary.closed_mutex {
            call.closed = Some((
                parameter,
                *call.intervals.get(&formal).ok_or_else(|| {
                    unsupported(&expr.span, "a helper release without its actual acquisition")
                })?,
            ));
        }
        Ok(Some(Box::new(call)))
    }

    fn instance(&mut self, formal: Instance, span: &Span) -> Result<Instance, VirErr> {
        if let Some(actual) = self.instances.get(&formal) {
            return Ok(*actual);
        }
        if matches!(formal, Instance::Input(_)) {
            return Err(unsupported(span, "an unbound synchronization input"));
        }
        let actual = Instance::Fresh(Accounting::fresh_allocation());
        self.instances.insert(formal, actual);
        Ok(actual)
    }

    pub(in super::super) fn validate(
        &self,
        site: u64,
        actor: Option<WorkerId>,
        intervals: &mut BTreeSet<Interval>,
        attempts: &mut BTreeSet<Interval>,
        span: &Span,
    ) -> Result<(), VirErr> {
        if self.visit.site != site || !self.visit.valid_for(actor) {
            return Err(unsupported(span, "a helper acquisition outside its calling occurrence"));
        }
        for (formal, actual) in &self.intervals {
            if !self.incoming.contains(formal) && !intervals.insert(*actual) {
                return Err(unsupported(span, "a reused helper acquisition binder"));
            }
            if self.attempts.contains(formal) {
                attempts.insert(*actual);
            }
        }
        Ok(())
    }

    /// An interval introduced by this checked call has one caller-visible
    /// occurrence on return. Incoming guard arguments keep their original visit.
    pub(in super::super) fn acquires_at_visit(
        &self,
        id: Interval,
        access: &SourceVisit<u64>,
    ) -> bool {
        self.visit.same_visit_scope(access)
            && (!self.payload_borrows.contains(&id)
                || self.published_section().is_some_and(|(_, actual)| actual == id))
            && self
                .intervals
                .iter()
                .any(|(formal, actual)| *actual == id && !self.incoming.contains(formal))
    }

    pub(in super::super) fn single_release(&self) -> Option<Interval> {
        self.closed.filter(|_| self.visit.single_visit()).map(|(_, interval)| interval)
    }

    pub(in super::super) fn publish_section(
        &mut self,
        parameter: usize,
        span: &Span,
    ) -> Result<Interval, VirErr> {
        let Some((_, interval)) = self.closed.filter(|(index, _)| *index == parameter) else {
            return Err(unsupported(span, "a shared release without its checked helper parameter"));
        };
        self.published = true;
        Ok(interval)
    }

    pub(in super::super) fn published_section(&self) -> Option<(usize, Interval)> {
        self.closed.filter(|_| self.published)
    }

    pub(in super::super) fn has_fresh_acquisitions(&self) -> bool {
        self.intervals.keys().any(|formal| !self.incoming.contains(formal))
    }

    pub(in super::super) fn has_intervals(&self) -> bool {
        !self.intervals.is_empty()
    }

    pub(in super::super) fn result(&self, formal: Owned) -> Owned {
        match formal {
            Owned::Mutex(id) => Owned::Mutex(self.instances[&id]),
            Owned::Guard(id) => Owned::Guard(self.intervals[&id]),
            Owned::Attempt(id) => Owned::Attempt(self.intervals[&id]),
            Owned::GuardOption(tag) => Owned::GuardOption(tag.substitute(|id| self.intervals[&id])),
        }
    }

    pub(in super::super) fn incoming_actuals(&self) -> impl Iterator<Item = Interval> + '_ {
        self.incoming.iter().map(|id| self.intervals[id])
    }

    pub(in super::super) fn consumed(&self) -> impl Iterator<Item = Interval> + '_ {
        self.incoming_actuals().filter(|id| !self.borrowed.contains(id))
    }

    /// Contract slack can rely only on an incoming acquisition held throughout.
    pub(in super::super) fn allowance(
        &self,
        profiles: &[crate::resource::memory::lifetime::Profile],
    ) -> Condition {
        Condition {
            held: self
                .incoming
                .iter()
                .filter(|id| profiles.iter().all(|p| p.condition.held.contains(id)))
                .map(|id| self.intervals[id])
                .collect(),
            boundary: Boundary::Live,
        }
    }

    pub(in super::super) fn condition(&self, condition: &Condition) -> Condition {
        let interval = |id: Interval| self.intervals[&id];
        Condition {
            held: condition.held.iter().copied().map(interval).collect(),
            boundary: match condition.boundary {
                Boundary::Wait(id) => Boundary::Wait(interval(id)),
                Boundary::Attempt(id) => Boundary::Attempt(interval(id)),
                Boundary::Release(id) => Boundary::Release(interval(id)),
                other => other,
            },
        }
    }
}
