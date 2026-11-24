//! Byte observations on the two sides of an asynchronous call. These are
//! templates at executable sites: a loop visit instantiates a publication,
//! and an actual handle selects a completion. Traversal order is not a schedule.

mod publication;

use super::{WorkerId, execution::Execution};
use crate::{
    ast::*,
    messages::Span,
    resource::memory::{
        accounting::{CheckKind, Obligation},
        analysis::Analysis,
        concurrency::sites::Binding,
        contracts,
        footprint::{Footprint, MemoryBudget, MemoryKind},
        model::unsupported,
    },
};
use std::collections::BTreeSet;

/// Source-visible caller phases. The worker starts with its own acquisitions.
#[derive(Clone, Copy)]
pub(in super::super) enum Phase {
    Fork,
    Published,
    Waiting,
    Ready,
    Resumed,
}

impl Phase {
    pub(in super::super) fn description(self) -> &'static str {
        match self {
            Self::Fork => "before transferring worker captures",
            Self::Published => "after transferring worker captures",
            Self::Waiting => "while waiting for a worker",
            Self::Ready => "while retaining a completed worker result",
            Self::Resumed => "after worker join",
        }
    }
}

/// The caller can remain here while the published child enters its body.
/// The child's separate entry ledger owns all moved captures. The caller
/// retains the handle slot, completion tag and other source temporaries.
pub(in super::super) struct Publication {
    pub(super) caller: Option<WorkerId>,
    site: Binding,
    pub(super) span: Span,
    pub(super) occurrence: Expr,
    caller_frame: Footprint,
    /// Before splitting the captures, each path contributes one combined cost.
    /// Independently maximizing the two resulting ledgers can mix paths.
    at_fork: Footprint,
}

/// Only this handle can resume this caller. Each visit selects a single
/// occurrence even when several worker families can supply the result.
pub(in super::super) struct Join {
    phases: JoinPhases,
    /// Checked result producers associated with the selected handle.
    pub(in super::super) families: BTreeSet<WorkerId>,
    /// Immutable record of the actual handle. A fixed handle without a
    /// descriptor names the one live publication in its ownership domain.
    record: Option<Expr>,
}

/// The same three states apply to a formal input handle. Such a helper
/// preserves its operand and wait edge without claiming a successful result.
pub(in super::super) struct JoinPhases {
    caller: Option<WorkerId>,
    site: Binding,
    span: Span,
    /// Caller frame after operand evaluation, including the consumed handle.
    waiting: Footprint,
    /// Caller and completed result coexist before either handle or tag retires.
    ready: Footprint,
    /// The result now belongs to the caller, including its native Result layout.
    resumed: Footprint,
}

impl JoinPhases {
    /// Keep a caller-relative helper trace attached to its executable join.
    pub(in super::super) fn at(&self, span: &Span) -> bool {
        self.site.anchor == span.id
    }

    pub(super) fn obligations(&self, bound: &Expr) -> impl Iterator<Item = Obligation> {
        [
            (&self.waiting, "while waiting for a worker"),
            (&self.ready, "while retaining a completed worker result"),
            (&self.resumed, "after worker join"),
        ]
        .into_iter()
        .map(|(frame, phase)| Obligation {
            span: self.span.clone(),
            cost: actor_cost(&self.span, frame.clone(), self.caller),
            bound: MemoryBudget::total(bound.clone()),
            kind: CheckKind::WorkerState(phase),
        })
    }
}

/// While complete, inline payload bytes belong to the heap completion record.
/// The owned allocations already have their own kinds and identities.
pub(super) fn completed(span: &Span, live: Footprint, inline: u64) -> Footprint {
    let bytes = contracts::literal(span, inline);
    live.reclassify(span, MemoryKind::host_local(), MemoryKind::host_heap(), bytes)
}

/// The worker's own tag lives in its publisher's ledger through completion.
/// Independent body costs exclude that ledger, including when the actor waits.
fn actor_cost(span: &Span, frame: Footprint, actor: Option<WorkerId>) -> Footprint {
    if actor.is_none() {
        return frame;
    }
    let tag = contracts::literal(span, verus_meter_model::completion_bytes(0).unwrap());
    frame.add(span, Footprint::charge(MemoryKind::host_heap(), tag))
}

impl Analysis<'_> {
    fn state_binding(&self, span: &Span, publish: bool) -> Result<Binding, VirErr> {
        self.concurrency
            .native_site(span.id)
            .filter(|site| {
                site.anchor == span.id
                    && if publish { site.operation.spawns() } else { site.operation.joins() }
            })
            .cloned()
            .ok_or_else(|| {
                unsupported(span, "a worker state without its executable spawn or join site")
            })
    }

    pub(super) fn publication_state(
        &mut self,
        span: &Span,
        actor: WorkerId,
        at_fork: Footprint,
    ) -> Result<Publication, VirErr> {
        Ok(Publication {
            caller: self.current_worker,
            site: self.state_binding(span, true)?,
            span: span.clone(),
            occurrence: self.worker_identity(span, actor),
            caller_frame: self.storage.worker_frame(span, Phase::Published, |cost| cost),
            at_fork,
        })
    }

    /// Use capture observations only after evaluating the spawn operand. This
    /// inequality describes a permitted overlap, not a completed child in the
    /// caller's current ledger.
    pub(super) fn check_publication_result(
        &mut self,
        execution: &Execution,
        descriptor: Option<&Expr>,
    ) {
        let publication = &execution.publication;
        let span = &publication.span;
        let mut check = |cost: Footprint, phase| {
            let obligation = Obligation {
                span: span.clone(),
                cost: actor_cost(span, cost, publication.caller),
                bound: MemoryBudget::total(self.bound.clone()),
                kind: CheckKind::WorkerState(phase),
            };
            if let Some(statement) = crate::resource::memory::symbolic::obligation(&obligation) {
                self.growth.after.entry(span.id).or_default().push(statement);
            }
        };
        // Reserving the tag already recorded the full coordinator frame at
        // this exact fork. A nested publisher additionally owes its own tag.
        if publication.caller.is_some() {
            check(publication.at_fork.clone(), "at worker publication");
        }
        if let Some(early) = execution.pre_return_footprint(span, descriptor) {
            let entry = execution.initial.live_expression(span);
            if matches!((contracts::constant(&early.total()), contracts::constant(&entry.total())),
                (Some(produced), Some(captured)) if produced <= captured)
            {
                return;
            }
            check(publication.caller_frame.add(span, early), "before spawn returns");
        }
    }

    pub(super) fn record_join(
        &mut self,
        span: &Span,
        families: BTreeSet<WorkerId>,
        record: Option<Expr>,
        waiting: Footprint,
        ready: Footprint,
    ) -> Result<(), VirErr> {
        let phases = self.join_phases(span, waiting, ready)?;
        self.growth.worker_joins.entry(span.id).or_default().push(Join {
            phases,
            families,
            record,
        });
        Ok(())
    }

    pub(super) fn join_phases(
        &mut self,
        span: &Span,
        waiting: Footprint,
        ready: Footprint,
    ) -> Result<JoinPhases, VirErr> {
        Ok(JoinPhases {
            caller: self.current_worker,
            site: self.state_binding(span, false)?,
            span: span.clone(),
            waiting,
            ready,
            resumed: self.storage.worker_frame(span, Phase::Resumed, |cost| cost),
        })
    }

    /// Check each observation in the lexical scope where its byte expressions
    /// are valid. Body costs stay attached to their source effects and graph.
    pub(super) fn state_obligations(&mut self) -> Result<(), VirErr> {
        let bound = MemoryBudget::total(self.bound.clone());
        let workers = &self.growth.worker_executions;
        let scope_matches = |actor: Option<WorkerId>, site: &Binding| {
            actor.is_none_or(|id| {
                workers.get(&id).is_some_and(|e| {
                    self.concurrency
                        .closures
                        .get(&e.definition)
                        .is_some_and(|closure| closure.function == site.scope)
                })
            })
        };
        for join in self.growth.worker_joins.values().flatten() {
            if !scope_matches(join.phases.caller, &join.phases.site)
                || join.families.is_empty()
                || join.families.iter().any(|actor| !workers.contains_key(actor))
                || (join.families.len() != 1 && join.record.is_none())
            {
                return Err(unsupported(
                    &join.phases.span,
                    "a join state without its selected worker",
                ));
            }
            let ownership =
                join.phases.caller.map_or(&self.transitions, |id| &workers[&id].effects.ownership);
            if let Some(super::super::transfer::checked::Operation::WorkerJoin {
                mutex_receipt: Some(receipt),
                ..
            }) = ownership.operation_at(&join.phases.span)
                && !receipt.matches_join(&join.families, join.record.as_ref(), &self.growth)
            {
                return Err(unsupported(
                    &join.phases.span,
                    "a mutex receipt without its selected producer",
                ));
            }
            // In the coordinator, receiving the payload records the intact
            // waiting frame before releasing the handle and tag. Packing the
            // Result records its new layout. Reuse those ordinary inequalities.
            if join.phases.caller.is_some() {
                self.obligations.extend(join.phases.obligations(&self.bound));
            } else if join
                .families
                .iter()
                .any(|id| workers[id].effects.ownership.protected_versions.result_root().is_some())
            {
                // The joined forest first belongs to the intact completion
                // record. Prove this phase before the handle and tag retire.
                self.obligations.push(Obligation {
                    span: join.phases.span.clone(),
                    cost: join.phases.ready.clone(),
                    bound: bound.clone(),
                    kind: CheckKind::WorkerState(Phase::Ready.description()),
                });
            }
        }
        for execution in workers.values() {
            let publication = &execution.publication;
            if !scope_matches(publication.caller, &publication.site) {
                return Err(unsupported(
                    &publication.span,
                    "a publication state outside its source worker",
                ));
            }
            // A composed worker already proves its local phases against the
            // exported costs. The whole-operation allowance is meaningful at
            // publication. A zero-capacity issuer can make a local phase unreachable.
            if self.storage.covers_workers() {
                continue;
            }
            // A synchronized execution exports every source phase, including
            // waiting and newly unrestricted storage at release. Preserve these
            // local checks independently of the whole-operation proof.
            for point in execution.effects.points.iter() {
                self.obligations.push(Obligation {
                    span: point.span.clone(),
                    cost: actor_cost(&point.span, point.cost.clone(), Some(execution.actor)),
                    bound: bound.clone(),
                    kind: CheckKind::WorkerState("during worker execution"),
                });
            }
        }
        Ok(())
    }
}
