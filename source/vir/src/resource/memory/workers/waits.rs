//! A join retains its caller and target until collection. Track the actual
//! waiting actor: standard join can panic on self/cyclic joins, so a panic-free
//! domain cannot silently treat those cases as ordinary nontermination.
//! Other waits may still block forever; this is not a termination argument.

use super::super::{
    lifetime::{Storage, Value},
    model::unsupported,
};
use super::{Stage, WorkerId, Workers};
use crate::{ast::VirErr, messages::Span};
use std::collections::BTreeSet;

#[derive(Clone, PartialEq, Eq)]
pub(super) struct Waiter {
    /// None names this accounting scope's coordinator, not a new worker.
    actor: Option<WorkerId>,
    /// The consumed source handle remains an inline argument while waiting.
    handle: Value,
}

impl Workers {
    fn waiting_on(&self, actor: Option<WorkerId>) -> Option<WorkerId> {
        self.records.iter().find_map(|(id, worker)| {
            worker.waiter.as_ref().filter(|waiter| waiter.actor == actor).map(|_| *id)
        })
    }

    /// A blocked actor cannot execute a later source operation or complete.
    pub(super) fn blocked(&self, actor: Option<WorkerId>) -> bool {
        self.waiting_on(actor).is_some()
    }

    pub(super) fn wait(
        &mut self,
        id: WorkerId,
        actor: Option<WorkerId>,
        span: &Span,
        handle: Value,
    ) -> Result<(), VirErr> {
        let target =
            self.records.get(&id).ok_or_else(|| unsupported(span, "joining an unknown worker"))?;
        if target.detached.is_some() || target.waiter.is_some() {
            return Err(unsupported(span, "a detached or already consumed join handle"));
        }
        if let Some(actor) = actor
            && !self
                .records
                .get(&actor)
                .is_some_and(|worker| matches!(worker.stage, Stage::Running))
        {
            return Err(unsupported(span, "a join outside its live caller worker"));
        }
        if self.blocked(actor) {
            return Err(unsupported(span, "another join before the caller's pending join returns"));
        }
        // Follow currently outstanding waits, not historical or syntactic join
        // edges. Collecting a result ends its edge and permits later work.
        let mut cursor = id;
        let mut seen = BTreeSet::new();
        loop {
            if actor == Some(cursor) || !seen.insert(cursor) {
                return Err(unsupported(
                    span,
                    "self or cyclic joins in the panic-free accounting domain",
                ));
            }
            let Some(next) = self.waiting_on(Some(cursor)) else { break };
            cursor = next;
        }
        self.records.get_mut(&id).unwrap().waiter = Some(Waiter { actor, handle });
        Ok(())
    }

    /// Only the actor that actually waited can receive the completed storage.
    /// Removing this record ends that actor's wait, not the result's lifetime.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the TODO 05 join adapter consumes checked completion effects")
    )]
    pub(super) fn take_result(
        &mut self,
        id: WorkerId,
        actor: Option<WorkerId>,
        span: &Span,
    ) -> Result<(Storage, Value, u64), VirErr> {
        let worker =
            self.records.get(&id).ok_or_else(|| unsupported(span, "joining an unknown worker"))?;
        if worker.detached.is_some()
            || !worker.waiter.as_ref().is_some_and(|waiter| waiter.actor == actor)
            || !matches!(worker.stage, Stage::Completed(_))
        {
            return Err(unsupported(
                span,
                "join requires checked completion and its actual waiting caller",
            ));
        }
        let worker = self.records.remove(&id).unwrap();
        let Stage::Completed(result) = worker.stage else { unreachable!() };
        Ok((result, worker.waiter.unwrap().handle, worker.completion))
    }
}
