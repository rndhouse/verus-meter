//! Observe the same path and byte expression as ordinary source accounting.
//! A blocked caller retains its storage. Unlock changes the phase constraint
//! even if every byte in the previous phase remains live.

use super::{Accounting, MemoryReport};
use crate::resource::memory::{
    model::unsupported,
    synchronization::local::{Boundary, Interval},
};
use crate::{ast::VirErr, messages::Span};

impl Accounting {
    /// The formal guard already exists when execution enters this function.
    pub(in super::super) fn enter_guard(&mut self, interval: Interval) {
        for path in &mut self.paths {
            path.held.insert(interval);
        }
    }

    pub(in super::super) fn check_exit_intervals(
        &self,
        span: &Span,
        borrowed: &std::collections::BTreeSet<Interval>,
        result: Option<super::super::synchronization::local::Owned>,
    ) -> Result<(), VirErr> {
        use super::super::synchronization::local::Owned;
        for path in &self.paths {
            let mut expected = borrowed.clone();
            match result {
                Some(Owned::Guard(id)) => {
                    expected.insert(id);
                }
                Some(Owned::Attempt(id)) if path.held.contains(&id) => {
                    expected.insert(id);
                }
                _ => {}
            }
            if expected != path.held {
                return Err(unsupported(
                    span,
                    "an acquisition surviving without a checked outgoing guard",
                ));
            }
        }
        Ok(())
    }

    /// Commit a checked synchronous exit. Caller-only acquisitions survive the call.
    pub(in super::super) fn commit_call_intervals(
        &mut self,
        span: &Span,
        call: &super::super::synchronization::helpers::Call,
        result: Option<super::super::synchronization::local::Owned>,
    ) -> Result<(), VirErr> {
        use super::super::synchronization::local::Owned;
        let mut acquired = Vec::new();
        for path in &mut self.paths {
            for id in call.consumed() {
                path.held.remove(&id);
            }
            if let Some(Owned::Guard(id)) = result {
                if path.held.iter().any(|held| held.instance == id.instance && *held != id) {
                    return Err(unsupported(
                        span,
                        "a returned guard conflicting with a held mutex",
                    ));
                }
                path.held.insert(id);
            } else if let Some(Owned::Attempt(id)) = result
                && !path.held.iter().any(|held| held.instance == id.instance)
            {
                let mut success = path.clone();
                success.held.insert(id);
                acquired.push(success);
            }
        }
        if self.paths.len() + acquired.len() > 1024 {
            return Err(unsupported(span, "more than 1024 helper-exit ownership alternatives"));
        }
        self.paths.extend(acquired);
        Ok(())
    }

    /// Destruction can only release these existing owners. Before visiting
    /// the children in any implementation order, cover their combined storage
    /// with every potentially ending acquisition removed from the condition.
    /// Keep the authoritative held set until the respective destructor executes.
    pub(in super::super) fn cover_unordered_cleanup<'a>(
        &mut self,
        span: &Span,
        children: impl Iterator<Item = &'a super::super::heap::Owner>,
    ) {
        if self.paths.iter().all(|path| path.held.is_empty()) {
            return;
        }
        let mut ending = std::collections::BTreeSet::new();
        let mut shared = false;
        let count = children
            .inspect(|child| {
                child.visit(&mut |owner| {
                    if let Some(interval) = owner
                        .synchronization
                        .and_then(super::super::synchronization::local::Owned::interval)
                    {
                        ending.insert(interval);
                    }
                    // Destruction of a final strong link may also destroy its backing.
                    shared |= owner.shared.is_some();
                })
            })
            .count();
        if count < 2 || (!shared && ending.is_empty()) {
            return;
        }
        for mut path in self.paths.clone() {
            let original = path.held.len();
            path.held.retain(|guard| !shared && !ending.contains(guard));
            if path.held.len() != original {
                self.record_phase(
                    span,
                    Self::path_expression(&path, span),
                    &path,
                    Boundary::UnorderedCleanup,
                );
            }
        }
    }

    pub(in super::super) fn acquire_interval(
        &mut self,
        span: &Span,
        interval: Interval,
        contract: super::super::synchronization::Contract,
    ) -> Result<(), VirErr> {
        let holds_mutex =
            |path: &super::Live| path.held.iter().any(|held| held.instance == interval.instance);
        if contract.may_block() && self.paths.iter().any(holds_mutex) {
            return Err(unsupported(span, "reentrant blocking acquisition of a held mutex"));
        }
        let mut acquired = Vec::new();
        let before = std::mem::take(&mut self.paths);
        for path in &before {
            let boundary = if contract.may_block() {
                Boundary::Wait(interval)
            } else {
                Boundary::Attempt(interval)
            };
            self.record_phase(span, Self::path_expression(path, span), path, boundary);
            if !holds_mutex(path) {
                let mut path = path.clone();
                path.held.insert(interval);
                acquired.push(path);
            }
        }
        if !contract.may_block() {
            // WouldBlock owns no guard. Keep the entire prior ledger on this path.
            if before.len() + acquired.len() > 1024 {
                return Err(unsupported(span, "more than 1024 try-lock ownership alternatives"));
            }
            self.paths = before;
        }
        self.paths.extend(acquired);
        self.record_live(span)
    }

    /// Keep each caller path paired with its actual acquisitions. A spawned
    /// body receives only the captured storage, never its publisher's held set.
    pub(in super::super) fn worker_frame(
        &mut self,
        span: &Span,
        phase: super::super::workers::states::Phase,
        project: impl Fn(super::Footprint) -> super::Footprint,
    ) -> super::Footprint {
        if !self.holding_any() {
            return project(self.live_expression(span));
        }
        let paths = self.paths.clone();
        paths
            .into_iter()
            .map(|path| {
                let cost = project(Self::path_expression(&path, span));
                self.record_phase(span, cost.clone(), &path, Boundary::Worker(phase));
                cost
            })
            .reduce(|left, right| left.maximum(span, right))
            .expect("a held acquisition has a live path")
    }

    pub(in super::super) fn holds_interval(&self, interval: Interval) -> bool {
        !self.paths.is_empty() && self.paths.iter().all(|path| path.held.contains(&interval))
    }

    /// Narrow only at an executable result variant or a verified unwrap.
    pub(in super::super) fn select_interval(&mut self, interval: Interval, acquired: bool) -> bool {
        self.paths.retain(|path| path.held.contains(&interval) == acquired);
        !self.paths.is_empty()
    }

    pub(in super::super) fn release_interval(&mut self, span: &Span, interval: Interval) {
        for index in 0..self.paths.len() {
            let path = &mut self.paths[index];
            if path.held.remove(&interval) {
                let path = path.clone();
                self.record_phase(
                    span,
                    Self::path_expression(&path, span),
                    &path,
                    Boundary::Release(interval),
                );
            }
        }
    }
}

impl MemoryReport {
    /// Trace only acquisition boundaries. Their byte terms are the same terms
    /// used for ordinary memory obligations, including surviving storage.
    pub fn interval_diagnostics(&self) -> Vec<crate::ast::VirErrAs> {
        self.points
            .iter()
            .filter_map(|point| point.condition.diagnostic(&point.span, &point.cost))
            .collect()
    }
}
