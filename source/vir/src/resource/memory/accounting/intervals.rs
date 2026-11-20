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
                    if let Some(super::super::synchronization::local::Owned::Guard(interval)) =
                        owner.synchronization
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
    ) -> Result<(), VirErr> {
        if self
            .paths
            .iter()
            .any(|path| path.held.iter().any(|other| other.instance == interval.instance))
        {
            return Err(unsupported(span, "reentrant blocking acquisition of a held mutex"));
        }
        for path in self.paths.clone() {
            self.record_phase(
                span,
                Self::path_expression(&path, span),
                &path,
                Boundary::Wait(interval),
            );
        }
        for path in &mut self.paths {
            path.held.insert(interval);
        }
        self.record_live(span)
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
