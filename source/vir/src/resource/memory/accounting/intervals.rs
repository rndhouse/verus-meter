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
