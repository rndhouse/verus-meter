//! Checked live/peak accounting and source-located diagnostics.

use super::model::{MODEL_NAME, unsupported};
use crate::ast::{Expr, VirErr, VirErrAs};
use crate::messages::{Span, error, note};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub struct StorageEvent {
    pub span: Span,
    pub description: String,
    pub live: u64,
}

pub struct StorageReport {
    // A conservative call envelope can exceed u64 even when its selected cost
    // fits. Actual reservations and declared budgets still use the u64 model.
    pub peak: u128,
    pub budget: u64,
    pub events: Vec<StorageEvent>,
    pub(super) reservations: Vec<(Span, u64)>,
    pub(super) conditional: bool,
    pub(super) call_costs: Vec<(Span, Expr)>,
}

impl StorageReport {
    pub fn diagnostics(&self, span: &Span) -> Vec<VirErrAs> {
        let mut result = vec![VirErrAs::Note(note(
            span,
            if self.conditional {
                format!(
                    "resource model {MODEL_NAME}: fixed-cost peak {} bytes, budget envelope {} bytes; symbolic storage obligations require Verus proofs",
                    self.peak, self.budget
                )
            } else {
                format!(
                    "resource model {MODEL_NAME}: peak {} bytes, budget {} bytes",
                    self.peak, self.budget
                )
            },
        ))];
        result.extend(self.events.iter().map(|event| {
            VirErrAs::Note(note(
                &event.span,
                format!("storage: {}; live {} bytes", event.description, event.live),
            ))
        }));
        result
    }
}

/// A path's high-water mark, including the source that established it.
#[derive(Clone)]
pub(super) struct Peak {
    pub(super) bytes: u128,
    pub(super) span: Span,
    pub(super) costs: Vec<(Span, Expr)>,
}

impl Peak {
    pub(super) fn merge(&mut self, other: &Self) {
        if other.bytes > self.bytes {
            self.bytes = other.bytes;
            self.span = other.span.clone();
        }
        // Cloned peaks share the same obligation expressions. Keep their common
        // history once when joining branches or adding a loop's iteration peak
        // to a checkpoint. A span can have multiple distinct charges, so span
        // identity alone is not enough to identify a shared obligation.
        let mut seen: HashSet<_> =
            self.costs.iter().map(|(span, cost)| (span.id, Arc::as_ptr(cost))).collect();
        self.costs.extend(
            other
                .costs
                .iter()
                .filter(|(span, cost)| seen.insert((span.id, Arc::as_ptr(cost))))
                .cloned(),
        );
    }
}

pub(super) struct Accounting {
    live: u64,
    dynamic: HashMap<u64, Expr>,
    peak_costs: Vec<(Span, Expr)>,
    peak_span: Span,
    report: StorageReport,
}

impl Accounting {
    pub(super) fn new(span: &Span, budget: u64) -> Self {
        Self {
            live: 0,
            dynamic: HashMap::new(),
            peak_costs: Vec::new(),
            peak_span: span.clone(),
            report: StorageReport {
                peak: 0,
                budget,
                events: Vec::new(),
                reservations: Vec::new(),
                conditional: false,
                call_costs: Vec::new(),
            },
        }
    }

    pub(super) fn live(&self) -> u64 {
        self.live
    }

    pub(super) fn peak(&self) -> Peak {
        Peak {
            bytes: self.report.peak,
            span: self.peak_span.clone(),
            costs: self.peak_costs.clone(),
        }
    }

    pub(super) fn set_peak(&mut self, peak: Peak) {
        self.peak_costs = peak.costs;
        self.report.peak = peak.bytes;
        self.peak_span = peak.span;
    }

    pub(super) fn reserve(&mut self, span: &Span, bytes: u64, reason: &str) -> Result<(), VirErr> {
        if bytes == 0 {
            return Ok(());
        }
        self.live = self
            .live
            .checked_add(bytes)
            .ok_or_else(|| unsupported(span, "storage totals exceeding u64"))?;
        if u128::from(self.live) > self.report.peak {
            self.report.peak = u128::from(self.live);
            self.peak_span = span.clone();
        }
        if self.dynamic.is_empty() {
            self.report.reservations.push((span.clone(), self.live));
        } else {
            self.symbolic_cost(span, self.live_expression(span));
        }
        self.event(span, format!("reserve {bytes} bytes for {reason}"));
        Ok(())
    }

    // The call is an instantaneous cost: its maximum belongs to the peak, not
    // live storage. Keep that envelope for traces/checkpoints, including values
    // above u64, while only the instantiated cost must fit the enclosing budget.
    pub(super) fn record_call(&mut self, span: &Span, additional: u64, cost: Expr) {
        let envelope = u128::from(self.live) + u128::from(additional);
        if envelope > self.report.peak {
            self.report.peak = envelope;
            self.peak_span = span.clone();
        }
        if additional != 0 && !self.dynamic.is_empty() {
            let envelope_cost = super::contracts::add(
                span,
                self.live_expression(span),
                super::contracts::literal(span, additional),
            );
            self.peak_costs.push((span.clone(), envelope_cost));
        }
        self.report.call_costs.push((span.clone(), cost));
        self.report.conditional = true;
        self.event(span, format!("callee budget envelope: fixed peak {envelope} bytes"));
    }

    pub(super) fn live_expression(&self, span: &Span) -> Expr {
        self.dynamic.values().cloned().fold(super::contracts::literal(span, self.live), |a, b| {
            super::contracts::add(span, a, b)
        })
    }

    pub(super) fn reserve_dynamic(&mut self, span: &Span, cost: Expr) {
        self.dynamic.insert(span.id, cost);
        self.symbolic_cost(span, self.live_expression(span));
    }

    pub(super) fn release_dynamic(&mut self, id: u64) {
        assert!(self.dynamic.remove(&id).is_some(), "balanced dynamic ownership");
    }

    pub(super) fn symbolic_cost(&mut self, span: &Span, cost: Expr) {
        self.report.call_costs.push((span.clone(), cost.clone()));
        self.peak_costs.push((span.clone(), cost));
        self.report.conditional = true;
    }

    pub(super) fn release(&mut self, span: &Span, bytes: u64, reason: &str) {
        if bytes == 0 {
            return;
        }
        self.live = self.live.checked_sub(bytes).expect("balanced resource events");
        self.event(span, format!("release {bytes} bytes for {reason}"));
    }

    pub(super) fn event(&mut self, span: &Span, description: String) {
        self.report.events.push(StorageEvent { span: span.clone(), description, live: self.live });
    }

    pub(super) fn finish(self, function_span: &Span) -> Result<StorageReport, VirErr> {
        self.finish_scope(function_span, "function exit", "local storage budget exceeded")
    }

    pub(super) fn finish_conditional(mut self, span: &Span) -> StorageReport {
        self.release(span, self.live, "function exit");
        self.report.conditional = true;
        self.report
    }

    pub(super) fn finish_section(self, section_span: &Span) -> Result<StorageReport, VirErr> {
        self.finish_scope(section_span, "section exit", "section storage budget exceeded")
    }

    fn finish_scope(
        mut self,
        scope_span: &Span,
        exit: &str,
        diagnostic: &str,
    ) -> Result<StorageReport, VirErr> {
        self.release(scope_span, self.live, exit);
        let (peak_span, required_peak) = self
            .report
            .reservations
            .iter()
            .max_by_key(|(_, n)| n)
            .map(|(span, n)| (span, *n))
            .unwrap_or((scope_span, 0));
        if required_peak > self.report.budget {
            return Err(error(
                peak_span,
                format!(
                    "{diagnostic}: peak {} bytes exceeds budget {} bytes ({MODEL_NAME})",
                    required_peak, self.report.budget,
                ),
            )
            .secondary_span(scope_span));
        }
        Ok(self.report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> Span {
        Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "peak merge test".into(),
        }
    }

    #[test]
    fn repeated_branch_joins_keep_shared_cost_once() {
        let span = span();
        let mut storage = Accounting::new(&span, 100);
        storage.symbolic_cost(&span, super::super::contracts::literal(&span, 8));
        let mut peak = storage.peak();
        for _ in 0..64 {
            let sibling = peak.clone();
            peak.merge(&sibling);
            assert_eq!(peak.costs.len(), 1);
        }
    }

    #[test]
    fn overlapping_peaks_preserve_distinct_charges_at_the_same_span() {
        let span = span();
        let cost = |n| (span.clone(), super::super::contracts::literal(&span, n));
        let shared = cost(8);
        let left = cost(16);
        let right = cost(32);
        let mut peak =
            Peak { bytes: 16, span: span.clone(), costs: vec![shared.clone(), left.clone()] };
        let other =
            Peak { bytes: 32, span: span.clone(), costs: vec![shared.clone(), right.clone()] };
        peak.merge(&other);
        peak.merge(&other);
        assert_eq!(peak.bytes, 32);
        assert_eq!(peak.costs.len(), 3);
        for (actual, expected) in peak.costs.iter().zip([shared, left, right]) {
            assert_eq!(actual.0.id, expected.0.id);
            assert!(Arc::ptr_eq(&actual.1, &expected.1));
        }
    }
}
