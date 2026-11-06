//! Checked live/peak accounting and source-located diagnostics.

use super::model::{MODEL_NAME, unsupported};
use crate::ast::{Expr, VirErr, VirErrAs};
use crate::messages::{Span, error, note};
use std::collections::HashMap;

pub struct StorageEvent {
    pub span: Span,
    pub description: String,
    pub live: u64,
}

pub struct StorageReport {
    pub peak: u64,
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
    pub(super) bytes: u64,
    pub(super) span: Span,
    pub(super) costs: Vec<(Span, Expr)>,
}

impl Peak {
    pub(super) fn merge(&mut self, other: &Self) {
        if other.bytes > self.bytes {
            self.bytes = other.bytes;
            self.span = other.span.clone();
        }
        self.costs.extend(other.costs.iter().cloned());
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
        if self.live > self.report.peak {
            self.report.peak = self.live;
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

    // Keep an envelope for traces/checkpoints, but prove the instantiated cost
    // instead of treating that envelope as a required allocation.
    pub(super) fn reserve_call(
        &mut self,
        span: &Span,
        additional: u64,
        cost: Expr,
    ) -> Result<(), VirErr> {
        self.reserve(span, additional, "callee budget envelope")?;
        if additional != 0 {
            if self.dynamic.is_empty() {
                self.report.reservations.pop();
            } else {
                self.report.call_costs.pop();
            }
        }
        self.report.call_costs.push((span.clone(), cost));
        self.report.conditional = true;
        Ok(())
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
