//! Checked live/peak accounting and source-located diagnostics.

use super::model::{MODEL_NAME, unsupported};
use crate::ast::{VirErr, VirErrAs};
use crate::messages::{Span, error, note};

pub struct StorageEvent {
    pub span: Span,
    pub description: String,
    pub live: u64,
}

pub struct StorageReport {
    pub peak: u64,
    pub budget: u64,
    pub events: Vec<StorageEvent>,
}

impl StorageReport {
    pub fn diagnostics(&self, span: &Span) -> Vec<VirErrAs> {
        let mut result = vec![VirErrAs::Note(note(
            span,
            format!(
                "resource model {MODEL_NAME}: peak {} bytes, budget {} bytes",
                self.peak, self.budget,
            ),
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

pub(super) struct Accounting {
    live: u64,
    peak_span: Span,
    report: StorageReport,
}

impl Accounting {
    pub(super) fn new(span: &Span, budget: u64) -> Self {
        Self {
            live: 0,
            peak_span: span.clone(),
            report: StorageReport { peak: 0, budget, events: Vec::new() },
        }
    }

    pub(super) fn live(&self) -> u64 {
        self.live
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
        self.event(span, format!("reserve {bytes} bytes for {reason}"));
        Ok(())
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

    pub(super) fn finish(mut self, function_span: &Span) -> Result<StorageReport, VirErr> {
        self.release(function_span, self.live, "function exit");
        if self.report.peak > self.report.budget {
            return Err(error(&self.peak_span, format!(
                "local storage budget exceeded: peak {} bytes exceeds budget {} bytes ({MODEL_NAME})",
                self.report.peak, self.report.budget,
            )).secondary_span(function_span));
        }
        Ok(self.report)
    }
}
