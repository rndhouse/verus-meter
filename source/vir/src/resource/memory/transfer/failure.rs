//! Inference failures are explanations, not proof failures or byte estimates.
//!
//! Optional summaries may discard these explanations. Required summaries report
//! the failed boundary without publishing a partial ownership transformation.

use crate::ast::VirErr;
use crate::messages::Span;

#[derive(Clone)]
pub(super) struct Failure {
    /// Executable source site, or the function boundary for export checks.
    pub(super) span: Span,
    /// The inference boundary that could not produce an exact description.
    pub(super) reason: &'static str,
}

impl Failure {
    pub(super) fn new(span: &Span, reason: &'static str) -> Self {
        Self { span: span.clone(), reason }
    }

    pub(super) fn diagnostic(&self, function: &Span) -> VirErr {
        super::super::model::unsupported(
            &self.span,
            &format!(
                "this runtime ownership transformation; no precise helper summary can be inferred: {}",
                self.reason
            ),
        )
        .secondary_label(function, "ownership summary required for this function")
    }
}
