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
    /// Earlier operation whose exit observation the dependent allocation needs.
    pub(super) observation: Option<std::sync::Arc<Span>>,
}

impl Failure {
    pub(super) fn new(span: &Span, reason: &'static str) -> Self {
        Self { span: span.clone(), reason, observation: None }
    }

    pub(super) fn diagnostic(&self, function: &Span) -> VirErr {
        let diagnostic = super::super::model::unsupported(
            &self.span,
            &format!(
                "this runtime ownership transformation; no precise helper summary can be inferred: {}",
                self.reason
            ),
        )
        .secondary_label(function, "ownership summary required for this function");
        if let Some(site) = &self.observation {
            diagnostic
                .secondary_label(site, "the exact size relationship could not be inferred here")
        } else {
            diagnostic
        }
    }
}
