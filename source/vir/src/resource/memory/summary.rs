//! Facts derived together while checking a function, consumed together at calls.

use crate::ast::*;
use std::sync::Arc;

/// Ordered source effects retained alongside an ownership interface. The AST
/// supplies branches, loops and exits; the operation map supplies the semantics
/// accepted by accounting at those sites. Neither is a scalar peak summary.
pub(super) struct BodyEffects {
    pub(super) body: Expr,
    pub(super) ownership: super::transfer::Checked,
    /// Resolved ordinary helpers whose proofs the caller must discharge.
    pub(super) calls: Vec<(Fun, crate::messages::Span)>,
}

impl BodyEffects {
    /// Every consumed helper must retain its verified source effects. A function
    /// contract alone cannot discharge worker cleanup or panic-free dependencies.
    pub(super) fn validate(
        &self,
        summaries: &std::collections::HashMap<Fun, FunctionSummary>,
    ) -> Result<(), VirErr> {
        for (callee, span) in &self.calls {
            if summaries.get(callee).and_then(|summary| summary.effects.as_ref()).is_none() {
                return Err(super::model::unsupported(
                    span,
                    "worker helper without checked body effects",
                ));
            }
        }
        // Accounting chose the semantics; validate that every effect still has
        // its original source site in this ordered body before exporting it.
        use super::transfer::checked::Kind;
        let mut sites = std::collections::HashSet::new();
        crate::ast_visitor::map_expr_visitor_env(
            &self.body,
            &mut air::scope_map::ScopeMap::new(),
            &mut sites,
            &|sites, _, value| {
                sites.insert(value.span.id);
                Ok(value.clone())
            },
            &|sites, _, statement| {
                sites.insert(statement.span.id);
                Ok(vec![statement.clone()])
            },
            &|_, typ| Ok(typ.clone()),
            &|sites, _, place| {
                sites.insert(place.span.id);
                Ok(place.clone())
            },
            &|sites, _, pattern| {
                sites.insert(pattern.span.id);
                Ok(pattern.clone())
            },
        )?;
        let kinds = [
            Kind::Operation,
            Kind::Branch,
            Kind::Move,
            Kind::Assign,
            Kind::Pattern,
            Kind::Scope,
            Kind::Loop,
            Kind::Exit,
        ];
        let coverage = sites.into_iter().flat_map(|id| kinds.map(|kind| (kind, id))).collect();
        if !self.ownership.covered(&coverage) {
            return Err(super::model::unsupported(
                &self.body.span,
                "worker effects detached from their executable source sites",
            ));
        }
        Ok(())
    }
}

/// Call-composition facts established together by a checked function body.
#[derive(Clone)]
pub(super) struct FunctionSummary {
    /// The checked body remains available to asynchronous and later synchronized
    /// composition; existing synchronous calls still use the interfaces below.
    pub(super) effects: Option<Arc<BodyEffects>>,
    /// Borrowed owner roots changed by checked operations, including logical
    /// length changes that retain the same allocation and reservation.
    pub(super) modified_parameters: std::collections::BTreeSet<usize>,
    /// Physical-ownership transformation, required for runtime ownership interfaces.
    pub(super) transfer: Option<super::transfer::Template>,
    /// Owning runtime operations require this interface even behind leaf returns.
    pub(super) transfer_required: bool,
    /// Container-independent ownership, byte sizes, and retained replacements.
    pub(super) allocations: super::allocations::AllocationSummary,
    /// Vector-specific reservation requirements and result capacity facts.
    pub(super) vectors: super::vector_calls::VectorSummary,
    /// Allocation provenance IDs map to disjoint nodes of owned parameter trees.
    pub(super) input_paths: Vec<super::paths::InputPath>,
    /// Zero-based input index when the result forwards that value's charge.
    pub(super) return_parameter: Option<usize>,
    /// Simultaneous costs and input/result lifetimes needed to compose a call.
    pub(super) profiles: Vec<super::lifetime::Profile>,
}

impl FunctionSummary {
    /// The returned vector carries this parameter's outstanding handles.
    pub(super) fn worker_parameter(&self) -> Option<usize> {
        self.effects.as_ref()?.ownership.worker_parameter.map(|(index, _)| index)
    }
}
