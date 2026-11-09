//! Erased, verifier-owned allocation state and operation scheduling.
//!
//! A reservation lower bound and a retained-byte upper bound are deliberately
//! distinct. Borrowed inputs need not expose their allocation size: the caller
//! keeps paying for that allocation while the callee pays for replacement buffers.

use super::contracts;
use super::symbolic::assign;
use crate::ast::*;
use crate::ast_util::*;
use crate::messages::Span;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone)]
pub(super) struct VectorState {
    /// Guaranteed reserved element slots, including occupied slots.
    pub(super) capacity: Expr,
    /// Initial reservation remains a lower bound because supported operations never shrink.
    pub(super) minimum: Expr,
    /// Direct pushes require length-dependent loop bounds; helper effects have stable bounds.
    pub(super) pushes: usize,
    /// Scratch snapshot prevents a transition from reading its own updated state.
    pub(super) next_capacity: Expr,
    /// Model size of one non-owning element.
    pub(super) element: u64,
    /// An inferred entry reservation whose no-growth uses are checked by Verus.
    pub(super) reserved: bool,
    /// Container-independent byte state and allocation identity.
    pub(super) backing: super::allocations::RetainedAllocation,
}

#[derive(Default)]
pub(super) struct Growth {
    /// All states have function-wide proof scope; executable ownership controls charges.
    pub(super) vectors: Vec<VectorState>,
    /// Function-entry declarations for erased proof state.
    pub(super) declarations: Vec<Stmt>,
    /// Capture allocation facts before checks and before consuming their sources.
    pub(super) before: HashMap<u64, Vec<Stmt>>,
    /// Snapshot the next state after checks, before executing the operation.
    pub(super) updates: HashMap<u64, Vec<Stmt>>,
    /// Commit snapshots after the operation and its argument evaluation.
    pub(super) after: HashMap<u64, Vec<Stmt>>,
    /// Inductive resource invariants generated for each loop.
    pub(super) loops: HashMap<u64, Vec<Expr>>,
    /// Enclosing allocations excluded from a section's local accounting.
    pub(super) section_protected: std::collections::HashSet<usize>,
}

pub(super) fn select(span: &Span, condition: Expr, yes: Expr, no: Expr) -> Expr {
    SpannedTyped::new(span, &int_typ(), ExprX::If(condition, yes, Some(no)))
}

/// Explicit source-model growth policy. Allocator rounding and metadata are
/// excluded, as for with_capacity. Count both buffers during replacement.
pub(super) fn grown_capacity(span: &Span, length: Expr, element: u64) -> Expr {
    let minimum = if element == 1 {
        8
    } else if element <= 1024 {
        4
    } else {
        1
    };
    contracts::maximum(
        span,
        contracts::literal(span, minimum),
        contracts::maximum(
            span,
            contracts::multiply(span, contracts::literal(span, 2), length.clone()),
            contracts::add(span, length, contracts::literal(span, 1)),
        ),
    )
}

impl Growth {
    pub(super) fn revision(&self) -> usize {
        self.before.values().map(Vec::len).sum::<usize>()
            + self.updates.values().map(Vec::len).sum::<usize>()
    }

    pub(super) fn new_vector(
        &mut self,
        span: &Span,
        capacity: Expr,
        size: super::footprint::Charge<Expr>,
        element: u64,
        input: Option<usize>,
        allocation: u64,
    ) -> usize {
        let id = self.vectors.len();
        let mut variable = |suffix: &str| {
            let name = VarIdent(
                Arc::new(format!("$memory_{suffix}")),
                VarIdentDisambiguate::VirTemp(id as u64),
            );
            let (value, declaration) = super::symbolic::integer_local(span, name);
            self.declarations.push(declaration);
            value
        };
        let lower = variable("capacity");
        let upper = variable("bytes");
        let next_capacity = variable("next_capacity");
        let next_bytes = variable("next_bytes");
        self.before.entry(span.id).or_default().extend([
            assign(span, &lower, capacity.clone()),
            assign(span, &upper, size.amount.clone()),
        ]);
        self.vectors.push(VectorState {
            capacity: lower,
            minimum: capacity,
            pushes: 0,
            next_capacity,
            element,
            reserved: false,
            backing: super::allocations::RetainedAllocation {
                id: allocation,
                kind: size.kind,
                initial_bytes: size.amount,
                bytes: upper,
                next_bytes,
                input,
                changed: false,
                floor: contracts::literal(span, 0),
            },
        });
        id
    }

    /// These are ordinary checked loop invariants, never assumed summaries.
    pub(super) fn invariants(
        &self,
        span: &Span,
        ids: &[usize],
        allowed: &std::collections::HashSet<VarIdent>,
        fallback: &Expr,
    ) -> Vec<Expr> {
        let mut result = Vec::new();
        for id in ids {
            let state = &self.vectors[*id];
            let zero = contracts::literal(span, 0);
            result.push(mk_ineq(span, &state.minimum, &state.capacity, InequalityOp::Le));
            result.push(mk_ineq(span, &zero, &state.capacity, InequalityOp::Le));
            result.push(mk_ineq(span, &zero, &state.backing.bytes, InequalityOp::Le));
            let mut in_scope = true;
            let _: Result<(), VirErr> =
                crate::ast_visitor::expr_visitor_check(&state.backing.floor, &mut |_, expr| {
                    if let ExprX::Var(name) = &expr.x {
                        in_scope &= allowed.contains(name);
                    }
                    Ok(())
                });
            // A helper may use a scalar declared inside this loop. Its expression
            // cannot escape into the header; the checked function budget is a
            // sound, in-scope bound for the live replacement instead.
            let floor = if in_scope { state.backing.floor.clone() } else { fallback.clone() };
            let upper = contracts::maximum(
                span,
                floor.clone(),
                contracts::multiply(
                    span,
                    contracts::literal(span, state.element),
                    grown_capacity(span, state.capacity.clone(), state.element),
                ),
            );
            let upper = if state.pushes == 0 {
                contracts::maximum(span, state.backing.initial_bytes.clone(), floor)
            } else {
                upper
            };
            result.push(mk_ineq(span, &state.backing.bytes, &upper, InequalityOp::Le));
        }
        result
    }
}

impl super::analysis::Analysis<'_> {
    pub(super) fn retain_vector_growth(
        &mut self,
        span: &Span,
        id: usize,
        replacement: super::footprint::Charge<Expr>,
    ) -> Result<(), VirErr> {
        if let Some((snapshot, commit)) =
            self.growth.vectors[id].backing.retain(span, &replacement)?
        {
            self.growth.updates.entry(span.id).or_default().push(snapshot);
            self.growth.after.entry(span.id).or_default().push(commit);
        }
        Ok(())
    }
}

/// Register only the proof locals introduced after execution mode checking.
/// Rust source identifiers cannot contain `$`, and the internal disambiguator
/// distinguishes these bindings from all user locals.
pub(crate) fn resolution_modes(
    body: &Expr,
    variables: &mut HashMap<VarIdent, Mode>,
    temporaries: &mut HashMap<u64, Mode>,
) {
    let ExprX::Block(statements, _) = &body.x else { return };
    for statement in statements.iter() {
        if let StmtX::Decl { pattern, init, mode: Some((Mode::Spec, _)), .. } = &statement.x {
            if let PatternX::Var(binding) = &pattern.x {
                if matches!(binding.name.1, VarIdentDisambiguate::VirTemp(_))
                    && binding.name.0.starts_with("$memory_")
                {
                    variables.insert(binding.name.clone(), Mode::Spec);
                    if let Some(init) = init {
                        temporaries.insert(init.span.id, Mode::Spec);
                    }
                }
            }
        }
    }
}

/// Every replacement is created while its receiver handle is live. If even the
/// smallest replacement cannot fit, a successful body proof establishes that
/// no replacement occurred. This preserves precise summaries for small helpers.
pub(super) fn retained_bound(state: &VectorState, function: &Function, bound: &Expr) -> Expr {
    if state.element == 0 {
        return contracts::literal(&function.span, 0);
    }
    if let (Some(input), Some(budget)) = (state.backing.input, contracts::constant(bound)) {
        let minimum = contracts::constant(&grown_capacity(
            &function.span,
            contracts::literal(&function.span, 0),
            state.element,
        ))
        .unwrap();
        let handle =
            if matches!(&*function.x.params[input].x.typ, TypX::Datatype(..)) { 24 } else { 8 };
        if u128::from(budget) < u128::from(minimum) * u128::from(state.element) + handle {
            return contracts::literal(&function.span, 0);
        }
    }
    bound.clone()
}
