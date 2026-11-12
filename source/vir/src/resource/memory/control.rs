//! Lexical control-flow edges carry the same ownership state as fallthrough.
//!
//! Capture an edge after evaluating its result, then unwind each scope exactly
//! once while propagating it to its target. Historical cost points remain in
//! accounting; unreachable fallthrough never receives an edge's live storage.

use super::{
    analysis::Analysis,
    heap::Owner,
    lifetime::{BranchState, Value},
    model::unsupported,
};
use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
use crate::{ast::*, messages::Span};

/// Exit expressions are admitted at structural sequence/branch boundaries.
/// Operand-level short circuiting needs a different evaluation interface; reject
/// it before partially accounting for a constructor, operator, or call.
pub(super) fn validate(
    body: &Expr,
    modes: &std::collections::HashMap<VarIdent, Mode>,
) -> Result<(), VirErr> {
    struct Context<'a> {
        structural: bool,
        modes: &'a std::collections::HashMap<VarIdent, Mode>,
    }
    impl Context<'_> {
        fn expr(&mut self, value: &Expr, structural: bool) -> Result<(), VirErr> {
            let old = std::mem::replace(&mut self.structural, structural);
            let result = self.visit_expr(value);
            self.structural = old;
            result
        }
    }
    impl AstVisitor<Walk, VirErr, NoScoper> for Context<'_> {
        fn visit_place(&mut self, place: &Place) -> Result<(), VirErr> {
            self.visit_place_rec(place)
        }
        fn visit_pattern(&mut self, _: &Pattern) -> Result<(), VirErr> {
            Ok(())
        }
        fn visit_stmt(&mut self, statement: &Stmt) -> Result<(), VirErr> {
            if super::execution::ignored_statement(statement, self.modes) {
                Ok(())
            } else {
                self.visit_stmt_rec(statement)
            }
        }
        fn visit_expr(&mut self, value: &Expr) -> Result<(), VirErr> {
            if super::execution::ignored_expression(value) {
                return Ok(());
            }
            let structural = self.structural;
            match &value.x {
                ExprX::Return(result) | ExprX::BreakOrContinue { value: result, .. } => {
                    if !structural {
                        return Err(unsupported(
                            &value.span,
                            "control-flow exits inside operands or call arguments",
                        ));
                    }
                    if let Some(result) = result {
                        self.expr(result, true)?;
                    }
                    Ok(())
                }
                ExprX::If(condition, yes, no) => {
                    self.expr(condition, false)?;
                    self.expr(yes, structural)?;
                    if let Some(no) = no {
                        self.expr(no, structural)?;
                    }
                    Ok(())
                }
                ExprX::Loop { cond, body, .. } => {
                    if let Some(cond) = cond {
                        self.expr(cond, false)?;
                    }
                    self.expr(body, structural)
                }
                ExprX::Match(source, arms, _) => {
                    self.structural = false;
                    self.visit_place(source)?;
                    for arm in arms.iter() {
                        self.expr(&arm.x.guard, false)?;
                        self.expr(&arm.x.body, structural)?;
                    }
                    self.structural = structural;
                    Ok(())
                }
                ExprX::Block(..) | ExprX::NeverToAny(_) => self.visit_expr_rec(value),
                ExprX::ReadPlace(place, _) if matches!(place.x, PlaceX::Temporary(_)) => {
                    self.visit_expr_rec(value)
                }
                _ => {
                    self.structural = false;
                    let result = self.visit_expr_rec(value);
                    self.structural = structural;
                    result
                }
            }
        }
        fn visit_typ(&mut self, _: &Typ) -> Result<(), VirErr> {
            Ok(())
        }
    }
    Context { structural: true, modes }.visit_expr(body)
}

/// An exit target is a compiler-resolved label, never a source label spelling.
#[derive(Clone, PartialEq, Eq)]
pub(super) enum Target {
    /// Complete the current function after evaluating the return value.
    Return,
    /// Leave the labelled loop, optionally producing its value.
    Break(Label),
    /// Revisit the labelled loop head after releasing intervening locals.
    Continue(Label),
}

/// A pending exit with its result detached from the locals being unwound.
pub(super) struct Edge {
    /// Destination that will consume this edge after lexical cleanup.
    pub(super) target: Target,
    /// Source exit used for cleanup and unsupported-dependency diagnostics.
    pub(super) span: Span,
    /// Live values, allocations, and peak history on this edge alone.
    pub(super) state: BranchState,
    /// Inline result remains live while enclosing scopes release their locals.
    pub(super) value: Value,
    /// Separately allocated result storage, if the exit produces an owner.
    pub(super) owner: Option<Owner>,
}

/// Fallthrough reachability and edges not yet consumed by their target.
pub(super) struct Flow {
    /// Whether the next source operation can execute on the current path.
    pub(super) reachable: bool,
    /// Edges unwind through scopes before a loop or function consumes them.
    pub(super) exits: Vec<Edge>,
}

impl Default for Flow {
    fn default() -> Self {
        Self { reachable: true, exits: Vec::new() }
    }
}

impl Analysis<'_> {
    pub(super) fn exit(
        &mut self,
        expr: &Expr,
        target: Target,
        result: Option<&Expr>,
    ) -> Result<(), VirErr> {
        // Moving an enclosing owner is safe on a terminating edge: this path
        // cannot reach the branch join or loop back edge that protects it.
        let protection =
            result.filter(|value| direct_result(value)).map(|_| self.heap.exit_protection());
        let value = if let Some(result) = result { self.produce(result)? } else { Value::unit() };
        if !self.flow.reachable {
            if let Some(protection) = protection {
                self.heap.unprotect(protection);
            }
            return Ok(());
        }
        let owner = self.result_owner.take();
        if let Some(protection) = protection {
            self.heap.unprotect(protection);
        }
        self.transitions.exits.insert(expr.span.id, target.clone());
        self.flow.exits.push(Edge {
            target,
            span: expr.span.clone(),
            state: self.branch_state(),
            value,
            owner,
        });
        self.flow.reachable = false;
        Ok(())
    }

    /// A scope cleans only edges created inside it. Outer pending edges already
    /// passed through their own scopes and must not be dropped a second time.
    pub(super) fn cleanup_scope(&mut self, locals: &[(Span, VarIdent)], first_exit: usize) {
        fn cleanup(analysis: &mut Analysis<'_>, locals: &[(Span, VarIdent)]) {
            for (span, name) in locals.iter().rev() {
                // Lexical destruction is mandated by the exit; transfer guards
                // restrict source operations, not cleanup of an ending scope.
                if let Some(owner) = analysis.heap.owners.remove(name) {
                    analysis.release_owner(owner, span);
                }
                if let Some(value) = analysis.slots.remove(name) {
                    analysis.release_value(value, span);
                }
            }
        }
        cleanup(self, locals);
        let normal = self.branch_state();
        let produced = self.produced.take();
        let owner = self.result_owner.take();
        let mut edges = self.flow.exits.split_off(first_exit);
        for edge in &mut edges {
            self.restore_branch(&edge.state);
            cleanup(self, locals);
            edge.state = self.branch_state();
        }
        self.flow.exits.extend(edges);
        self.restore_branch(&normal);
        self.produced = produced;
        self.result_owner = owner;
    }

    /// Join only compatible structural roles. Byte envelopes cannot stand in
    /// for different allocation identities or unknown returned ownership.
    pub(super) fn join_exit(&mut self, span: &Span, state: &BranchState) -> Result<(), VirErr> {
        if !compatible_heap(&self.heap, &state.heap) {
            return Err(unsupported(
                span,
                "path-dependent ownership roles or input regions on control-flow exits",
            ));
        }
        self.join_branch(state)
    }

    pub(super) fn finish_returns(&mut self, span: &Span, normal: Value) -> Result<Value, VirErr> {
        let mut result = self.flow.reachable.then_some(normal);
        let mut owner = self.result_owner.take();
        let edges = std::mem::take(&mut self.flow.exits);
        for edge in edges {
            if edge.target != Target::Return {
                return Err(unsupported(&edge.span, "an unresolved control-flow exit"));
            }
            if let Some(result) = &mut result {
                self.join_exit(span, &edge.state)?;
                result.merge(&edge.value);
                owner = merge_result(span, owner, edge.owner)?;
            } else {
                self.restore_branch(&edge.state);
                result = Some(edge.value);
                owner = edge.owner;
            }
        }
        self.result_owner = owner;
        Ok(result.unwrap_or_else(Value::unit))
    }
}

/// A direct move detaches an existing value without releasing its storage in
/// the current accounting region. General result evaluation keeps the normal
/// protection rules, especially for owners paid by an enclosing memory section.
fn direct_result(value: &Expr) -> bool {
    fn place(value: &Place) -> bool {
        match &value.x {
            PlaceX::Local(_) => true,
            PlaceX::Field(_, base) | PlaceX::DerefMut(base) => place(base),
            PlaceX::Temporary(value) => direct_result(value),
            _ => false,
        }
    }
    match &value.x {
        ExprX::Var(_) => true,
        ExprX::ReadPlace(value, _) => place(value),
        ExprX::Block(statements, Some(tail)) if statements.is_empty() => direct_result(tail),
        _ => false,
    }
}

/// Continuing roles may share mutable proof state, but fixed allocation and
/// provenance identities cannot change implicitly at a loop exit.
pub(super) fn compatible_heap(a: &super::heap::Heap, b: &super::heap::Heap) -> bool {
    [(&a.owners, &b.owners), (&a.borrowed, &b.borrowed)].iter().all(|(left, right)| {
        left.len() == right.len()
            && left.iter().all(|(name, a)| right.get(name).is_some_and(|b| compatible(a, b)))
    })
}

/// Fixed result storage can agree across distinct exit sites. Dynamic vectors
/// must retain the same proof-state identities; other choices need a richer
/// checked exit interface and are explicitly unsupported for now.
pub(super) fn merge_result(
    span: &Span,
    left: Option<Owner>,
    right: Option<Owner>,
) -> Result<Option<Owner>, VirErr> {
    match (left, right) {
        (None, None) => Ok(None),
        (Some(mut left), Some(right)) => {
            if compatible(&left, &right) {
                fn minima(span: &Span, left: &mut Owner, right: &Owner) {
                    if let (Some(left), Some(right)) = (&mut left.elements, &right.elements) {
                        super::metadata::reservations::join_minima(
                            span,
                            &mut left.minima,
                            &right.minima,
                        );
                        left.precise &= right.precise;
                    }
                    for (slot, child) in &mut left.children {
                        minima(span, child, &right.children[slot]);
                    }
                }
                minima(span, &mut left, &right);
                Ok(Some(left))
            } else {
                Err(unsupported(
                    span,
                    "path-dependent returned allocation identities on control-flow exits",
                ))
            }
        }
        _ => Err(unsupported(span, "inconsistent owning results on control-flow exits")),
    }
}

/// Shared proof-state identities can vary in value along an edge. Frozen
/// descriptors and reservations must actually agree before they can be reused.
fn compatible(a: &Owner, b: &Owner) -> bool {
    fn expression(a: &Option<Expr>, b: &Option<Expr>) -> bool {
        match (a, b) {
            (None, None) => true,
            (Some(a), Some(b)) => super::transfer::simplify::same_expression(a, b),
            _ => false,
        }
    }
    a.bytes == b.bytes
        && a.kind == b.kind
        && a.dynamic == b.dynamic
        && a.vector == b.vector
        && a.input == b.input
        && a.view == b.view
        && a.geometry_known == b.geometry_known
        && expression(&a.geometry, &b.geometry)
        && expression(&a.extent, &b.extent)
        && expression(&a.capacity, &b.capacity)
        && match (&a.elements, &b.elements) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                a.view == b.view
                    && a.states == b.states
                    && a.inputs == b.inputs
                    && super::transfer::simplify::same_expression(&a.records, &b.records)
            }
            _ => false,
        }
        && a.children.len() == b.children.len()
        && a.children.iter().all(|(slot, a)| b.children.get(slot).is_some_and(|b| compatible(a, b)))
}
