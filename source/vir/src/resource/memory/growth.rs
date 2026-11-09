//! Erased, verifier-owned state for changing vector allocations.
//!
//! A reservation lower bound and a retained-byte upper bound are deliberately
//! distinct. Borrowed inputs need not expose their allocation size: the caller
//! keeps paying for that allocation while the callee pays for replacement buffers.

use super::contracts;
use crate::ast::*;
use crate::ast_util::*;
use crate::def::Spanned;
use crate::messages::Span;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone)]
pub(super) struct VectorState {
    /// Guaranteed reserved element slots, including occupied slots.
    pub(super) capacity: Expr,
    /// Initial reservation remains a lower bound because supported operations never shrink.
    pub(super) minimum: Expr,
    /// Constructor charge, or zero for an allocation supplied by the caller.
    pub(super) initial_bytes: Expr,
    /// Direct pushes require length-dependent loop bounds; helper effects have stable bounds.
    pub(super) pushes: usize,
    /// Upper bound for retained backing storage charged in this function.
    pub(super) bytes: Expr,
    /// Scratch snapshot prevents a transition from reading its own updated state.
    pub(super) next_capacity: Expr,
    /// Retained-byte snapshot committed after the executable operation.
    pub(super) next_bytes: Expr,
    /// Stable identity of this allocation's charge across moves and branches.
    pub(super) allocation: u64,
    /// Model size of one non-owning element.
    pub(super) element: u64,
    /// Original parameter, if this allocation came from the caller.
    pub(super) input: Option<usize>,
    /// Whether this body can replace the backing allocation.
    pub(super) changed: bool,
    /// Bounds from helpers that need not relate to the retained capacity minimum.
    pub(super) floor: Expr,
}

#[derive(Default)]
pub(super) struct Growth {
    /// All states have function-wide proof scope; executable ownership controls charges.
    pub(super) vectors: Vec<VectorState>,
    /// Function-entry declarations for erased proof state.
    pub(super) declarations: Vec<Stmt>,
    /// Initializers run before the reservation checks at their constructor.
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

pub(super) fn assign(span: &Span, variable: &Expr, value: Expr) -> Stmt {
    let ExprX::Var(name) = &variable.x else { unreachable!() };
    Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &unit_typ(),
            ExprX::Assign {
                place: SpannedTyped::new(span, &int_typ(), PlaceX::Local(name.clone())),
                rhs: value,
                op: None,
                typ: int_typ(),
                resolve: false,
            },
        )),
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
        bytes: Expr,
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
            let value = SpannedTyped::new(span, &int_typ(), ExprX::Var(name.clone()));
            let zero = contracts::literal(span, 0);
            self.declarations.push(Spanned::new(
                span.clone(),
                StmtX::Decl {
                    pattern: SpannedTyped::new(
                        span,
                        &int_typ(),
                        PatternX::Var(PatternBinding {
                            name,
                            by_ref: ByRef::No,
                            typ: int_typ(),
                            user_mut: Some(true),
                            copy: true,
                            move_exec_to_proof_okay: MoveExecToProofOkay::No,
                        }),
                    ),
                    mode: Some((Mode::Spec, DeclProph::Default)),
                    init: Some(SpannedTyped::new(span, &int_typ(), PlaceX::Temporary(zero))),
                    els: None,
                    assert_irrefutable: false,
                },
            ));
            value
        };
        let lower = variable("capacity");
        let upper = variable("bytes");
        let next_capacity = variable("next_capacity");
        let next_bytes = variable("next_bytes");
        self.before
            .entry(span.id)
            .or_default()
            .extend([assign(span, &lower, capacity.clone()), assign(span, &upper, bytes.clone())]);
        self.vectors.push(VectorState {
            capacity: lower,
            minimum: capacity,
            initial_bytes: bytes,
            pushes: 0,
            bytes: upper,
            next_capacity,
            next_bytes,
            allocation,
            element,
            input,
            changed: false,
            floor: contracts::literal(span, 0),
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
            result.push(mk_ineq(span, &zero, &state.bytes, InequalityOp::Le));
            let mut in_scope = true;
            let _: Result<(), VirErr> =
                crate::ast_visitor::expr_visitor_check(&state.floor, &mut |_, expr| {
                    if let ExprX::Var(name) = &expr.x {
                        in_scope &= allowed.contains(name);
                    }
                    Ok(())
                });
            // A helper may use a scalar declared inside this loop. Its expression
            // cannot escape into the header; the checked function budget is a
            // sound, in-scope bound for the live replacement instead.
            let floor = if in_scope { state.floor.clone() } else { fallback.clone() };
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
                contracts::maximum(span, state.initial_bytes.clone(), floor)
            } else {
                upper
            };
            result.push(mk_ineq(span, &state.bytes, &upper, InequalityOp::Le));
        }
        result
    }
}

impl super::analysis::Analysis<'_> {
    pub(super) fn retain_vector_growth(&mut self, span: &Span, id: usize, bound: Expr) {
        if contracts::constant(&bound) == Some(0) {
            return;
        }
        let state = &mut self.growth.vectors[id];
        // The old buffer is retained on the no-growth path, the replacement on
        // the growth path. Keep their maximum, never their sum after the call.
        let upper = contracts::maximum(span, state.bytes.clone(), bound.clone());
        self.growth.updates.entry(span.id).or_default().push(assign(
            span,
            &state.next_bytes,
            upper,
        ));
        self.growth.after.entry(span.id).or_default().push(assign(
            span,
            &state.bytes,
            state.next_bytes.clone(),
        ));
        state.floor = contracts::maximum(span, state.floor.clone(), bound);
        state.changed = true;
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
    if let (Some(input), Some(budget)) = (state.input, contracts::constant(bound)) {
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

impl super::analysis::Analysis<'_> {
    /// Infer a useful invariant for a common fill loop. The generated invariant
    /// is still proved at entry and at every back edge by Verus.
    pub(super) fn fill_loop_invariants(&mut self, cond: &Expr, body: &Expr) -> Vec<Expr> {
        let ExprX::Binary(BinaryOp::Inequality(InequalityOp::Lt), length, limit) = &cond.x else {
            return vec![];
        };
        let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &length.x else {
            return vec![];
        };
        if attrs.resource_intrinsic != Some(ResourceIntrinsic::VecLen) || args.len() != 1 {
            return vec![];
        }
        let Ok((name, _, _)) = self.vector_receiver(&args[0]) else { return vec![] };
        let Some(id) = self.vector_state(&name) else { return vec![] };
        let state = &self.growth.vectors[id];
        if state.input.is_none() || state.changed {
            return vec![];
        }
        let Ok(limit) = contracts::quantity(limit, &self.stable_scalars) else { return vec![] };
        let same = match (&limit.x, &state.minimum.x) {
            (ExprX::Var(a), ExprX::Var(b)) => a == b,
            (ExprX::Const(a), ExprX::Const(b)) => a == b,
            _ => false,
        };
        if !same {
            return vec![];
        }
        let mut pushes = 0;
        let mut simple = true;
        let _: Result<(), VirErr> = crate::ast_visitor::expr_visitor_check(body, &mut |_, expr| {
            match &expr.x {
                ExprX::Loop { .. } => simple = false,
                ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. } => {
                    match attrs.resource_intrinsic {
                        Some(ResourceIntrinsic::VecPush) => pushes += 1,
                        Some(ResourceIntrinsic::VecLen) => {}
                        _ => simple = false,
                    }
                }
                _ => {}
            }
            Ok(())
        });
        if !simple || pushes > 1 {
            return vec![];
        }
        vec![
            mk_eq(&cond.span, &state.bytes, &contracts::literal(&cond.span, 0)),
            mk_eq(&cond.span, &state.capacity, &state.minimum),
        ]
    }
}
