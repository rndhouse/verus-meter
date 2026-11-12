//! Connect Verus's existing for-loop lowering to the shared checked loop model.
//!
//! The executable wrapper, next call, exhaustion match, and proofs remain in
//! place. Ownership repetition evaluates only a successful visit of that same
//! checked dispatch; its exhaustion edge closes the finite count separately.

use super::{iterators, model::unsupported};
use crate::ast_visitor::{AstVisitor, NoScoper, Rewrite};
use crate::{ast::*, messages::Span};
use std::collections::HashMap;
use std::sync::Arc;

/// The compiler-resolved dispatch and proof observations of one lowered for.
#[derive(Clone)]
pub(super) struct ForLoop {
    /// Native wrapper binding, moved by the macro's irrefutable match.
    pub(super) receiver: VarIdent,
    /// Actual wrapper index used by its already verified next contract.
    pub(super) position: Expr,
    /// Initial sequence length in the macro's ordinary exhaustion postcondition.
    pub(super) length: Expr,
    /// Macro snapshot before next; nested bodies observe this visit's head.
    previous: Expr,
    /// Exhaustion break, recorded and checked by ordinary body accounting.
    pub(super) exhaustion: u64,
    /// Original match identity, replaced only in the symbolic successful visit.
    dispatch: u64,
    /// Binding selected by Some, with its real compiler type and identity.
    binding: Pattern,
    /// Next operation, evaluated as successful only within a counted visit.
    next: Expr,
    /// Selected arm, including the macro's assignment to the yielded local.
    selected: Expr,
}

/// Turn the wrapper's irrefutable match into the equivalent lexical binding.
/// Existing variables retain their modes; executable initialization and the
/// loop-isolation boundary are preserved. No source loop is lowered again.
pub(super) fn prepare(
    function: &Function,
    modes: &HashMap<VarIdent, Mode>,
    fresh: &dyn Fn(&Span) -> Span,
) -> Result<Function, VirErr> {
    if function.x.attrs.resource_contract.is_none() {
        return Ok(function.clone());
    }
    let Some(body) = &function.x.body else { return Ok(function.clone()) };
    // Keep functions without for lowering in their original representation.
    let has_for = crate::ast_visitor::expr_visitor_check(body, &mut |_, expr| {
        if matches!(expr.x, ExprX::Loop { is_for_loop: true, .. }) { Err(()) } else { Ok(()) }
    })
    .is_err();
    if !has_for {
        return Ok(function.clone());
    }
    struct Lowering<'a> {
        /// The same mode information used by body accounting and call discovery.
        modes: &'a HashMap<VarIdent, Mode>,
        /// Synthesized declarations require identities distinct from source nodes.
        fresh: &'a dyn Fn(&Span) -> Span,
    }
    impl AstVisitor<Rewrite, VirErr, NoScoper> for Lowering<'_> {
        fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
            Ok(typ.clone())
        }
        fn visit_pattern(&mut self, pattern: &Pattern) -> Result<Pattern, VirErr> {
            Ok(pattern.clone())
        }
        fn visit_place(&mut self, place: &Place) -> Result<Place, VirErr> {
            self.visit_place_rec(place)
        }
        fn visit_stmt(&mut self, statement: &Stmt) -> Result<Vec<Stmt>, VirErr> {
            if super::execution::ignored_statement(statement, self.modes) {
                return Ok(vec![statement.clone()]);
            }
            let statement = self.visit_stmt_rec(statement)?;
            // The lowering uses `let () = body` to enforce a unit source body.
            // Rust has already checked that pattern; evaluating its initializer
            // as a statement retains the same scope without inventing a slot.
            if let StmtX::Decl { pattern, init: Some(init), els: None, .. } = &statement.x
                && let PatternX::Constructor(Dt::Tuple(0), _, fields) = &pattern.x
                && fields.is_empty()
                && let PlaceX::Temporary(value) = &init.x
            {
                return Ok(vec![crate::def::Spanned::new(
                    statement.span.clone(),
                    StmtX::Expr(value.clone()),
                )]);
            }
            Ok(vec![statement])
        }
        fn visit_expr(&mut self, original: &Expr) -> Result<Expr, VirErr> {
            if super::execution::ignored_expression(original) {
                return Ok(original.clone());
            }
            // Loop specifications are already mode-checked and stay untouched.
            if let ExprX::Loop { cond, body, .. } = &original.x {
                let cond = cond.as_ref().map(|cond| self.visit_expr(cond)).transpose()?;
                let body = self.visit_expr(body)?;
                let mut rewritten = original.clone();
                let ExprX::Loop { cond: target_cond, body: target_body, .. } =
                    &mut Arc::make_mut(&mut rewritten).x
                else {
                    unreachable!()
                };
                *target_cond = cond;
                *target_body = body;
                return Ok(rewritten);
            }
            let expr = self.visit_expr_rec(original)?;
            let ExprX::Match(source, arms, _) = &expr.x else { return Ok(expr.clone()) };
            if iterators::kind(&source.typ) != Some(iterators::Kind::Wrapper) {
                return Ok(expr.clone());
            }
            let [arm] = arms.as_slice() else { return Ok(expr.clone()) };
            let PatternX::Var(binding) = &arm.x.pattern.x else { return Ok(expr.clone()) };
            if binding.by_ref != ByRef::No
                || !matches!(arm.x.guard.x, ExprX::Const(Constant::Bool(true)))
                || !matches!(arm.x.body.x, ExprX::Loop { is_for_loop: true, .. })
            {
                return Ok(expr.clone());
            }
            let declaration = crate::def::Spanned::new(
                (self.fresh)(&expr.span),
                StmtX::Decl {
                    pattern: arm.x.pattern.clone(),
                    mode: Some((Mode::Exec, DeclProph::Default)),
                    init: Some(source.clone()),
                    els: None,
                    assert_irrefutable: false,
                },
            );
            Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Block(Arc::new(vec![declaration]), Some(arm.x.body.clone())),
            ))
        }
    }
    let body = Lowering { modes, fresh }.visit_expr(body)?;
    let mut function = function.clone();
    Arc::make_mut(&mut function).x.body = Some(body);
    Ok(function)
}

fn strip(value: &Expr) -> &Expr {
    match &value.x {
        ExprX::Block(statements, Some(tail)) if statements.is_empty() => strip(tail),
        ExprX::NeverToAny(inner) => strip(inner),
        _ => value,
    }
}

impl ForLoop {
    /// Only the macro's checked wrapper-next dispatch supplies iteration facts.
    /// A different lowering or an unsupported yield shape fails explicitly.
    pub(super) fn new(body: &Expr, invs: &LoopInvariants, label: &Label) -> Result<Self, VirErr> {
        let mut dispatch = None;
        crate::ast_visitor::expr_visitor_check(body, &mut |_, expr| {
            if let ExprX::Match(source, arms, _) = &expr.x
                && let PlaceX::Temporary(next) = &source.x
                && let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } =
                    &next.x
                && attrs.resource_intrinsic == Some(ResourceIntrinsic::IteratorNext)
                && let Some(argument) = args.first()
                && let Some(name) = iterators::receiver(argument)
            {
                // Nested for loops have different compiler-resolved labels.
                let exhausted = arms.iter().find_map(|arm| {
                    let ExprX::BreakOrContinue { label: target, is_break: true, value: None } =
                        &strip(&arm.x.body).x
                    else {
                        return None;
                    };
                    (target == label).then_some(strip(&arm.x.body).span.id)
                });
                if let Some(exhaustion) = exhausted {
                    dispatch = Some((expr.clone(), next.clone(), name, exhaustion));
                }
            }
            Ok::<(), VirErr>(())
        })?;
        let Some((dispatch, next, receiver, exhaustion)) = dispatch else {
            return Err(unsupported(&body.span, "this for-loop iterator dispatch"));
        };
        let ExprX::Match(_, arms, _) = &dispatch.x else { unreachable!() };
        let selected = arms.iter().find_map(|arm| {
            let PatternX::Constructor(_, variant, fields) = &arm.x.pattern.x else { return None };
            if variant.as_str() != "Some" {
                return None;
            }
            let [field] = fields.as_slice() else { return None };
            matches!(field.a.x, PatternX::Var(_)).then_some((field.a.clone(), arm.x.body.clone()))
        });
        let Some((binding, selected)) = selected else {
            return Err(unsupported(&dispatch.span, "this for-loop item pattern"));
        };
        let mut bounds = None;
        for invariant in invs.iter() {
            if let ExprX::UnaryOpr(UnaryOpr::AutoLoopEnsures, value) = &invariant.inv.x
                && let ExprX::Binary(BinaryOp::Eq(_), position, length) = &value.x
            {
                bounds = Some((position.clone(), length.clone()));
            }
        }
        let Some((position, length)) = bounds else {
            return Err(unsupported(
                &body.span,
                "for loops without the standard iterator invariants",
            ));
        };
        let mut previous = None;
        let mut advanced = false;
        crate::ast_visitor::expr_visitor_check(body, &mut |_, value| {
            advanced |= value.span.id == next.span.id && matches!(value.x, ExprX::Call { .. });
            if !advanced
                && previous.is_none()
                && let ExprX::Assign { place, rhs, .. } = &value.x
                && iterators::kind(&place.typ) == Some(iterators::Kind::Wrapper)
                && super::paths::expr(rhs, &place.typ)
                    .is_some_and(|(name, path)| name == receiver && path.is_empty())
                && let PlaceX::Local(name) = &place.x
            {
                previous =
                    Some(SpannedTyped::new(&place.span, &place.typ, ExprX::Var(name.clone())));
            }
            Ok::<(), VirErr>(())
        })?;
        let previous = previous.ok_or_else(|| {
            unsupported(&body.span, "a for loop without its pre-advance snapshot")
        })?;
        Ok(Self {
            receiver,
            position,
            length,
            previous,
            exhaustion,
            dispatch: dispatch.span.id,
            binding,
            next,
            selected,
        })
    }

    /// Next advances the executable wrapper before the user's body runs. Facts
    /// inherited by nested loops describe the saved head, not that advanced state.
    /// Ordinary entry checks still prove each rewritten fact at the nested loop.
    pub(super) fn body_fact(&self, fact: &Expr) -> Result<Expr, VirErr> {
        let ExprX::Var(previous) = &self.previous.x else { unreachable!() };
        crate::ast_visitor::map_expr_place_visitor(
            fact,
            &|value| {
                Ok(if matches!(&value.x, ExprX::Var(name) if name == &self.receiver) {
                    self.previous.clone()
                } else {
                    value.clone()
                })
            },
            &|place| {
                Ok(if matches!(&place.x, PlaceX::Local(name) if name == &self.receiver) {
                    SpannedTyped::new(&place.span, &place.typ, PlaceX::Local(previous.clone()))
                } else {
                    place.clone()
                })
            },
        )
    }

    /// The finite count describes successful advances, excluding the final None.
    pub(super) fn successful_body(&self, body: &Expr) -> Result<Expr, VirErr> {
        crate::ast_visitor::map_expr_visitor(body, &|expr| {
            if expr.span.id != self.dispatch || !matches!(expr.x, ExprX::Match(..)) {
                return Ok(expr.clone());
            }
            let next = SpannedTyped::new(&self.next.span, &self.binding.typ, self.next.x.clone());
            let declaration = crate::def::Spanned::new(
                self.binding.span.clone(),
                StmtX::Decl {
                    pattern: self.binding.clone(),
                    mode: Some((Mode::Exec, DeclProph::Default)),
                    init: Some(SpannedTyped::new(
                        &next.span,
                        &next.typ,
                        PlaceX::Temporary(next.clone()),
                    )),
                    els: None,
                    assert_irrefutable: false,
                },
            );
            Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Block(Arc::new(vec![declaration]), Some(self.selected.clone())),
            ))
        })
    }
}
