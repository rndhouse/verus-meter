//! Closed forest powers for stationary paths and affine descriptor updates.
//!
//! These candidates retain complete forests. Use-site induction proves equality
//! with the checked recurrence; recognition grants no ownership or byte facts.

use super::*;
use crate::resource::memory::{accounting::Accounting, contracts};
use std::sync::Arc;

/// Propose a closed form for stationary overwrites and descriptor translations.
/// Other programs retain the exact recurrence and its finite proof window.
pub(super) fn closed(span: &Span, step: &Expr, initial: &Expr, count: &Expr) -> Option<Expr> {
    let ExprX::Closure(binders, body) = &step.x else { return None };
    let ordinal = &binders[0].name;
    let state = &binders[1].name;
    let name = VarIdent(
        Arc::new("$memory_closed_visits".into()),
        VarIdentDisambiguate::VirTemp(Accounting::fresh_allocation()),
    );
    let visits = SpannedTyped::new(span, &crate::ast_util::int_typ(), ExprX::Var(name.clone()));
    let lifted = crate::ast_visitor::map_expr_visitor(body, &|value| {
        if let Some(args) = simplify::call(value, "allocated") {
            if !independent(&args[0], ordinal) || !independent(&args[0], state) {
                return Err(super::super::model::unsupported(
                    &value.span,
                    "a nonstationary descriptor recurrence",
                ));
            }
            let mut args = args.as_ref().clone();
            for value in &mut args[1..] {
                *value = numeric(value, state, ordinal, &visits).ok_or_else(|| {
                    super::super::model::unsupported(
                        &value.span,
                        "a nonaffine descriptor recurrence",
                    )
                })?;
            }
            return Ok(expr::operation(&value.span, "allocated", args, value.typ.clone()));
        }
        if let ExprX::If(condition, _, _) = &value.x {
            if !independent(condition, ordinal) || !independent(condition, state) {
                return Err(super::super::model::unsupported(
                    &value.span,
                    "a nonstationary descriptor recurrence",
                ));
            }
        }
        for operation in [
            "remove_index",
            "take_children",
            "reverse_children",
            "iterate",
            "generate_children",
            "tile_children",
        ] {
            if simplify::call(value, operation).is_some() {
                return Err(super::super::model::unsupported(
                    &value.span,
                    "a nonstationary descriptor recurrence",
                ));
            }
        }
        for operation in ["subtree", "without", "prefix", "replace"] {
            if let Some(args) = simplify::call(value, operation) {
                if !independent(&args[1], ordinal) || !independent(&args[1], state) {
                    return Err(super::super::model::unsupported(
                        &value.span,
                        "a nonstationary descriptor recurrence",
                    ));
                }
            }
        }
        Ok(value.clone())
    })
    .ok()?;
    let lifted = substitute(
        &lifted,
        &HashMap::from([
            (state.clone(), initial.clone()),
            (ordinal.clone(), contracts::subtract(span, visits.clone(), expr::integer(span, 1))),
        ]),
    );
    let body = choice(
        span,
        crate::ast_util::mk_ineq(span, &visits, &expr::integer(span, 0), InequalityOp::Le),
        initial.clone(),
        lifted,
    );
    let closed = SpannedTyped::new(
        span,
        &Arc::new(TypX::SpecFn(Arc::new(vec![crate::ast_util::int_typ()]), expr::memory_type())),
        ExprX::Closure(
            Arc::new(vec![Arc::new(VarBinderX { name, a: crate::ast_util::int_typ() })]),
            body,
        ),
    );
    Some(expr::operation(
        span,
        "iterate_closed",
        vec![step.clone(), initial.clone(), count.clone(), closed],
        expr::memory_type(),
    ))
}

/// Only free observations participate in recurrence classification.
fn independent(value: &Expr, name: &VarIdent) -> bool {
    crate::ast_visitor::expr_visitor_check(value, &mut |scope, value| {
        if matches!(&value.x, ExprX::Var(var) if var == name && !scope.contains_key(var)) {
            Err(super::super::model::unsupported(
                &value.span,
                "a nonstationary descriptor recurrence",
            ))
        } else {
            Ok(())
        }
    })
    .is_ok()
}

/// A descriptor either overwrites its field or translates one prior observation
/// by a stable quantity. Higher scalar recurrences need another closed form.
fn numeric(value: &Expr, state: &VarIdent, ordinal: &VarIdent, visits: &Expr) -> Option<Expr> {
    if independent(value, state) {
        return Some(value.clone());
    }
    let mut observations = Vec::<Expr>::new();
    crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
        if let ExprX::UnaryOpr(UnaryOpr::Field(_), record) = &value.x {
            if crate::ast_util::types_equal(&record.typ, &expr::record_type())
                && !independent(value, state)
                && !observations.iter().any(|old| simplify::same_expression(old, value))
            {
                observations.push(value.clone());
            }
        }
        Ok::<(), ()>(())
    })
    .ok()?;
    let [observation] = observations.as_slice() else { return None };
    if !independent(observation, ordinal) {
        return None;
    }
    let name = VarIdent(
        Arc::new("$memory_affine_descriptor".into()),
        VarIdentDisambiguate::VirTemp(Accounting::fresh_allocation()),
    );
    let token =
        SpannedTyped::new(&value.span, &crate::ast_util::int_typ(), ExprX::Var(name.clone()));
    let value = crate::ast_visitor::map_expr_visitor(value, &|value| {
        Ok::<_, VirErr>(if simplify::same_expression(value, observation) {
            token.clone()
        } else {
            value.clone()
        })
    })
    .ok()?;
    if !independent(&value, state) {
        return None;
    }
    let (slope, offset) = simplify::affine(&value, &name)?;
    if contracts::constant(&slope) != Some(1) || !independent(&offset, ordinal) {
        return None;
    }
    Some(contracts::add(
        &value.span,
        observation.clone(),
        contracts::multiply(&value.span, offset, visits.clone()),
    ))
}
