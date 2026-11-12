//! Classify effect-free loop-head exits as an additional comparison boundary.
//!
//! This selects an exact repetition candidate; the source body and its real
//! break edges remain authoritative for cleanup and ordinary proof checking.

use super::*;
use crate::ast_util::mk_ineq;
use std::sync::Arc;

fn only_break(value: &Expr, label: &Label) -> Option<u64> {
    match &value.x {
        ExprX::NeverToAny(inner) => only_break(inner, label),
        ExprX::ReadPlace(place, _) => match &place.x {
            PlaceX::Temporary(inner) => only_break(inner, label),
            _ => None,
        },
        ExprX::Block(statements, tail) => match (statements.as_slice(), tail) {
            ([], Some(tail)) => only_break(tail, label),
            ([statement], None) => match &statement.x {
                StmtX::Expr(value) => only_break(value, label),
                _ => None,
            },
            _ => None,
        },
        ExprX::BreakOrContinue { label: target, is_break: true, value: None }
            if target == label =>
        {
            Some(value.span.id)
        }
        _ => None,
    }
}

fn comparison(condition: &Expr) -> Option<Control> {
    let ExprX::Binary(BinaryOp::Inequality(comparison), start, end) = &condition.x else {
        return None;
    };
    // Only pure scalar observations can be omitted from the repeated body.
    // Calls and allocation effects must execute under their ordinary rules.
    let mut pure = true;
    crate::ast_visitor::expr_visitor_check(condition, &mut |_, value| {
        pure &= !matches!(value.x, ExprX::Call { .. } | ExprX::Assign { .. });
        Ok::<(), VirErr>(())
    })
    .ok()?;
    if !pure {
        return None;
    }
    Some(Control {
        start: start.clone(),
        end: end.clone(),
        counter: local(start),
        comparison: match comparison {
            InequalityOp::Lt => InequalityOp::Ge,
            InequalityOp::Le => InequalityOp::Gt,
            InequalityOp::Gt => InequalityOp::Le,
            InequalityOp::Ge => InequalityOp::Lt,
        },
    })
}

fn intersect(span: &Span, first: Option<Control>, next: Control) -> Option<Control> {
    let Some(first) = first else { return Some(next) };
    if first.comparison != next.comparison
        || first.counter.is_none()
        || first.counter != next.counter
    {
        return None;
    }
    let upper = matches!(first.comparison, InequalityOp::Lt | InequalityOp::Le);
    let choose = mk_ineq(
        span,
        &first.end,
        &next.end,
        if upper { InequalityOp::Le } else { InequalityOp::Ge },
    );
    let end = SpannedTyped::new(
        span,
        &first.end.typ,
        ExprX::If(choose, first.end.clone(), Some(next.end)),
    );
    Some(Control { end, ..first })
}

pub(super) fn head_breaks(
    body: &Expr,
    label: &Label,
    control: Option<Control>,
) -> (Option<Control>, Expr, Vec<u64>) {
    let ExprX::Block(statements, tail) = &body.x else {
        return (control, body.clone(), Vec::new());
    };
    if statements.is_empty()
        && let Some(tail) = tail
    {
        let (control, inner, exits) = head_breaks(tail, label, control);
        return (
            control,
            SpannedTyped::new(&body.span, &body.typ, ExprX::Block(statements.clone(), Some(inner))),
            exits,
        );
    }
    let mut control = control;
    let mut exits = Vec::new();
    for statement in statements.iter() {
        let StmtX::Expr(value) = &statement.x else { break };
        let ExprX::If(condition, yes, None) = &value.x else { break };
        let Some(id) = only_break(yes, label) else { break };
        let Some(next) = comparison(condition) else { break };
        let Some(combined) = intersect(&body.span, control.clone(), next) else { break };
        control = Some(combined);
        exits.push(id);
    }
    let remaining = Arc::new(statements[exits.len()..].to_vec());
    let iteration = SpannedTyped::new(&body.span, &body.typ, ExprX::Block(remaining, tail.clone()));
    (control, iteration, exits)
}
