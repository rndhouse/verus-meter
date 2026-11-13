//! Exact scalar identities, allocation fields, and memory-kind cost rewrites.

use super::super::{choice, expr};
use super::inspect::{call, empty};
use super::simplify;
use crate::ast::*;
use crate::resource::memory::contracts;

/// Apply additive and multiplicative identities to unbounded arithmetic.
pub(super) fn arithmetic(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let ExprX::Binary(BinaryOp::Arith(op), left, right) = &value.x {
        match op {
            ArithOp::Add(OverflowBehavior::Allow) | ArithOp::Sub(OverflowBehavior::Allow)
                if contracts::constant(right) == Some(0) =>
            {
                return Some(left.clone());
            }
            ArithOp::Add(OverflowBehavior::Allow) if contracts::constant(left) == Some(0) => {
                return Some(right.clone());
            }
            ArithOp::Mul(OverflowBehavior::Allow)
                if contracts::constant(right) == Some(0)
                    || contracts::constant(left) == Some(0) =>
            {
                return Some(expr::integer(span, 0));
            }
            ArithOp::Mul(OverflowBehavior::Allow) if contracts::constant(right) == Some(1) => {
                return Some(left.clone());
            }
            ArithOp::Mul(OverflowBehavior::Allow) if contracts::constant(left) == Some(1) => {
                return Some(right.clone());
            }
            _ => {}
        }
    }
    None
}

/// Read known allocation descriptor fields without changing their types.
pub(super) fn record_field(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let ExprX::UnaryOpr(UnaryOpr::Field(field), record) = &value.x {
        if let Some(args) = call(record, "allocated") {
            let index = match field.field.as_str() {
                "kind" => 1,
                "bytes" => 2,
                "capacity" => 3,
                "length" => 4,
                _ => return Some(value.clone()),
            };
            return Some(SpannedTyped::new(span, &value.typ, args[index].x.clone()));
        }
    }
    None
}

/// Distribute memory-kind costs through finite forest constructors.
pub(super) fn cost(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let Some(args) = call(value, "cost") {
        let memory = &args[0];
        let kind = &args[1];
        let cost = |memory: Expr| expr::cost(span, memory, kind.clone());
        if empty(memory) {
            return Some(expr::integer(span, 0));
        }
        if let Some(parts) = call(memory, "add") {
            return Some(simplify(&contracts::add(
                span,
                cost(parts[0].clone()),
                cost(parts[1].clone()),
            )));
        }
        if let Some(parts) = call(memory, "prefix").or_else(|| call(memory, "shift_children")) {
            return Some(simplify(&cost(parts[0].clone())));
        }
        if let Some(parts) = call(memory, "repeat").or_else(|| call(memory, "tile_children")) {
            return Some(simplify(&contracts::multiply(
                span,
                parts[2].clone(),
                cost(parts[0].clone()),
            )));
        }
        if let Some(parts) = call(memory, "push") {
            if let Some(record) = call(&parts[1], "allocated") {
                let amount = choice(
                    span,
                    crate::ast_util::mk_eq(span, &record[1], kind),
                    record[2].clone(),
                    expr::integer(span, 0),
                );
                return Some(simplify(&contracts::add(span, cost(parts[0].clone()), amount)));
            }
        }
    }
    None
}

/// Fold fully constant scalar operations after the structural rules decline.
pub(super) fn fold_constants(value: &Expr) -> Expr {
    let constant = |value: &Expr| matches!(value.x, ExprX::Const(_));
    let fold = match &value.x {
        ExprX::Unary(_, a) => constant(a),
        ExprX::Binary(_, a, b) | ExprX::Logical(_, a, b) => constant(a) && constant(b),
        _ => false,
    };
    if fold { contracts::simplify(value) } else { value.clone() }
}
