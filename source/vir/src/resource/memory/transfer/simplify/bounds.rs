//! Scalar decompositions and allocation-bound candidates for checked loop proofs.
//!
//! Candidate ceilings require operation-site proof obligations. They never
//! replace the actual allocation fields in exported ownership forests.

use super::super::expr;
use super::simplify;
use crate::ast::*;
use crate::resource::memory::contracts;

/// Decompose a scalar extent into `slope * index + intercept`. Only algebraic
/// identities are recognized; arbitrary metadata lookups retain their generator.
pub(in super::super) fn affine(value: &Expr, index: &VarIdent) -> Option<(Expr, Expr)> {
    let span = &value.span;
    if crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
        if matches!(&value.x, ExprX::Var(name) if name == index) { Err(()) } else { Ok(()) }
    })
    .is_ok()
    {
        return Some((expr::integer(span, 0), value.clone()));
    }
    if matches!(&value.x, ExprX::Var(name) if name == index) {
        return Some((expr::integer(span, 1), expr::integer(span, 0)));
    }
    let ExprX::Binary(BinaryOp::Arith(op), left, right) = &value.x else {
        return None;
    };
    let (a, b) = affine(left, index)?;
    let (c, d) = affine(right, index)?;
    let pair = match op {
        ArithOp::Add(_) => (contracts::add(span, a, c), contracts::add(span, b, d)),
        ArithOp::Sub(_) => (contracts::subtract(span, a, c), contracts::subtract(span, b, d)),
        ArithOp::Mul(_) if contracts::constant(&a) == Some(0) => {
            (contracts::multiply(span, b.clone(), c), contracts::multiply(span, b, d))
        }
        ArithOp::Mul(_) if contracts::constant(&c) == Some(0) => {
            (contracts::multiply(span, a, d.clone()), contracts::multiply(span, b, d))
        }
        _ => return None,
    };
    Some((simplify(&pair.0), simplify(&pair.1)))
}

/// Propose a scalar ceiling for allocation observations of a selected child.
/// Only proof candidates use this substitution; exported forests retain the
/// actual descriptor fields. Operation-site obligations prove each candidate.
pub(in super::super) fn allocation_bound(
    value: &Expr,
    tokens: &std::collections::HashSet<VarIdent>,
    ceiling: &Expr,
) -> Expr {
    crate::ast_visitor::map_expr_visitor(value, &|expression| {
        if let ExprX::UnaryOpr(UnaryOpr::Field(_), record) = &expression.x {
            if crate::ast_util::types_equal(&record.typ, &expr::record_type()) {
                let dependent = crate::ast_visitor::expr_visitor_check(record, &mut |_, value| {
                    if matches!(&value.x, ExprX::Var(name) if tokens.contains(name)) {
                        Err(())
                    } else {
                        Ok(())
                    }
                })
                .is_err();
                if dependent {
                    return Ok::<Expr, VirErr>(ceiling.clone());
                }
            }
        }
        Ok::<Expr, VirErr>(expression.clone())
    })
    .expect("infallible allocation-bound construction")
}
