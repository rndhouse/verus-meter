//! Recognize forest operations, inspect paths and roots, and compare pure expressions.

use super::super::expr;
use crate::ast::*;
use crate::messages::Span;
use std::sync::Arc;

/// Match a canonical sequence or memory-algebra function and expose its arguments.
pub(in super::super) fn call<'a>(value: &'a Expr, name: &str) -> Option<&'a Exprs> {
    let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } = &value.x else {
        return None;
    };
    let expected = match name {
        "empty" => crate::fun!(CrateId::Vstd => "seq", "Seq"; "empty"),
        "push" => crate::fun!(CrateId::Vstd => "seq", "Seq"; "push"),
        "add" => crate::fun!(CrateId::Vstd => "seq", "Seq"; "add"),
        _ => return expr::is_operation(function, name).then_some(args),
    };
    (*function == expected).then_some(args)
}

/// Recognize an explicit empty sequence rather than infer symbolic emptiness.
pub(super) fn empty(value: &Expr) -> bool {
    call(value, "empty").is_some()
}

/// Recover the ordered slots of a path built from finite sequence constructors.
pub(in super::super) fn path(value: &Expr) -> Option<Vec<Expr>> {
    if empty(value) {
        return Some(vec![]);
    }
    let args = call(value, "push")?;
    let mut path = path(&args[0])?;
    path.push(args[1].clone());
    Some(path)
}

/// Build a finite ownership path from its slot expressions.
pub(super) fn make_path(span: &Span, values: &[Expr]) -> Expr {
    values.iter().fold(expr::path(span, []), |path, value| expr::push(span, path, value.clone()))
}

/// Recognize forest constructors that cannot contain an enclosing root record.
pub(super) fn rootless(value: &Expr) -> bool {
    empty(value)
        || call(value, "runtime").is_some()
        || call(value, "descendants").is_some()
        || call(value, "repeat").is_some()
        || call(value, "tile_children").is_some()
        || call(value, "generate_children").is_some()
        || call(value, "shift_children").is_some_and(|args| rootless(&args[0]))
        || call(value, "take_children").is_some()
        || call(value, "reverse_children").is_some()
        || call(value, "prefix")
            .is_some_and(|args| path(&args[1]).is_some_and(|path| !path.is_empty()))
        || call(value, "add").is_some_and(|args| rootless(&args[0]) && rootless(&args[1]))
}

/// Recover an explicit root without unfolding abstract incoming forests.
pub(super) fn known_root(value: &Expr) -> Option<Expr> {
    if let Some(args) = call(value, "with_root") {
        return Some(args[1].clone());
    }
    if let Some(args) = call(value, "push") {
        if call(&args[1], "allocated").is_some_and(|record| empty(&record[0])) {
            return Some(args[1].clone());
        }
    }
    if let Some(args) = call(value, "add") {
        if rootless(&args[1]) {
            return known_root(&args[0]);
        }
    }
    None
}

/// Structural equality for pure expressions used by forest maps and joins.
/// Unknown forms stay distinct; this never asks the solver or guesses an index.
pub(in crate::resource::memory) fn same_expression(a: &Expr, b: &Expr) -> bool {
    if Arc::ptr_eq(a, b) {
        return true;
    }
    if !crate::ast_util::types_equal(&a.typ, &b.typ) {
        return false;
    }
    match (&a.x, &b.x) {
        (ExprX::Var(a), ExprX::Var(b)) => a == b,
        (ExprX::Const(Constant::Int(a)), ExprX::Const(Constant::Int(b))) => a == b,
        (ExprX::Const(Constant::Bool(a)), ExprX::Const(Constant::Bool(b))) => a == b,
        (ExprX::Binary(a, al, ar), ExprX::Binary(b, bl, br)) => {
            a == b && same_expression(al, bl) && same_expression(ar, br)
        }
        (ExprX::Unary(a, al), ExprX::Unary(b, bl)) => a == b && same_expression(al, bl),
        (ExprX::UnaryOpr(UnaryOpr::Field(a), al), ExprX::UnaryOpr(UnaryOpr::Field(b), bl)) => {
            a == b && same_expression(al, bl)
        }
        (ExprX::If(ac, al, Some(ar)), ExprX::If(bc, bl, Some(br))) => {
            same_expression(ac, bc) && same_expression(al, bl) && same_expression(ar, br)
        }
        (
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, af, at, ai, _),
                args: aa,
                post_args: None,
                body: None,
            },
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, bf, bt, bi, _),
                args: ba,
                post_args: None,
                body: None,
            },
        ) => {
            af == bf
                && ai.is_empty()
                && bi.is_empty()
                && crate::ast_util::n_types_equal(at, bt)
                && aa.len() == ba.len()
                && aa.iter().zip(ba.iter()).all(|(a, b)| same_expression(a, b))
        }
        _ => false,
    }
}

/// Expand finite closed forests without disturbing the scoped range algebra
/// used for symbolic caller-supplied ownership. Its requested views and prefix
/// cuts deliberately stay opaque for counterexample queries.
pub(super) fn closed(value: &Expr) -> bool {
    crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
        if matches!(value.x, ExprX::Var(_)) { Err(()) } else { Ok(()) }
    })
    .is_ok()
}
