//! Preserve zero local charges when pending updates expand a counter into a
//! forest cost. This says nothing about executable cardinality or reservation.
//! Only zero-charge-preserving operations participate; unknown expressions stay
//! symbolic and receive the existing checked contract bound at call composition.

use crate::ast::*;
use crate::resource::memory::contracts;
use std::collections::HashSet;

pub(in super::super) fn simplify(
    value: &Expr,
    scalars: &HashSet<VarIdent>,
    forests: &HashSet<VarIdent>,
) -> Result<Expr, VirErr> {
    let value = crate::ast_visitor::map_expr_visitor(value, &|value| {
        Ok(match &value.x {
            ExprX::Var(name) if scalars.contains(name) => contracts::literal(&value.span, 0),
            _ if zero_cost(value, forests) => contracts::literal(&value.span, 0),
            _ => value.clone(),
        })
    })?;
    Ok(contracts::simplify(&value))
}

fn zero_cost(value: &Expr, forests: &HashSet<VarIdent>) -> bool {
    matches!(&value.x, ExprX::Call { target: CallTarget::Fun(_, fun, _, _, _), args, .. }
        if super::expr::is_operation(fun, "cost") && zero_forest(&args[0], forests))
}

fn zero_forest(value: &Expr, forests: &HashSet<VarIdent>) -> bool {
    if let ExprX::Var(name) = &value.x {
        return forests.contains(name);
    }
    let ExprX::Call { target: CallTarget::Fun(_, fun, _, _, _), args, .. } = &value.x else {
        return false;
    };
    if *fun == crate::fun!(CrateId::Vstd => "seq", "Seq"; "empty") {
        return true;
    }
    if *fun == crate::fun!(CrateId::Vstd => "seq", "Seq"; "add") {
        return args.iter().all(|arg| zero_forest(arg, forests));
    }
    if *fun == crate::fun!(CrateId::Vstd => "seq", "Seq"; "push") {
        return zero_forest(&args[0], forests) && zero_record(&args[1]);
    }
    [
        "subtree",
        "without",
        "prefix",
        "runtime",
        "nonruntime",
        "descendants",
        "remove_index",
        "repeat",
        "take_children",
    ]
    .iter()
    .any(|name| super::expr::is_operation(fun, name))
        && zero_forest(&args[0], forests)
}

fn zero_record(value: &Expr) -> bool {
    matches!(&value.x, ExprX::Call { target: CallTarget::Fun(_, fun, _, _, _), args, .. }
        if super::expr::is_operation(fun, "allocated")
            && contracts::constant(&contracts::simplify(&args[2])) == Some(0))
}
