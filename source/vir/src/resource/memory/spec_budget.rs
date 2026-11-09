//! Numeric spec calls stay opaque to accounting and are interpreted by Verus.
//!
//! Budget headers are removed before ordinary mode checking. Validate their
//! callees and arguments here before inserting them into generated assertions.

use super::contracts;
use crate::ast::*;
use crate::messages::error;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Admit a direct, local numeric specification with stable scalar arguments.
/// Its body receives ordinary Verus checking; accounting never evaluates it.
pub(super) fn validate(
    expr: &Expr,
    allowed: &HashSet<VarIdent>,
    functions: &HashMap<Fun, Function>,
) -> Result<Expr, VirErr> {
    let ExprX::Call {
        target: CallTarget::Fun(CallTargetKind::Static, name, types, impls, attrs),
        args,
        post_args: None,
        body: None,
    } = &expr.x
    else {
        return Err(error(&expr.span, "memory budgets require a direct spec function call"));
    };
    let function = functions.get(name).ok_or_else(|| {
        error(&expr.span, "memory budget spec functions must be defined in this crate")
    })?;
    let f = &function.x;
    if f.mode != Mode::Spec
        || !matches!(f.kind, FunctionKind::Static)
        || !f.typ_params.is_empty()
        || !f.typ_bounds.is_empty()
        || !types.is_empty()
        || !impls.is_empty()
        || attrs.resource_intrinsic.is_some()
        || f.attrs.autospec.is_some()
        || f.proxy.is_some()
        || f.attrs.is_external_body
        || f.body.is_none()
        || f.params.iter().any(|p| p.x.mode != Mode::Spec)
    {
        return Err(error(
            &expr.span,
            "memory budgets require a local, nongeneric spec function with a verified body",
        ));
    }
    if !matches!(&*expr.typ, TypX::Int(IntRange::Nat | IntRange::U(64))) {
        return Err(error(&expr.span, "memory budget spec functions must return nat or u64"));
    }
    let args =
        args.iter().map(|arg| argument(arg, allowed, functions)).collect::<Result<Vec<_>, _>>()?;
    // The ordinary autospec pass has already run on executable/spec bodies,
    // but not on erased budget metadata. This target is already a checked spec
    // function, so finalize it without redirecting to an executable function.
    let attrs = CallTargetAttrs {
        autospec: AutospecUsage::Final,
        assume_external_allowed: false,
        ..attrs.clone()
    };
    let target =
        CallTarget::Fun(CallTargetKind::Static, name.clone(), types.clone(), impls.clone(), attrs);
    Ok(SpannedTyped::new(
        &expr.span,
        &expr.typ,
        ExprX::Call { target, args: Arc::new(args), post_args: None, body: None },
    ))
}

/// Keep the first integration limited to scalar inputs, comparisons, casts to
/// mathematical integers, and nested numeric spec calls. No runtime work or
/// mutable state can become an unchecked budget assumption.
fn argument(
    expr: &Expr,
    allowed: &HashSet<VarIdent>,
    functions: &HashMap<Fun, Function>,
) -> Result<Expr, VirErr> {
    match &expr.x {
        ExprX::Call { .. } => validate(expr, allowed, functions),
        ExprX::Unary(op @ UnaryOp::Clip { range: IntRange::Int | IntRange::Nat, .. }, value) => {
            Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Unary(*op, argument(value, allowed, functions)?),
            ))
        }
        _ => contracts::predicate(expr, allowed),
    }
}
