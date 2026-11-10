//! Versioned contract, word-size policy, and function/operator eligibility.

use crate::ast::*;
use crate::messages::{Span, error};
use serde::{Deserialize, Serialize};
use vir_macros::ToDebugSNode;

pub(super) const MODEL_NAME: &str = "source-values-v19-64";
pub(super) const WORD_BYTES: u64 = 8;

/// Current source-storage contract. This unreleased format has no legacy variants.
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct ResourceContract {
    /// Simultaneous workspace allowed by this function.
    pub budget: super::BudgetExpr,
}

pub(super) fn unsupported(span: &Span, what: &str) -> VirErr {
    error(span, format!("resource model {MODEL_NAME} does not support {what}"))
}

pub(super) fn unit(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Datatype(Dt::Tuple(0), _, _))
}

/// Native integer widths share one policy across layouts, operators and contracts.
/// Pointer-sized integers use the model's fixed word size, not the host layout.
pub(super) fn integer_size(range: &IntRange) -> Option<u64> {
    match range {
        IntRange::U(bits @ (8 | 16 | 32 | 64 | 128))
        | IntRange::I(bits @ (8 | 16 | 32 | 64 | 128)) => Some(u64::from(*bits) / 8),
        IntRange::USize | IntRange::ISize => Some(WORD_BYTES),
        _ => None,
    }
}

pub(super) fn integer_type_size(typ: &Typ) -> Option<u64> {
    if let TypX::Int(range) = &**typ { integer_size(range) } else { None }
}

pub(super) fn slice(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Primitive(Primitive::Slice, args)
        if args.len() == 1)
}

pub(super) fn arithmetic(op: &BinaryOp) -> bool {
    match op {
        BinaryOp::Arith(
            ArithOp::Add(OverflowBehavior::Error(range))
            | ArithOp::Sub(OverflowBehavior::Error(range))
            | ArithOp::Mul(OverflowBehavior::Error(range)),
        ) => integer_size(range).is_some(),
        _ => false,
    }
}

/// Rust lowering represents a negative literal as unchecked `0 - magnitude`.
/// Recognize that literal alone; all executable arithmetic retains overflow checks.
pub(super) fn negative_literal(expr: &Expr) -> Option<Constant> {
    if !matches!(&*expr.typ, TypX::Int(IntRange::I(_) | IntRange::ISize))
        || integer_type_size(&expr.typ).is_none()
    {
        return None;
    }
    if let ExprX::Binary(BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Allow)), a, b) = &expr.x
        && let (ExprX::Const(Constant::Int(zero)), ExprX::Const(Constant::Int(magnitude))) =
            (&a.x, &b.x)
        && *zero == 0.into()
        && *magnitude >= 0.into()
    {
        Some(Constant::Int(-magnitude))
    } else {
        None
    }
}

pub(super) fn eligible(function: &Function) -> Result<(), VirErr> {
    let f = &function.x;
    if f.mode != Mode::Exec
        || !matches!(f.kind, FunctionKind::Static)
        || !matches!(f.item_kind, ItemKind::Function)
        || !f.typ_params.is_empty()
        || !f.typ_bounds.is_empty()
        || f.attrs.is_async
        || f.attrs.is_unsafe
        || f.attrs.is_external_body
        || f.proxy.is_some()
    {
        return Err(unsupported(
            &function.span,
            "this function (expected a safe, nongeneric exec function)",
        ));
    }
    if f.body.is_none() {
        return Err(unsupported(&function.span, "functions without a verified body"));
    }
    Ok(())
}
