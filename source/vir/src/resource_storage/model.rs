//! Versioned contract, word-size policy, and function/operator eligibility.

use crate::ast::*;
use crate::messages::{Span, error};
use serde::{Deserialize, Serialize};
use vir_macros::ToDebugSNode;

pub(super) const MODEL_NAME: &str = "lexical-slots-v5-64";
pub(super) const WORD_BYTES: u64 = 8;

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum ResourceContract {
    // Keep the original discriminant: a new model must never deserialize as
    // the old model merely because the Rust variant was renamed.
    LexicalSlotsV0 {
        budget: u64,
    },
    LexicalSlotsV1_64 {
        budget: u64,
    },
    LexicalSlotsV2_64 {
        budget: u64,
    },
    LexicalSlotsV3_64 {
        budget: u64,
    },
    /// Historical v3 model with compile-time budget expressions.
    LexicalSlotsV3Expr {
        budget: super::BudgetExpr,
    },
    /// Aggregate initialization uses its destination's existing storage charge.
    LexicalSlotsV4Expr {
        budget: super::BudgetExpr,
    },
    /// Source storage objects only; no inferred expression/address temporaries.
    LexicalSlotsV5Expr {
        budget: super::BudgetExpr,
    },
}

pub(super) fn unsupported(span: &Span, what: &str) -> VirErr {
    error(span, format!("resource model {MODEL_NAME} does not support {what}"))
}

pub(super) fn unit(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Datatype(Dt::Tuple(0), _, _))
}

pub(super) fn slice(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Primitive(Primitive::Slice, args)
        if args.len() == 1 && matches!(&*args[0], TypX::Int(IntRange::U(32))))
}

pub(super) fn arithmetic(op: &BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Arith(
            ArithOp::Add(OverflowBehavior::Error(IntRange::U(32) | IntRange::USize))
                | ArithOp::Sub(OverflowBehavior::Error(IntRange::U(32) | IntRange::USize))
                | ArithOp::Mul(OverflowBehavior::Error(IntRange::U(32) | IntRange::USize))
        )
    )
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
        || !unit(&f.outer_ret.x.typ)
    {
        return Err(unsupported(
            &function.span,
            "this function (expected a safe, nongeneric exec function returning unit)",
        ));
    }
    if f.body.is_none() {
        return Err(unsupported(&function.span, "functions without a verified body"));
    }
    Ok(())
}
