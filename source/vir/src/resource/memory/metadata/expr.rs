//! Typed expressions for the verified allocation metadata algebra.

use crate::ast::*;
use crate::ast_util::{const_int_from_i128, int_typ, unit_typ};
use crate::def::Spanned;
use crate::messages::Span;
use std::sync::Arc;

pub(in super::super) fn record_type() -> Typ {
    Arc::new(TypX::Datatype(record_name(), Arc::new(vec![]), Arc::new(vec![])))
}

fn record_name() -> Dt {
    super::algebra::record()
}

pub(in super::super) fn sequence_type(element: Typ) -> Typ {
    Arc::new(TypX::Datatype(
        Dt::Path(crate::path!(CrateId::Vstd => "seq", "Seq")),
        Arc::new(vec![element]),
        Arc::new(vec![]),
    ))
}

pub(in super::super) fn memory_type() -> Typ {
    sequence_type(record_type())
}

pub(in super::super) fn integer(span: &Span, n: i128) -> Expr {
    SpannedTyped::new(span, &int_typ(), ExprX::Const(const_int_from_i128(n)))
}

/// Freeze a scalar as erased observation data, without an allocation or strong
/// link. Boolean captures use 0/1; integers retain their mathematical value.
pub(in super::super) fn scalar_observation(span: &Span, path: Expr, value: Expr) -> Expr {
    let value = if matches!(&*value.typ, TypX::Bool) {
        super::super::growth::select(span, value, integer(span, 1), integer(span, 0))
    } else {
        SpannedTyped::new(span, &int_typ(), value.x.clone())
    };
    operation(span, "scalar_observation", vec![path, value], record_type())
}

/// Canonical identity shared by generated calls and scoped definition reveals.
pub(in super::super) fn function(name: &str) -> Fun {
    super::algebra::function(name)
}

/// Match generated operations using their complete, encoded VIR identity.
pub(in super::super) fn is_operation(value: &Fun, name: &str) -> bool {
    super::algebra::is_function(value, name)
}

fn call(span: &Span, name: Fun, types: Vec<Typ>, args: Vec<Expr>, result: Typ) -> Expr {
    SpannedTyped::new(
        span,
        &result,
        ExprX::Call {
            target: CallTarget::Fun(
                CallTargetKind::Static,
                name,
                Arc::new(types),
                Arc::new(vec![]),
                CallTargetAttrs {
                    resource_intrinsic: None,
                    autospec: AutospecUsage::Final,
                    const_var: false,
                    assume_external_allowed: false,
                },
            ),
            args: Arc::new(args),
            post_args: None,
            body: None,
        },
    )
}

pub(in super::super) fn operation(span: &Span, name: &str, args: Vec<Expr>, result: Typ) -> Expr {
    call(span, function(name), vec![], args, result)
}

pub(in super::super) fn lemma(span: &Span, name: &str, args: Vec<Expr>) -> Stmt {
    Spanned::new(span.clone(), StmtX::Expr(operation(span, name, args, unit_typ())))
}

/// A generated metadata obligation with a domain-specific diagnostic. This
/// creates an assertion, never an assumption or an executable storage effect.
pub(in super::super) fn check(span: &Span, condition: Expr, message: &str) -> Stmt {
    Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &unit_typ(),
            ExprX::AssertAssume {
                is_assume: false,
                expr: condition,
                msg: Some(crate::messages::error(span, message)),
            },
        )),
    )
}

/// Explain a generated invariant without changing its proposition. Preserve a
/// more specific origin when a fact is inherited by another loop or proof site.
pub(in super::super) fn purpose(value: Expr, message: &str) -> Expr {
    if matches!(value.x, ExprX::UnaryOpr(UnaryOpr::ProofNote(_), _)) {
        return value;
    }
    SpannedTyped::new(
        &value.span,
        &value.typ,
        ExprX::UnaryOpr(
            UnaryOpr::ProofNote(ProofNoteLabel {
                text: Arc::new(message.into()),
                is_custom_err: false,
            }),
            value.clone(),
        ),
    )
}

pub(in super::super) fn empty(span: &Span, element: Typ) -> Expr {
    call(
        span,
        crate::fun!(CrateId::Vstd => "seq", "Seq"; "empty"),
        vec![element.clone()],
        vec![],
        sequence_type(element),
    )
}

pub(in super::super) fn push(span: &Span, sequence: Expr, element: Expr) -> Expr {
    // Metadata indices are mathematical integers even when the executable
    // index is a usize. Instantiate Seq::push from its receiver, preserving
    // that type across the generated call.
    let TypX::Datatype(_, types, _) = &*sequence.typ else { unreachable!() };
    call(
        span,
        crate::fun!(CrateId::Vstd => "seq", "Seq"; "push"),
        types.as_ref().clone(),
        vec![sequence.clone(), element],
        sequence.typ.clone(),
    )
}

pub(in super::super) fn add(span: &Span, left: Expr, right: Expr) -> Expr {
    let TypX::Datatype(_, types, _) = &*left.typ else { unreachable!() };
    call(
        span,
        crate::fun!(CrateId::Vstd => "seq", "Seq"; "add"),
        types.as_ref().clone(),
        vec![left.clone(), right],
        left.typ.clone(),
    )
}

pub(in super::super) fn path(span: &Span, slots: impl IntoIterator<Item = i128>) -> Expr {
    slots
        .into_iter()
        .fold(empty(span, int_typ()), |path, slot| push(span, path, integer(span, slot)))
}

pub(in super::super) fn field(span: &Span, value: Expr, name: &str, typ: Typ) -> Expr {
    let TypX::Datatype(datatype, _, _) = &*value.typ else { unreachable!() };
    let variant = "Record";
    let op = FieldOpr {
        datatype: datatype.clone(),
        variant: Arc::new(variant.into()),
        field: Arc::new(name.into()),
        get_variant: false,
        check: VariantCheck::None,
    };
    SpannedTyped::new(span, &typ, ExprX::UnaryOpr(UnaryOpr::Field(op), value))
}

pub(in super::super) fn record_field(span: &Span, value: Expr, name: &str) -> Expr {
    field(span, value, name, int_typ())
}

pub(in super::super) fn cost(span: &Span, memory: Expr, kind: Expr) -> Expr {
    operation(span, "cost", vec![memory, kind], int_typ())
}

pub(in super::super) fn subtree(span: &Span, memory: Expr, path: Expr) -> Expr {
    operation(span, "subtree", vec![memory, path], memory_type())
}

pub(in super::super) fn without(span: &Span, memory: Expr, path: Expr) -> Expr {
    operation(span, "without", vec![memory, path], memory_type())
}

pub(in super::super) fn prefix(span: &Span, memory: Expr, path: Expr) -> Expr {
    operation(span, "prefix", vec![memory, path], memory_type())
}

pub(in super::super) fn lookup(span: &Span, memory: Expr, path: Expr) -> Expr {
    operation(span, "lookup", vec![memory, path], record_type())
}

/// Declare erased metadata at function scope; the owning operation schedules its snapshot.
pub(in super::super) fn local(
    span: &Span,
    stem: &str,
    typ: Typ,
    initial: Expr,
    mode: Mode,
) -> (Expr, Stmt) {
    let name = VarIdent(
        Arc::new(format!("$memory_{stem}")),
        VarIdentDisambiguate::VirTemp(super::super::accounting::Accounting::fresh_allocation()),
    );
    let value = SpannedTyped::new(span, &typ, ExprX::Var(name.clone()));
    let declaration = Spanned::new(
        span.clone(),
        StmtX::Decl {
            pattern: SpannedTyped::new(
                span,
                &typ,
                PatternX::Var(PatternBinding {
                    name,
                    by_ref: ByRef::No,
                    typ: typ.clone(),
                    user_mut: Some(true),
                    copy: false,
                    move_exec_to_proof_okay: MoveExecToProofOkay::No,
                }),
            ),
            mode: Some((mode, DeclProph::Default)),
            init: Some(SpannedTyped::new(span, &typ, PlaceX::Temporary(initial))),
            els: None,
            assert_irrefutable: false,
        },
    );
    (value, declaration)
}

pub(in super::super) fn assign(span: &Span, variable: &Expr, rhs: Expr) -> Stmt {
    let ExprX::Var(name) = &variable.x else { unreachable!() };
    Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &unit_typ(),
            ExprX::Assign {
                place: SpannedTyped::new(span, &variable.typ, PlaceX::Local(name.clone())),
                rhs,
                op: None,
                typ: variable.typ.clone(),
                resolve: false,
            },
        )),
    )
}
