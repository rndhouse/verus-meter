//! Execution boundaries shared by call discovery and memory accounting.

use crate::ast::*;
use std::collections::HashMap;

/// Identify proof-only expression regions that neither traversal should enter.
pub(super) fn ignored_expression(expr: &Expr) -> bool {
    matches!(
        &expr.x,
        ExprX::Ghost { .. }
            | ExprX::AssertAssume { .. }
            | ExprX::AssertBy { .. }
            | ExprX::AssertQuery { .. }
            | ExprX::AssertCompute(..)
            | ExprX::Fuel(..)
            | ExprX::RevealString(..)
            | ExprX::RevealByteString(..)
    )
}

/// Exclude explicit or inferred ghost declarations before evaluating initializers.
pub(super) fn ignored_statement(stmt: &Stmt, modes: &HashMap<VarIdent, Mode>) -> bool {
    if let StmtX::Decl { mode, pattern, .. } = &stmt.x {
        matches!(mode, Some((Mode::Spec | Mode::Proof, _)))
            || matches!(&pattern.x, PatternX::Var(binding) if matches!(modes.get(&binding.name),Some(Mode::Spec | Mode::Proof)))
    } else {
        false
    }
}

/// Resolve the named storage initialized by a by-value declaration.
/// The atomic constructor returns its location together with an erased linear
/// permission. Destructuring moves the sole executable storage into the first
/// binding. Both accounting traversals still evaluate the actual initializer.
pub(super) fn declaration_binding<'a>(
    layouts: &super::layout::Layouts,
    pattern: &'a Pattern,
    init: Option<&Place>,
) -> Option<(&'a PatternBinding, &'a Typ, Option<Place>)> {
    if let PatternX::Var(binding) = &pattern.x {
        return Some((binding, &binding.typ, init.cloned()));
    }
    if let Some(source) = init
        && matches!(source.x, PlaceX::Local(_))
        && let Some((binding, field)) = erased_record_binding(layouts, pattern)
    {
        let projection =
            SpannedTyped::new(&pattern.span, &binding.typ, PlaceX::Field(field, source.clone()));
        return Some((binding, &binding.typ, Some(projection)));
    }
    let PlaceX::Temporary(call) = &init?.x else { return None };
    let ExprX::Call { target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs), .. } =
        &call.x
    else {
        return None;
    };
    if attrs.resource_intrinsic
        != Some(ResourceIntrinsic::Atomic(super::synchronization::AtomicOperation::New))
    {
        return None;
    }
    let PatternX::Constructor(Dt::Tuple(2), _, fields) = &pattern.x else { return None };
    let field =
        |name: &str| fields.iter().find(|field| field.name.as_str() == name).map(|field| &field.a);
    let runtime = field("0")?;
    let permission = field("1")?;
    let PatternX::Var(binding) = &runtime.x else { return None };
    if !matches!(binding.by_ref, ByRef::No)
        || !matches!(&*permission.typ, TypX::Decorate(TypDecoration::Tracked, None, _))
        || !matches!(
            &permission.x,
            PatternX::Wildcard | PatternX::Var(PatternBinding { by_ref: ByRef::No, .. })
        )
    {
        return None;
    }
    Some((binding, &pattern.typ, init.cloned()))
}

/// Project the one copied reference out of a record of proof evidence. The
/// original record retains its inline slot. A borrowed binding to an erased
/// field would itself take executable storage, so it requires its own rule.
fn erased_record_binding<'a>(
    layouts: &super::layout::Layouts,
    pattern: &'a Pattern,
) -> Option<(&'a PatternBinding, FieldOpr)> {
    let PatternX::Constructor(datatype @ Dt::Path(_), variant, fields) = &pattern.x else {
        return None;
    };
    let declared = layouts.struct_variant(&pattern.typ, &pattern.span).ok()?;
    if declared.name != *variant
        || !fields.iter().all(|field| {
            matches!(
                &field.a.x,
                PatternX::Wildcard | PatternX::Var(PatternBinding { by_ref: ByRef::No, .. })
            )
        })
    {
        return None;
    }
    let mut runtime = declared.fields.iter().filter(|field| {
        field.a.1 == Mode::Exec
            && !matches!(
                &*field.a.0,
                TypX::Decorate(TypDecoration::Tracked | TypDecoration::Ghost, None, _)
            )
    });
    let field = runtime.next()?;
    if runtime.next().is_some()
        || !matches!(&*field.a.0, TypX::Decorate(TypDecoration::Ref, None, _))
    {
        return None;
    }
    let pat = fields.iter().find(|f| f.name == field.name)?;
    let PatternX::Var(binding) = &pat.a.x else { return None };
    if !binding.copy || !crate::ast_util::types_equal(&binding.typ, &field.a.0) {
        return None;
    }
    Some((
        binding,
        FieldOpr {
            datatype: datatype.clone(),
            variant: variant.clone(),
            field: field.name.clone(),
            get_variant: false,
            check: VariantCheck::None,
        },
    ))
}

/// Before VIR simplification a Ghost/Tracked constructor can still carry the
/// inner expression type. Its Rust destination is the matching erased wrapper.
pub(super) fn initializes(value: &Expr, destination: &Typ) -> bool {
    if crate::ast_util::types_equal(&value.typ, destination) {
        return true;
    }
    let ExprX::Ghost { alloc_wrapper: true, tracked, expr } = &value.x else { return false };
    let TypX::Decorate(mode, None, inner) = &**destination else { return false };
    matches!((tracked, mode), (true, TypDecoration::Tracked) | (false, TypDecoration::Ghost))
        && crate::ast_util::types_equal(&expr.typ, inner)
}
