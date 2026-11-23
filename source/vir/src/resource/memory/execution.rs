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
    pattern: &'a Pattern,
    init: Option<&Place>,
) -> Option<(&'a PatternBinding, &'a Typ)> {
    if let PatternX::Var(binding) = &pattern.x {
        return Some((binding, &binding.typ));
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
    Some((binding, &pattern.typ))
}
