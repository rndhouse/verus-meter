//! Execution boundaries shared by call discovery and memory accounting.

use crate::ast::*;
use std::collections::HashMap;

pub(super) fn ignored_expression(expr: &Expr) -> bool {
    matches!(
        &expr.x,
        ExprX::Ghost { alloc_wrapper: false, .. }
            | ExprX::AssertAssume { .. }
            | ExprX::AssertBy { .. }
            | ExprX::AssertQuery { .. }
            | ExprX::AssertCompute(..)
            | ExprX::Fuel(..)
            | ExprX::RevealString(..)
            | ExprX::RevealByteString(..)
    )
}

pub(super) fn ignored_statement(stmt: &Stmt, modes: &HashMap<VarIdent, Mode>) -> bool {
    if let StmtX::Decl { mode, pattern, .. } = &stmt.x {
        matches!(mode, Some((Mode::Spec | Mode::Proof, _)))
            || matches!(&pattern.x, PatternX::Var(binding) if matches!(modes.get(&binding.name),Some(Mode::Spec | Mode::Proof)))
    } else {
        false
    }
}
