//! Normalize finite forest descriptions before exporting or instantiating them.
//! These are structural algebra identities, not guesses about symbolic inputs.
//!
//! Shared-graph traversal and first-match dispatch live here. Inspection,
//! scalar rules, forest rules, collections, and proof-bound candidates have
//! separate modules; candidates are not normalization rules.

pub(super) mod bounds;
pub(super) mod collections;
mod forest;
pub(in crate::resource::memory) mod inspect;
mod scalar;

use crate::ast::*;
use std::collections::HashMap;
use std::sync::Arc;

/// Normalize a shared expression graph once per node. Branch composition reuses
/// entry forests; preserving that sharing avoids repeatedly expanding unchanged
/// subtrees and skips alternatives already decided by caller specialization.
pub(in super::super) fn simplify(value: &Expr) -> Expr {
    rewrite(value, None)
}

/// Substitute caller observations while normalizing the shared template graph.
pub(super) fn specialize(value: &Expr, values: &HashMap<VarIdent, Expr>) -> Expr {
    rewrite(value, Some(values))
}

fn rewrite(value: &Expr, values: Option<&HashMap<VarIdent, Expr>>) -> Expr {
    use crate::ast_visitor::{AstVisitor, NoScoper, Rewrite};
    // One normalization query retains its input graph while caching node identities.
    struct Normalize<'a> {
        /// Immutable caller observations replacing template symbols.
        values: Option<&'a HashMap<VarIdent, Expr>>,
        /// Normalized results keyed by nodes in the still-live input graph.
        cache: HashMap<usize, Expr>,
    }
    impl AstVisitor<Rewrite, VirErr, NoScoper> for Normalize<'_> {
        fn visit_expr(&mut self, value: &Expr) -> Result<Expr, VirErr> {
            let key = Arc::as_ptr(value) as usize;
            if let Some(value) = self.cache.get(&key) {
                return Ok(value.clone());
            }
            if let ExprX::Var(name) = &value.x {
                if let Some(replacement) = self.values.and_then(|values| values.get(name)) {
                    let result = simplify(replacement);
                    self.cache.insert(key, result.clone());
                    return Ok(result);
                }
            }
            if let ExprX::If(condition, yes, Some(no)) = &value.x {
                let condition = self.visit_expr(condition)?;
                if let ExprX::Const(Constant::Bool(selected)) = condition.x {
                    let result = self.visit_expr(if selected { yes } else { no })?;
                    self.cache.insert(key, result.clone());
                    return Ok(result);
                }
            }
            let result = node(&self.visit_expr_rec(value)?);
            self.cache.insert(key, result.clone());
            Ok(result)
        }
        fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
            Ok(typ.clone())
        }
        fn visit_place(&mut self, place: &Place) -> Result<Place, VirErr> {
            self.visit_place_rec(place)
        }
        fn visit_pattern(&mut self, pattern: &Pattern) -> Result<Pattern, VirErr> {
            self.visit_pattern_rec(pattern)
        }
        fn visit_stmt(&mut self, stmt: &Stmt) -> Result<Vec<Stmt>, VirErr> {
            Ok(vec![self.visit_stmt_rec(stmt)?])
        }
    }
    Normalize { values, cache: HashMap::new() }
        .visit_expr(value)
        .expect("infallible forest normalization")
}

/// Apply the first applicable rule in the established normalization order.
/// A rule can finish with an unchanged expression; only `None` tries the next rule.
fn node(value: &Expr) -> Expr {
    forest::empty_forest(value)
        .or_else(|| forest::branch_projection(value))
        .or_else(|| scalar::arithmetic(value))
        .or_else(|| collections::reverse_children(value))
        .or_else(|| scalar::record_field(value))
        .or_else(|| scalar::cost(value))
        .or_else(|| forest::ownership(value))
        .or_else(|| forest::remove_child(value))
        .or_else(|| collections::shift_children(value))
        .or_else(|| collections::finite_collections(value))
        .or_else(|| collections::take_children(value))
        .or_else(|| forest::select_path(value))
        .unwrap_or_else(|| scalar::fold_constants(value))
}
