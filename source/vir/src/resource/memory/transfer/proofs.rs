//! Explicit validity and cost facts for composed forest expressions.

use super::*;
use std::sync::Arc;

mod builders;
mod ranges;
mod scope;

use scope::ForestProofs;

#[cfg(test)]
mod tests;

/// Ordered loops retain reindexing inside abstract caller forests. Publish
/// inverse maps only for those completed outputs and only at requested indices.
pub(super) fn forest_views(
    span: &Span,
    value: &Expr,
    proofs: &mut Vec<Stmt>,
    ordered: bool,
) -> Result<(), VirErr> {
    let mut emitter = ForestProofs::new();
    emitter.forest(span, value, proofs)?;
    if ordered {
        use crate::ast_visitor::{VisitorControlFlow, expr_visitor_dfs};
        let mut visited = std::collections::HashSet::new();
        if let VisitorControlFlow::Stop(error) = expr_visitor_dfs::<VirErr, _>(
            value,
            &mut air::scope_map::ScopeMap::new(),
            &mut |scope, value| {
                if !scope.map().is_empty() || !visited.insert(Arc::as_ptr(value) as usize) {
                    return VisitorControlFlow::Return;
                }
                if let Some(args) = simplify::inspect::call(value, "remove_index") {
                    emitter.lemma(
                        span,
                        "remove_index_requested_views",
                        args.as_ref().clone(),
                        proofs,
                    );
                }
                VisitorControlFlow::Recurse
            },
        ) {
            return Err(error);
        }
    }
    Ok(())
}

/// Prove the forest expression's validity using the same algebra as local
/// operations. Conditional branches keep their own arithmetic assumptions.
pub(super) fn forest(span: &Span, value: &Expr, proofs: &mut Vec<Stmt>) -> Result<(), VirErr> {
    ForestProofs::new().forest(span, value, proofs)
}

impl ForestProofs {
    fn forest(&mut self, span: &Span, value: &Expr, proofs: &mut Vec<Stmt>) -> Result<(), VirErr> {
        if !self.visit(value) {
            return Ok(());
        }
        if let ExprX::If(condition, yes, Some(no)) = &value.x {
            self.forest(span, condition, proofs)?;
            let yes_proofs = self.branch(span, yes)?;
            let no_proofs = self.branch(span, no)?;
            let branch = SpannedTyped::new(
                span,
                &crate::ast_util::unit_typ(),
                ExprX::If(
                    condition.clone(),
                    crate::ast_util::mk_block(span, yes_proofs, None),
                    Some(crate::ast_util::mk_block(span, no_proofs, None)),
                ),
            );
            proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(branch)));
            return Ok(());
        }
        match &value.x {
            ExprX::Unary(_, value) | ExprX::UnaryOpr(_, value) => {
                self.forest(span, value, proofs)?
            }
            ExprX::Binary(_, left, right) => {
                self.forest(span, left, proofs)?;
                self.forest(span, right, proofs)?;
            }
            ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } => {
                for arg in args.iter() {
                    self.forest(span, arg, proofs)?;
                }
                let Some(Segment::V(name, _)) = function.path.segments.last() else {
                    return Ok(());
                };
                if expr::is_operation(function, name) {
                    let Some(Segment::V(name, _)) = function.path.segments.last() else {
                        return Ok(());
                    };
                    match name.as_str() {
                        "shift_children" => {
                            self.lemma(span, "shift_children_facts", args.as_ref().clone(), proofs)
                        }
                        "iterate" => {
                            builders::iterated(span, args, proofs, true, self)?;
                        }
                        "iterate_closed" => {
                            builders::closed_iteration(span, args, proofs, self)?;
                        }
                        "generate_children" => {
                            let args = builders::generated(span, args, proofs, self)?;
                            self.lemma(span, "generate_children_facts", args.clone(), proofs);
                            self.lemma(span, "generate_children_views", args, proofs);
                        }
                        "tile_children" => {
                            ranges::block(span, &args[0], &args[1], proofs, self)?;
                            self.lemma(span, "tile_children_facts", args.as_ref().clone(), proofs);
                            self.lemma(span, "tile_children_views", args.as_ref().clone(), proofs);
                        }
                        "repeat" => self.lemma(span, "repeat_facts", args.as_ref().clone(), proofs),
                        "take_children" => {
                            ranges::retention(span, &args[0], &args[1], proofs, self);
                            self.lemma(span, "take_children_facts", args.as_ref().clone(), proofs)
                        }
                        "reverse_children" => {
                            ranges::retention(span, &args[0], &args[1], proofs, self);
                            ranges::retention(span, &args[0], &args[2], proofs, self);
                            self.lemma(
                                span,
                                "reverse_children_facts",
                                args.as_ref().clone(),
                                proofs,
                            );
                            self.lemma(
                                span,
                                "reverse_children_views",
                                args.as_ref().clone(),
                                proofs,
                            );
                            self.lemma(
                                span,
                                "reverse_children_cost",
                                args.as_ref().clone(),
                                proofs,
                            );
                        }
                        "runtime" => {
                            self.lemma(
                                span,
                                "inspect",
                                vec![args[0].clone(), expr::path(span, [])],
                                proofs,
                            );
                            self.lemma(span, "runtime_class", args.as_ref().clone(), proofs);
                            self.lemma(
                                span,
                                "cost_runtime_partition",
                                vec![args[0].clone(), expr::integer(span, 0)],
                                proofs,
                            );
                        }
                        "allocated" => {
                            self.lemma(span, "well_formed_record", vec![value.clone()], proofs)
                        }
                        "prefix" => {
                            self.lemma(span, "runtime_prefix", args.as_ref().clone(), proofs);
                            self.lemma(span, "descendants_prefix", args.as_ref().clone(), proofs);
                            self.lemma(span, "well_formed_prefix", args.as_ref().clone(), proofs);
                            let mut args = args.as_ref().clone();
                            args.push(expr::integer(span, 0));
                            self.lemma(span, "cost_prefix", args, proofs);
                        }
                        "subtree" | "without" => {
                            if name.as_str() == "subtree" {
                                self.lemma(span, "request_path", args.as_ref().clone(), proofs);
                            }
                            if name.as_str() == "without" {
                                self.lemma(
                                    span,
                                    "runtime_without_facts",
                                    args.as_ref().clone(),
                                    proofs,
                                );
                                self.lemma(
                                    span,
                                    "partition_without",
                                    args.as_ref().clone(),
                                    proofs,
                                );
                                // Removing a child preserves its parent's descriptor.
                                // Nested pop templates need this root fact to bound
                                // the retained descendants plus the backing buffer.
                                self.lemma(
                                    span,
                                    "lookup_without",
                                    vec![args[0].clone(), args[1].clone(), expr::path(span, [])],
                                    proofs,
                                );
                            }
                            self.lemma(span, "inspect", args.as_ref().clone(), proofs);
                            let mut args = args.as_ref().clone();
                            args.push(expr::integer(span, 0));
                            self.lemma(span, "cost_partition", args, proofs);
                        }
                        "lookup" => {
                            // Composed calls can observe incoming geometry without
                            // an executable indexed loan to request its view first.
                            self.lemma(span, "request_path", args.as_ref().clone(), proofs);
                            if let Some(selected) = simplify::inspect::call(&args[0], "subtree") {
                                self.lemma(
                                    span,
                                    "lookup_subtree",
                                    vec![selected[0].clone(), selected[1].clone(), args[1].clone()],
                                    proofs,
                                );
                            }
                            self.lemma(span, "inspect", args.as_ref().clone(), proofs);
                        }
                        "remove_index" => {
                            self.lemma(span, "partition_remove", args.as_ref().clone(), proofs);
                            self.lemma(span, "remove_partition", args.as_ref().clone(), proofs);
                            self.lemma(span, "remove_root", args.as_ref().clone(), proofs);
                        }
                        "with_root" => {
                            self.lemma(span, "with_root_facts", args.as_ref().clone(), proofs)
                        }
                        "descendants" => {
                            self.lemma(span, "descendants_facts", args.as_ref().clone(), proofs)
                        }
                        "replace" => {
                            self.lemma(
                                span,
                                "inspect",
                                vec![args[0].clone(), args[1].clone()],
                                proofs,
                            );
                            self.lemma(
                                span,
                                "well_formed_prefix",
                                vec![args[2].clone(), args[1].clone()],
                                proofs,
                            );
                            self.lemma(
                                span,
                                "well_formed_add",
                                vec![
                                    expr::without(span, args[0].clone(), args[1].clone()),
                                    expr::prefix(span, args[2].clone(), args[1].clone()),
                                ],
                                proofs,
                            );
                        }
                        _ => {}
                    }
                } else if crate::ast_util::types_equal(&value.typ, &expr::memory_type()) {
                    let Some(Segment::V(name, _)) = function.path.segments.last() else {
                        return Ok(());
                    };
                    match name.as_str() {
                        "add" => {
                            self.lemma(span, "runtime_add", args.as_ref().clone(), proofs);
                            self.lemma(span, "descendants_add", args.as_ref().clone(), proofs);
                            self.lemma(span, "well_formed_add", args.as_ref().clone(), proofs);
                            let mut args = args.as_ref().clone();
                            args.push(expr::integer(span, 0));
                            self.lemma(span, "cost_add", args, proofs);
                        }
                        "push" => {
                            self.lemma(span, "runtime_push", args.as_ref().clone(), proofs);
                            self.lemma(span, "descendants_push", args.as_ref().clone(), proofs);
                            self.lemma(span, "well_formed_push", args.as_ref().clone(), proofs);
                            let mut args = args.as_ref().clone();
                            args.push(expr::integer(span, 0));
                            self.lemma(span, "cost_push", args, proofs);
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}
