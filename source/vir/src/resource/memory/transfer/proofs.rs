//! Explicit validity and cost facts for composed forest expressions.

use super::*;

/// Prove the forest expression's validity using the same algebra as local
/// operations. Conditional branches keep their own arithmetic assumptions.
pub(super) fn forest(span: &Span, value: &Expr, proofs: &mut Vec<Stmt>) -> Result<(), VirErr> {
    if let ExprX::If(condition, yes, Some(no)) = &value.x {
        forest(span, condition, proofs)?;
        let mut yes_proofs = Vec::new();
        let mut no_proofs = Vec::new();
        forest(span, yes, &mut yes_proofs)?;
        forest(span, no, &mut no_proofs)?;
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
        ExprX::Unary(_, value) | ExprX::UnaryOpr(_, value) => forest(span, value, proofs)?,
        ExprX::Binary(_, left, right) => {
            forest(span, left, proofs)?;
            forest(span, right, proofs)?;
        }
        ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } => {
            for arg in args.iter() {
                forest(span, arg, proofs)?;
            }
            let Some(Segment::V(name, _)) = function.path.segments.last() else {
                return Ok(());
            };
            if expr::is_operation(function, name) {
                let Some(Segment::V(name, _)) = function.path.segments.last() else {
                    return Ok(());
                };
                match name.as_str() {
                    "repeat" => {
                        proofs.push(expr::lemma(span, "repeat_facts", args.as_ref().clone()))
                    }
                    "take_children" => {
                        proofs.push(expr::lemma(span, "take_children_facts", args.as_ref().clone()))
                    }
                    "runtime" => {
                        proofs.push(expr::lemma(
                            span,
                            "inspect",
                            vec![args[0].clone(), expr::path(span, [])],
                        ));
                        proofs.push(expr::lemma(span, "runtime_class", args.as_ref().clone()));
                        proofs.push(expr::lemma(
                            span,
                            "cost_runtime_partition",
                            vec![args[0].clone(), expr::integer(span, 0)],
                        ));
                    }
                    "allocated" => {
                        proofs.push(expr::lemma(span, "well_formed_record", vec![value.clone()]))
                    }
                    "prefix" => {
                        proofs.push(expr::lemma(span, "runtime_prefix", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "descendants_prefix", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "well_formed_prefix", args.as_ref().clone()));
                        let mut args = args.as_ref().clone();
                        args.push(expr::integer(span, 0));
                        proofs.push(expr::lemma(span, "cost_prefix", args));
                    }
                    "subtree" | "without" => {
                        if name.as_str() == "without" {
                            proofs.push(expr::lemma(
                                span,
                                "partition_without",
                                args.as_ref().clone(),
                            ));
                            // Removing a child preserves its parent's descriptor.
                            // Nested pop templates need this root fact to bound
                            // the retained descendants plus the backing buffer.
                            proofs.push(expr::lemma(
                                span,
                                "lookup_without",
                                vec![args[0].clone(), args[1].clone(), expr::path(span, [])],
                            ));
                        }
                        proofs.push(expr::lemma(span, "inspect", args.as_ref().clone()));
                        let mut args = args.as_ref().clone();
                        args.push(expr::integer(span, 0));
                        proofs.push(expr::lemma(span, "cost_partition", args));
                    }
                    "lookup" => proofs.push(expr::lemma(span, "inspect", args.as_ref().clone())),
                    "remove_index" => {
                        proofs.push(expr::lemma(span, "partition_remove", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "remove_partition", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "remove_root", args.as_ref().clone()));
                    }
                    "with_root" => {
                        proofs.push(expr::lemma(span, "with_root_facts", args.as_ref().clone()))
                    }
                    "descendants" => {
                        proofs.push(expr::lemma(span, "descendants_facts", args.as_ref().clone()))
                    }
                    "replace" => {
                        proofs.push(expr::lemma(
                            span,
                            "inspect",
                            vec![args[0].clone(), args[1].clone()],
                        ));
                        proofs.push(expr::lemma(
                            span,
                            "well_formed_prefix",
                            vec![args[2].clone(), args[1].clone()],
                        ));
                        proofs.push(expr::lemma(
                            span,
                            "well_formed_add",
                            vec![
                                expr::without(span, args[0].clone(), args[1].clone()),
                                expr::prefix(span, args[2].clone(), args[1].clone()),
                            ],
                        ));
                    }
                    _ => {}
                }
            } else if crate::ast_util::types_equal(&value.typ, &expr::memory_type()) {
                let Some(Segment::V(name, _)) = function.path.segments.last() else {
                    return Ok(());
                };
                match name.as_str() {
                    "add" => {
                        proofs.push(expr::lemma(span, "runtime_add", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "descendants_add", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "well_formed_add", args.as_ref().clone()));
                        let mut args = args.as_ref().clone();
                        args.push(expr::integer(span, 0));
                        proofs.push(expr::lemma(span, "cost_add", args));
                    }
                    "push" => {
                        proofs.push(expr::lemma(span, "runtime_push", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "descendants_push", args.as_ref().clone()));
                        proofs.push(expr::lemma(span, "well_formed_push", args.as_ref().clone()));
                        let mut args = args.as_ref().clone();
                        args.push(expr::integer(span, 0));
                        proofs.push(expr::lemma(span, "cost_push", args));
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
    Ok(())
}
