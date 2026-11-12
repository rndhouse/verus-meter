//! Explicit validity and cost facts for composed forest expressions.

use super::*;
use std::sync::Arc;

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
                if let Some(args) = simplify::call(value, "remove_index") {
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

/// Facts established for shared expression nodes in this lexical proof scope.
/// Ancestor facts are available in a branch; branch-local facts cannot escape
/// to its sibling or parent. Quantified builder proofs start a fresh emitter.
struct ForestProofs {
    /// Retain each expression while its pointer identity is cached. Multiple
    /// roots may contain temporary nodes whose addresses would otherwise recycle.
    /// The root scope remains present until the emitter is discarded.
    scopes: Vec<Scope>,
}

/// Graph visits and pure lemma facts established under one set of assumptions.
#[derive(Default)]
struct Scope {
    /// Shared graph nodes already visited under these assumptions.
    nodes: HashMap<usize, Expr>,
    /// Pure lemma calls already established in this scope, grouped by callee.
    lemmas: HashMap<Fun, Vec<Exprs>>,
}

impl ForestProofs {
    fn new() -> Self {
        Self { scopes: vec![Scope::default()] }
    }

    fn branch(&mut self, span: &Span, value: &Expr) -> Result<Vec<Stmt>, VirErr> {
        self.scopes.push(Scope::default());
        let mut proofs = Vec::new();
        let result = self.forest(span, value, &mut proofs);
        self.scopes.pop();
        result?;
        Ok(proofs)
    }

    /// Generated metadata lemmas are pure: identical arguments establish the
    /// same facts again. Compare within this branch and its ancestors only.
    fn lemma(&mut self, span: &Span, name: &str, args: Vec<Expr>, proofs: &mut Vec<Stmt>) {
        let function = expr::function(name);
        if self.scopes.iter().any(|scope| {
            scope.lemmas.get(&function).is_some_and(|previous| {
                previous.iter().any(|old| {
                    old.len() == args.len()
                        && old.iter().zip(&args).all(|(a, b)| simplify::same_expression(a, b))
                })
            })
        }) {
            return;
        }
        self.scopes
            .last_mut()
            .unwrap()
            .lemmas
            .entry(function)
            .or_default()
            .push(Arc::new(args.clone()));
        proofs.push(expr::lemma(span, name, args));
    }

    fn forest(&mut self, span: &Span, value: &Expr, proofs: &mut Vec<Stmt>) -> Result<(), VirErr> {
        let key = Arc::as_ptr(value) as usize;
        if self.scopes.iter().any(|scope| scope.nodes.contains_key(&key)) {
            return Ok(());
        }
        self.scopes.last_mut().unwrap().nodes.insert(key, value.clone());
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
                            iterated(span, args, proofs, true, self)?;
                        }
                        "iterate_closed" => {
                            closed_iteration(span, args, proofs, self)?;
                        }
                        "generate_children" => {
                            let args = generated(span, args, proofs, self)?;
                            self.lemma(span, "generate_children_facts", args.clone(), proofs);
                            self.lemma(span, "generate_children_views", args, proofs);
                        }
                        "tile_children" => {
                            block(span, &args[0], &args[1], proofs, self)?;
                            self.lemma(span, "tile_children_facts", args.as_ref().clone(), proofs);
                            self.lemma(span, "tile_children_views", args.as_ref().clone(), proofs);
                        }
                        "repeat" => self.lemma(span, "repeat_facts", args.as_ref().clone(), proofs),
                        "take_children" => {
                            retention(span, &args[0], &args[1], proofs, self);
                            self.lemma(span, "take_children_facts", args.as_ref().clone(), proofs)
                        }
                        "reverse_children" => {
                            retention(span, &args[0], &args[1], proofs, self);
                            retention(span, &args[0], &args[2], proofs, self);
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
                            if let Some(selected) = simplify::call(&args[0], "subtree") {
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

/// Establish a block's logical index range structurally, independently of bytes.
fn block(
    span: &Span,
    value: &Expr,
    width: &Expr,
    proofs: &mut Vec<Stmt>,
    emitter: &mut ForestProofs,
) -> Result<(), VirErr> {
    let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } = &value.x else {
        return Err(super::super::model::unsupported(
            span,
            "an ownership block without a structural index range",
        ));
    };
    let Some(Segment::V(name, _)) = function.path.segments.last() else { unreachable!() };
    match name.as_str() {
        "empty" => {}
        "prefix" => {
            let path =
                simplify::path(&args[1]).filter(|path| path.len() == 1).ok_or_else(|| {
                    super::super::model::unsupported(
                        span,
                        "an ownership block without a single runtime index",
                    )
                })?;
            emitter.lemma(
                span,
                "block_bounds_prefix",
                vec![args[0].clone(), path[0].clone(), width.clone()],
                proofs,
            );
        }
        "add" => {
            block(span, &args[0], width, proofs, emitter)?;
            block(span, &args[1], width, proofs, emitter)?;
            emitter.lemma(
                span,
                "block_bounds_add",
                vec![args[0].clone(), args[1].clone(), width.clone()],
                proofs,
            );
        }
        "shift_children" => {
            let inner = super::super::contracts::subtract(span, width.clone(), args[1].clone());
            block(span, &args[0], &inner, proofs, emitter)?;
            emitter.lemma(
                span,
                "block_bounds_shift",
                vec![args[0].clone(), inner, args[1].clone()],
                proofs,
            );
        }
        "repeat" => emitter.lemma(
            span,
            "block_bounds_repeat",
            vec![args[0].clone(), args[1].clone(), args[2].clone(), width.clone()],
            proofs,
        ),
        "generate_children" => {
            let applied = generated(span, args, proofs, emitter)?;
            emitter.lemma(span, "block_bounds_generate", applied, proofs);
            let extent = super::super::contracts::add(
                span,
                args[3].clone(),
                super::super::contracts::multiply(span, args[1].clone(), args[2].clone()),
            );
            emitter.lemma(
                span,
                "block_bounds_weaken",
                vec![value.clone(), extent, width.clone()],
                proofs,
            );
        }
        "tile_children" => {
            block(span, &args[0], &args[1], proofs, emitter)?;
            emitter.lemma(span, "block_bounds_tile", args.as_ref().clone(), proofs);
            let extent = super::super::contracts::add(
                span,
                args[3].clone(),
                super::super::contracts::multiply(span, args[1].clone(), args[2].clone()),
            );
            emitter.lemma(
                span,
                "block_bounds_weaken",
                vec![value.clone(), extent, width.clone()],
                proofs,
            );
        }
        _ => return Err(super::super::model::unsupported(span, "this structural ownership block")),
    }
    Ok(())
}

/// Instantiate runtime-filter cuts at the range expressions that use them.
/// Keeping this law local avoids expanding unrelated counterexample terms.
fn retention(
    span: &Span,
    memory: &Expr,
    length: &Expr,
    proofs: &mut Vec<Stmt>,
    emitter: &mut ForestProofs,
) {
    let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } = &memory.x else {
        return;
    };
    if expr::is_operation(function, "runtime") {
        emitter.lemma(span, "take_children_runtime", vec![args[0].clone(), length.clone()], proofs);
    } else if *function == crate::fun!(CrateId::Vstd => "seq", "Seq"; "add") {
        retention(span, &args[0], length, proofs, emitter);
        retention(span, &args[1], length, proofs, emitter);
    }
}

/// Prove a builder for an arbitrary in-range iteration. Its bound variable is
/// local to this proof and to the exported specification closure.
fn generated(
    span: &Span,
    args: &Exprs,
    proofs: &mut Vec<Stmt>,
    emitter: &mut ForestProofs,
) -> Result<Vec<Expr>, VirErr> {
    let ExprX::Closure(binders, body) = &args[0].x else {
        return Err(super::super::model::unsupported(
            span,
            "a generated ownership block without its checked builder",
        ));
    };
    let (builder, declaration) =
        expr::local(span, "iteration_builder", args[0].typ.clone(), args[0].clone(), Mode::Spec);
    proofs.push(declaration);
    let index =
        SpannedTyped::new(span, &crate::ast_util::int_typ(), ExprX::Var(binders[0].name.clone()));
    let range = crate::ast_util::conjoin(
        span,
        &vec![
            crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &index, InequalityOp::Le),
            crate::ast_util::mk_ineq(span, &index, &args[2], InequalityOp::Lt),
        ],
    );
    let applied = SpannedTyped::new(
        span,
        &expr::memory_type(),
        ExprX::Call {
            target: CallTarget::FnSpec(builder.clone()),
            args: Arc::new(vec![index.clone()]),
            post_args: None,
            body: None,
        },
    );
    let affine = simplify::affine(
        &simplify::simplify(&expr::cost(span, body.clone(), expr::integer(span, 0))),
        &binders[0].name,
    );
    let mut facts = vec![
        expr::operation(span, "well_formed", vec![applied.clone()], crate::ast_util::bool_typ()),
        crate::ast_util::mk_eq(
            span,
            &expr::operation(span, "runtime", vec![applied.clone()], expr::memory_type()),
            &applied,
        ),
        expr::operation(
            span,
            "block_bounds",
            vec![applied.clone(), args[1].clone()],
            crate::ast_util::bool_typ(),
        ),
    ];
    if let Some((slope, intercept)) = &affine {
        let expected = super::super::contracts::add(
            span,
            super::super::contracts::multiply(span, slope.clone(), index),
            intercept.clone(),
        );
        facts.push(crate::ast_util::mk_eq(
            span,
            &expr::cost(span, applied.clone(), expr::integer(span, 0)),
            &expected,
        ));
    }
    let ensure = crate::ast_util::conjoin(span, &facts);
    let ensure = SpannedTyped::new(
        span,
        &crate::ast_util::bool_typ(),
        ExprX::WithTriggers { triggers: Arc::new(vec![Arc::new(vec![applied])]), body: ensure },
    );
    let mut body_proofs = Vec::new();
    let mut body_emitter = ForestProofs::new();
    body_emitter.forest(span, body, &mut body_proofs)?;
    block(span, body, &args[1], &mut body_proofs, &mut body_emitter)?;
    let proof = SpannedTyped::new(
        span,
        &crate::ast_util::unit_typ(),
        ExprX::AssertBy {
            vars: binders.clone(),
            require: range,
            ensure,
            proof: crate::ast_util::mk_block(span, body_proofs, None),
        },
    );
    proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(proof)));
    if let Some((slope, intercept)) = affine {
        emitter.lemma(
            span,
            "generated_cost_affine",
            vec![builder.clone(), args[2].clone(), slope, intercept],
            proofs,
        );
    } else {
        let fuel = SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::Fuel(
                crate::fun!(CrateId::Vstd => "std_specs", "memory"; "generated_cost"),
                simplify::FINITE_GENERATION_LIMIT + 1,
                false,
            ),
        );
        proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(fuel)));
    }
    let mut args = args.as_ref().clone();
    args[0] = builder;
    Ok(args)
}

/// Check one ordered recurrence step under the same validity assumption that
/// the verified iterator establishes for every preceding accumulator.
fn iterated(
    span: &Span,
    args: &Exprs,
    proofs: &mut Vec<Stmt>,
    unfold: bool,
    emitter: &mut ForestProofs,
) -> Result<(), VirErr> {
    let ExprX::Closure(binders, body) = &args[0].x else {
        return Err(super::super::model::unsupported(
            span,
            "an ownership recurrence without its checked transition",
        ));
    };
    let (builder, declaration) =
        expr::local(span, "iteration_step", args[0].typ.clone(), args[0].clone(), Mode::Spec);
    proofs.push(declaration);
    let index =
        SpannedTyped::new(span, &crate::ast_util::int_typ(), ExprX::Var(binders[0].name.clone()));
    let state = SpannedTyped::new(span, &expr::memory_type(), ExprX::Var(binders[1].name.clone()));
    let require = crate::ast_util::conjoin(
        span,
        &vec![
            crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &index, InequalityOp::Le),
            crate::ast_util::mk_ineq(span, &index, &args[2], InequalityOp::Lt),
            expr::operation(span, "well_formed", vec![state.clone()], crate::ast_util::bool_typ()),
        ],
    );
    let applied = SpannedTyped::new(
        span,
        &expr::memory_type(),
        ExprX::Call {
            target: CallTarget::FnSpec(builder.clone()),
            args: Arc::new(vec![index, state]),
            post_args: None,
            body: None,
        },
    );
    let ensure =
        expr::operation(span, "well_formed", vec![applied.clone()], crate::ast_util::bool_typ());
    let ensure = SpannedTyped::new(
        span,
        &crate::ast_util::bool_typ(),
        ExprX::WithTriggers { triggers: Arc::new(vec![Arc::new(vec![applied])]), body: ensure },
    );
    let mut body_proofs = Vec::new();
    forest(span, body, &mut body_proofs)?;
    let proof = SpannedTyped::new(
        span,
        &crate::ast_util::unit_typ(),
        ExprX::AssertBy {
            vars: binders.clone(),
            require,
            ensure,
            proof: crate::ast_util::mk_block(span, body_proofs, None),
        },
    );
    proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(proof)));
    emitter.lemma(span, "iterate_facts", vec![builder, args[1].clone(), args[2].clone()], proofs);
    if unfold {
        let fuel = SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::Fuel(
                crate::fun!(CrateId::Vstd => "std_specs", "memory"; "iterate"),
                simplify::FINITE_GENERATION_LIMIT + 1,
                false,
            ),
        );
        proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(fuel)));
    }
    Ok(())
}

/// Check the candidate's successor equation at an arbitrary visit before using
/// the generic closed-form induction. Forest equality retains every descriptor.
fn closed_iteration(
    span: &Span,
    args: &Exprs,
    proofs: &mut Vec<Stmt>,
    emitter: &mut ForestProofs,
) -> Result<(), VirErr> {
    iterated(span, args, proofs, false, emitter)?;
    let ExprX::Closure(step_binders, step_body) = &args[0].x else { unreachable!() };
    let ExprX::Closure(binders, closed_body) = &args[3].x else { unreachable!() };
    let index =
        SpannedTyped::new(span, &crate::ast_util::int_typ(), ExprX::Var(binders[0].name.clone()));
    let successor =
        crate::resource::memory::contracts::add(span, index.clone(), expr::integer(span, 1));
    let (closed, declaration) =
        expr::local(span, "closed_forest", args[3].typ.clone(), args[3].clone(), Mode::Spec);
    proofs.push(declaration);
    let (step, declaration) =
        expr::local(span, "closed_step", args[0].typ.clone(), args[0].clone(), Mode::Spec);
    proofs.push(declaration);
    let current = SpannedTyped::new(
        span,
        &expr::memory_type(),
        ExprX::Call {
            target: CallTarget::FnSpec(closed.clone()),
            args: Arc::new(vec![index.clone()]),
            post_args: None,
            body: None,
        },
    );
    let stepped = SpannedTyped::new(
        span,
        &expr::memory_type(),
        ExprX::Call {
            target: CallTarget::FnSpec(step.clone()),
            args: Arc::new(vec![index.clone(), current]),
            post_args: None,
            body: None,
        },
    );
    let requested = SpannedTyped::new(
        span,
        &expr::memory_type(),
        ExprX::Call {
            target: CallTarget::FnSpec(closed.clone()),
            args: Arc::new(vec![successor.clone()]),
            post_args: None,
            body: None,
        },
    );

    let next = substitute(closed_body, &HashMap::from([(binders[0].name.clone(), successor)]));
    let applied = substitute(
        step_body,
        &HashMap::from([
            (step_binders[0].name.clone(), index.clone()),
            (step_binders[1].name.clone(), closed_body.clone()),
        ]),
    );
    let raw = |value: &Expr, values: &HashMap<VarIdent, Expr>| {
        crate::ast_visitor::map_expr_visitor_env(
            value,
            &mut air::scope_map::ScopeMap::new(),
            &mut (),
            &|_, scope, value| {
                Ok::<_, VirErr>(if let ExprX::Var(name) = &value.x {
                    if !scope.contains_key(name) {
                        values.get(name).cloned().unwrap_or_else(|| value.clone())
                    } else {
                        value.clone()
                    }
                } else {
                    value.clone()
                })
            },
            &|_, _, stmt| Ok(vec![stmt.clone()]),
            &|_, typ| Ok(typ.clone()),
            &|_, _, place| Ok(place.clone()),
            &|_, _, pattern| Ok(pattern.clone()),
        )
    };
    let raw_next = raw(
        closed_body,
        &HashMap::from([(
            binders[0].name.clone(),
            crate::resource::memory::contracts::add(span, index.clone(), expr::integer(span, 1)),
        )]),
    )?;
    let raw_applied = raw(
        step_body,
        &HashMap::from([
            (step_binders[0].name.clone(), index.clone()),
            (step_binders[1].name.clone(), closed_body.clone()),
        ]),
    )?;
    let mut facts = Vec::new();
    // The induction ranges over arbitrary visit counts. Its finite descriptor
    // constructors still need their structural definitions at the successor
    // equation; keep this unfolding inside the equation proof, away from
    // caller budget queries and the opaque iteration operator.
    let mut records = 0u32;
    crate::ast_visitor::expr_visitor_check(closed_body, &mut |_, value| {
        if simplify::call(value, "allocated").is_some() {
            records = records.saturating_add(1);
        }
        Ok::<(), VirErr>(())
    })?;
    for operation in ["prefix", "subtree", "without"] {
        facts.push(crate::def::Spanned::new(
            span.clone(),
            StmtX::Expr(SpannedTyped::new(
                span,
                &crate::ast_util::unit_typ(),
                ExprX::Fuel(expr::function(operation), records.saturating_add(2), false),
            )),
        ));
    }
    let mut forest_proofs = ForestProofs::new();
    for value in [&raw_next, &raw_applied, &applied, &next] {
        forest_proofs.forest(span, value, &mut facts)?;
    }
    let proof = SpannedTyped::new(
        span,
        &crate::ast_util::unit_typ(),
        ExprX::AssertBy {
            vars: binders.clone(),
            require: crate::ast_util::conjoin(
                span,
                &vec![
                    crate::ast_util::mk_ineq(
                        span,
                        &expr::integer(span, 0),
                        &index,
                        InequalityOp::Le,
                    ),
                    crate::ast_util::mk_ineq(span, &index, &args[2], InequalityOp::Lt),
                ],
            ),
            ensure: SpannedTyped::new(
                span,
                &crate::ast_util::bool_typ(),
                ExprX::WithTriggers {
                    triggers: Arc::new(vec![Arc::new(vec![stepped.clone()])]),
                    body: crate::ast_util::mk_eq(span, &requested, &stepped),
                },
            ),
            proof: crate::ast_util::mk_block(span, facts, None),
        },
    );
    proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(proof)));
    let mut arguments = args.as_ref().clone();
    arguments[0] = step;
    arguments[3] = closed;
    emitter.lemma(span, "iterate_closed_facts", arguments, proofs);
    Ok(())
}
