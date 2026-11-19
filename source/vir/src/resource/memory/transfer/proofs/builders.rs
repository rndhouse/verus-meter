//! Checked builders, recurrence steps, and closed-form ownership induction.
//!
//! Quantified bodies establish facts in fresh emitters under their own
//! requirements; those local facts must not enter the caller's caches.

use super::super::{expr, simplify, substitute};
use super::{forest, ranges::block, scope::ForestProofs};
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{contracts, model};
use std::collections::HashMap;
use std::sync::Arc;

/// Prove a builder for an arbitrary in-range iteration. Its bound variable is
/// local to this proof and to the exported specification closure.
pub(super) fn generated(
    span: &Span,
    args: &Exprs,
    proofs: &mut Vec<Stmt>,
    emitter: &mut ForestProofs,
) -> Result<Vec<Expr>, VirErr> {
    let ExprX::Closure(binders, body) = &args[0].x else {
        return Err(model::unsupported(
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
    let affine = simplify::bounds::affine(
        &simplify::simplify(&expr::cost(span, body.clone(), expr::integer(span, 0))),
        &binders[0].name,
    );
    let mut facts = vec![
        (
            expr::operation(
                span,
                "well_formed",
                vec![applied.clone()],
                crate::ast_util::bool_typ(),
            ),
            "cannot prove generated collection block validity",
        ),
        (
            crate::ast_util::mk_eq(
                span,
                &expr::operation(span, "runtime", vec![applied.clone()], expr::memory_type()),
                &applied,
            ),
            "cannot prove generated collection block runtime paths",
        ),
        (
            expr::operation(
                span,
                "block_bounds",
                vec![applied.clone(), args[1].clone()],
                crate::ast_util::bool_typ(),
            ),
            "cannot prove generated collection block index range",
        ),
    ];
    if let Some((slope, intercept)) = &affine {
        let expected = contracts::add(
            span,
            contracts::multiply(span, slope.clone(), index),
            intercept.clone(),
        );
        facts.push((
            crate::ast_util::mk_eq(
                span,
                &expr::cost(span, applied.clone(), expr::integer(span, 0)),
                &expected,
            ),
            "cannot prove generated collection block byte charge",
        ));
    }
    let mut body_proofs = Vec::new();
    let mut body_emitter = ForestProofs::new();
    body_emitter.forest(span, body, &mut body_proofs)?;
    block(span, body, &args[1], &mut body_proofs, &mut body_emitter)?;
    let mut descriptions = Vec::new();
    worker_descriptions(span, body, crate::ast_util::mk_bool(span, true), &mut descriptions);
    for result in descriptions {
        // Validate the checked body's description at its construction, under
        // this occurrence's range. Collection operations merely preserve it.
        body_emitter.forest(span, &result, &mut body_proofs)?;
        facts.push((
            expr::operation(span, "well_formed", vec![result.clone()], crate::ast_util::bool_typ()),
            "cannot prove generated worker result validity",
        ));
        let cost = expr::cost(span, result, expr::integer(span, 0));
        facts.push((
            crate::ast_util::mk_eq(span, &cost, &simplify::simplify(&cost)),
            "cannot prove generated worker result byte charge",
        ));
    }
    for (fact, label) in &facts {
        body_proofs.push(expr::check(span, fact.clone(), label));
    }
    let ensure = SpannedTyped::new(
        span,
        &crate::ast_util::bool_typ(),
        ExprX::WithTriggers {
            triggers: Arc::new(vec![Arc::new(vec![applied])]),
            body: crate::ast_util::conjoin(
                span,
                &facts.into_iter().map(|(fact, _)| fact).collect(),
            ),
        },
    );
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
                expr::function("generated_cost"),
                simplify::collections::FINITE_GENERATION_LIMIT + 1,
                false,
            ),
        );
        proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(fuel)));
    }
    let mut args = args.as_ref().clone();
    args[0] = builder;
    Ok(args)
}

/// Conditional publications validate only the description selected on that
/// branch. Captured metadata is immutable data, not another collection to walk.
pub(super) fn worker_descriptions(span: &Span, value: &Expr, guard: Expr, output: &mut Vec<Expr>) {
    if let Some(args) = simplify::inspect::call(value, "worker_observation") {
        // A carried job's publication occupies the root of the input view.
        // Its result needs the same per-visit validity proof when it is joined.
        if let Some(inputs) = simplify::inspect::call(&args[2], "push")
            && simplify::inspect::call(&inputs[1], "worker_observation").is_some()
        {
            worker_descriptions(span, &inputs[1], guard.clone(), output);
        }
        output.push(simplify::simplify(&super::super::choice(
            span,
            guard,
            args[3].clone(),
            expr::empty(span, expr::record_type()),
        )));
        return;
    }
    match &value.x {
        ExprX::Call { args, .. } => {
            for arg in args.iter() {
                worker_descriptions(span, arg, guard.clone(), output);
            }
        }
        ExprX::If(condition, yes, Some(no)) => {
            worker_descriptions(
                span,
                yes,
                crate::ast_util::conjoin(span, &vec![guard.clone(), condition.clone()]),
                output,
            );
            let opposite = SpannedTyped::new(
                span,
                &crate::ast_util::bool_typ(),
                ExprX::Unary(UnaryOp::Not, condition.clone()),
            );
            worker_descriptions(
                span,
                no,
                crate::ast_util::conjoin(span, &vec![guard, opposite]),
                output,
            );
        }
        _ => {}
    }
}

/// Check one ordered recurrence step under the same validity assumption that
/// the verified iterator establishes for every preceding accumulator.
pub(super) fn iterated(
    span: &Span,
    args: &Exprs,
    proofs: &mut Vec<Stmt>,
    unfold: bool,
    emitter: &mut ForestProofs,
) -> Result<(), VirErr> {
    let ExprX::Closure(binders, body) = &args[0].x else {
        return Err(model::unsupported(
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
                expr::function("iterate"),
                simplify::collections::FINITE_GENERATION_LIMIT + 1,
                false,
            ),
        );
        proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(fuel)));
    }
    Ok(())
}

/// Check the candidate's successor equation at an arbitrary visit before using
/// the generic closed-form induction. Forest equality retains every descriptor.
pub(super) fn closed_iteration(
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
    let successor = contracts::add(span, index.clone(), expr::integer(span, 1));
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
            contracts::add(span, index.clone(), expr::integer(span, 1)),
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
        if simplify::inspect::call(value, "allocated").is_some() {
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
