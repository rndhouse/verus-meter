//! Conditional contracts become ordinary Verus obligations at reservation sites.
//!
//! Costs still come exclusively from the structural model. Immutable scalar
//! inputs give the budget a stable entry-state meaning without a ghost counter.

use super::accounting::StorageReport;
use super::layout::Layouts;
use crate::ast::*;
use crate::ast_util::*;
use crate::def::Spanned;
use crate::messages::{Span, error};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub(super) fn function_bound(
    function: &Function,
    budgets: &HashMap<Fun, u64>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
) -> Result<Option<Expr>, VirErr> {
    let bound = super::contracts::function_bound(function, budgets, functions, layouts)?;
    let declared_conditional = match &function.x.attrs.resource_contract {
        Some(super::model::ResourceContract::LexicalSlotsV5Expr { budget }) => {
            super::budget::is_conditional(budget)
        }
        _ => false,
    };
    Ok(if !declared_conditional && super::contracts::constant(&bound).is_some() {
        None
    } else {
        Some(bound)
    })
}

fn obligation(span: &Span, cost: &Expr, bound: &Expr) -> Stmt {
    let assertion = SpannedTyped::new(span, &unit_typ(), ExprX::AssertAssume {
        is_assume: false,
        expr: mk_ineq(span, cost, bound, InequalityOp::Le),
        msg: Some(error(span, "conditional memory budget exceeded: cannot prove the required model bytes fit the declared bound").secondary_span(&bound.span)),
    });
    Spanned::new(span.clone(), StmtX::Expr(assertion))
}

// Formula arithmetic is mathematical, but every evaluated sum/product must
// still fit the model's u64 range. Conditional arms retain their own guards.
fn range_checks(expr: &Expr, guard: &Expr, checks: &mut Vec<Stmt>) {
    let span = &expr.span;
    match &expr.x {
        ExprX::If(condition, yes, Some(no)) => {
            let and = |b: Expr| {
                SpannedTyped::new(
                    span,
                    &Arc::new(TypX::Bool),
                    ExprX::Logical(LogicalOp::And, guard.clone(), b),
                )
            };
            range_checks(yes, &and(condition.clone()), checks);
            let not = SpannedTyped::new(
                span,
                &Arc::new(TypX::Bool),
                ExprX::Unary(UnaryOp::Not, condition.clone()),
            );
            range_checks(no, &and(not), checks);
        }
        ExprX::Binary(BinaryOp::Arith(_), a, b) => {
            range_checks(a, guard, checks);
            range_checks(b, guard, checks);
            let fits =
                mk_ineq(span, expr, &super::contracts::literal(span, u64::MAX), InequalityOp::Le);
            let assertion = SpannedTyped::new(
                span,
                &unit_typ(),
                ExprX::AssertAssume {
                    is_assume: false,
                    expr: mk_implies(span, guard, &fits),
                    msg: Some(error(
                        span,
                        "memory budget arithmetic exceeds u64: cannot prove this expression fits",
                    )),
                },
            );
            checks.push(Spanned::new(span.clone(), StmtX::Expr(assertion)));
        }
        _ => {}
    }
}

pub(super) fn instrument(
    function: &Function,
    bound: Option<&Expr>,
    obligations: &[(Span, Expr, Expr)],
    checks: &[(Span, Expr)],
    report: &StorageReport,
    layouts: &Layouts,
    fresh_span: &dyn Fn(&Span) -> Span,
) -> Result<Function, VirErr> {
    // Inserted proofs must have fresh AST identities. Reusing an executable
    // allocation's identity confuses resolution inference for owned values.
    let mut sites: HashMap<u64, (Span, u64)> = HashMap::new();
    let parameter_spans: HashSet<_> = function.x.params.iter().map(|p| p.span.id).collect();
    for (span, bytes) in report.reservations.iter().filter(|_| bound.is_some()) {
        if parameter_spans.contains(&span.id) {
            continue;
        }
        let site = sites.entry(span.id).or_insert((span.clone(), 0));
        site.1 = site.1.max(*bytes);
    }
    let mut sites: HashMap<u64, (Span, Vec<Stmt>)> = sites
        .into_iter()
        .map(|(id, (span, bytes))| {
            let check = obligation(&span, &super::contracts::literal(&span, bytes), bound.unwrap());
            (id, (span, vec![check]))
        })
        .collect();
    for (span, cost, bound) in obligations {
        sites
            .entry(span.id)
            .or_insert_with(|| (span.clone(), Vec::new()))
            .1
            .push(obligation(span, cost, bound));
    }
    for (span, condition) in checks {
        let check = SpannedTyped::new(
            span,
            &unit_typ(),
            ExprX::AssertAssume {
                is_assume: false,
                expr: condition.clone(),
                msg: Some(error(
                    span,
                    "vector capacity exceeded: cannot prove this push fits the reserved capacity",
                )),
            },
        );
        sites
            .entry(span.id)
            .or_insert_with(|| (span.clone(), Vec::new()))
            .1
            .push(Spanned::new(span.clone(), StmtX::Expr(check)));
    }
    let body = function.x.body.as_ref().unwrap();
    let mut seen = HashSet::new();
    let body = crate::ast_visitor::map_expr_visitor_env(
        body,
        &mut air::scope_map::ScopeMap::new(),
        &mut seen,
        &|seen, _, expr| {
            // Resolution inference expects a two-phase borrow to remain a direct
            // call argument. Its parameter reservation is checked at the call;
            // the immutable-input bound has the same value at both locations.
            if matches!(expr.x, ExprX::TwoPhaseBorrowMut(_)) {
                return Ok(expr.clone());
            }
            let mut checks = Vec::new();
            if let ExprX::Call { args, .. } = &expr.x {
                for arg in args.iter().filter(|arg| matches!(arg.x, ExprX::TwoPhaseBorrowMut(_))) {
                    if let Some((_, statements)) = sites.get(&arg.span.id) {
                        seen.insert(arg.span.id);
                        checks.extend(statements.iter().cloned());
                    }
                }
            }
            if let Some((_, statements)) = sites.get(&expr.span.id) {
                seen.insert(expr.span.id);
                checks.extend(statements.iter().cloned());
            }
            if !checks.is_empty() {
                let checks = checks
                    .iter()
                    .map(|s| crate::ast_visitor::map_stmt_spans(s, &mut |span| fresh_span(span)))
                    .collect();
                Ok(mk_block(&fresh_span(&expr.span), checks, Some(expr.clone())))
            } else {
                Ok(expr.clone())
            }
        },
        &|seen, _, stmt| {
            if let StmtX::Decl { .. } = &stmt.x
                && let Some((_, statements)) = sites.get(&stmt.span.id)
            {
                seen.insert(stmt.span.id);
                Ok(statements
                    .iter()
                    .map(|s| crate::ast_visitor::map_stmt_spans(s, &mut |span| fresh_span(span)))
                    .chain(std::iter::once(stmt.clone()))
                    .collect())
            } else {
                Ok(vec![stmt.clone()])
            }
        },
        &|_, typ| Ok(typ.clone()),
        &|_, _, place| Ok(place.clone()),
        &|_, _, pattern| Ok(pattern.clone()),
    )?;
    // Never silently omit a charge if a future lowering introduces a new kind
    // of reservation site that this instrumentation does not recognize.
    for (id, (span, _)) in &sites {
        if !seen.contains(id) {
            return Err(error(span, "unsupported conditional memory reservation site"));
        }
    }
    let mut parameters = 0u64;
    for p in function.x.params.iter().filter(|p| p.x.mode == Mode::Exec) {
        parameters = parameters
            .checked_add(layouts.size(&p.x.typ, &p.span)?)
            .ok_or_else(|| error(&p.span, "parameter storage exceeds u64"))?;
    }
    let body = if let Some(bound) = bound {
        let check = obligation(
            &function.span,
            &super::contracts::literal(&function.span, parameters),
            bound,
        );
        let mut checks = vec![check];
        if super::contracts::numeric_input(bound) {
            range_checks(bound, &mk_bool(&function.span, true), &mut checks);
        }
        let checks = checks
            .iter()
            .map(|check| crate::ast_visitor::map_stmt_spans(check, &mut |span| fresh_span(span)))
            .collect();
        mk_block(&fresh_span(&body.span), checks, Some(body.clone()))
    } else {
        body
    };
    let mut result = function.clone();
    Arc::make_mut(&mut result).x.body = Some(body);
    Ok(result)
}
