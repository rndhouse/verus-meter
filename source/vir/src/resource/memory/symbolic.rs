//! Conditional contracts become ordinary Verus obligations at reservation sites.
//!
//! Costs still come exclusively from the structural model. Immutable scalar
//! inputs give the budget a stable entry-state meaning without a ghost counter.

use super::accounting::{CheckKind, Obligation};
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
        Some(super::model::ResourceContract { budget, .. }) => {
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

fn obligation(check: &Obligation) -> Option<Stmt> {
    let Obligation { span, cost, bound, kind } = check;
    let cost = cost.select(span, &bound.selection);
    let bound = &bound.amount;
    let message = match (super::contracts::constant(&cost), super::contracts::constant(bound)) {
        (Some(cost), Some(bound)) if cost <= bound => return None,
        (Some(cost), Some(bound)) => match kind {
            CheckKind::Function => format!("memory budget exceeded: peak {cost} bytes exceeds budget {bound} bytes"),
            CheckKind::Section => format!("section memory budget exceeded: peak {cost} bytes exceeds budget {bound} bytes"),
            CheckKind::Checkpoint => format!("mem_peak assertion failed: peak {cost} bytes exceeds bound {bound} bytes"),
        },
        _ => "conditional memory budget exceeded: cannot prove the required model bytes fit the declared bound".into(),
    };
    let assertion = SpannedTyped::new(
        span,
        &unit_typ(),
        ExprX::AssertAssume {
            is_assume: false,
            expr: mk_ineq(span, &cost, bound, InequalityOp::Le),
            msg: Some(if matches!(kind, CheckKind::Checkpoint) {
                error(&bound.span, message).secondary_span(span)
            } else {
                error(span, message).secondary_span(&bound.span)
            }),
        },
    );
    Some(Spanned::new(span.clone(), StmtX::Expr(assertion)))
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
        ExprX::Binary(BinaryOp::Arith(_), ..) | ExprX::Call { .. } => {
            if let ExprX::Binary(_, a, b) = &expr.x {
                range_checks(a, guard, checks);
                range_checks(b, guard, checks);
            }
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
    obligations: &[Obligation],
    checks: &[(Span, Expr)],
    growth: &super::growth::Growth,
    fresh_span: &dyn Fn(&Span) -> Span,
) -> Result<Function, VirErr> {
    // Inserted proofs must have fresh AST identities. Reusing an executable
    // allocation's identity confuses resolution inference for owned values.
    let mut sites: HashMap<u64, (Span, Vec<Stmt>)> = HashMap::new();
    let mut entry_checks = growth.declarations.clone();
    let mut parameter_spans: HashSet<_> = function.x.params.iter().map(|p| p.span.id).collect();
    parameter_spans.insert(function.span.id);
    for parameter in &parameter_spans {
        if let Some(init) = growth.before.get(parameter) {
            entry_checks.extend(init.clone());
        }
    }
    for check in obligations {
        let Some(statement) = obligation(check) else {
            continue;
        };
        if parameter_spans.contains(&check.span.id) {
            entry_checks.push(statement);
        } else {
            sites
                .entry(check.span.id)
                .or_insert_with(|| (check.span.clone(), Vec::new()))
                .1
                .push(statement);
        }
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
                    "vector capacity exceeded: cannot prove the operation fits the reserved capacity",
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
            let mut checks = growth.before.get(&expr.span.id).cloned().unwrap_or_default();
            let mut rewritten = expr.clone();
            if let ExprX::Loop { invs, .. } = &mut Arc::make_mut(&mut rewritten).x {
                if let Some(additional) = growth.loops.get(&expr.span.id) {
                    Arc::make_mut(invs).extend(additional.iter().map(|inv| LoopInvariant {
                        kind: LoopInvariantKind::InvariantAndEnsures,
                        inv: {
                            let statement =
                                Spanned::new(inv.span.clone(), StmtX::Expr(inv.clone()));
                            let statement =
                                crate::ast_visitor::map_stmt_spans(&statement, &mut |span| {
                                    fresh_span(span)
                                });
                            let StmtX::Expr(inv) = &statement.x else { unreachable!() };
                            inv.clone()
                        },
                    }));
                }
            }
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
            if let Some(updates) = growth.updates.get(&expr.span.id) {
                checks.extend(updates.clone());
            }
            if let Some(after) = growth.after.get(&expr.span.id) {
                let statements = after
                    .iter()
                    .map(|s| crate::ast_visitor::map_stmt_spans(s, &mut |span| fresh_span(span)))
                    .collect();
                let effects = mk_block(&fresh_span(&expr.span), statements, None);
                rewritten = SpannedTyped::new(
                    &fresh_span(&expr.span),
                    &expr.typ,
                    ExprX::EvalAndResolve(rewritten, effects),
                );
            }
            if !checks.is_empty() {
                let checks = checks
                    .iter()
                    .map(|s| crate::ast_visitor::map_stmt_spans(s, &mut |span| fresh_span(span)))
                    .collect();
                Ok(mk_block(&fresh_span(&expr.span), checks, Some(rewritten)))
            } else {
                Ok(rewritten)
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
    if let Some(bound) = bound {
        if super::contracts::numeric_input(bound) {
            range_checks(bound, &mk_bool(&function.span, true), &mut entry_checks);
        }
    }
    let body = if entry_checks.is_empty() {
        body
    } else {
        let checks = entry_checks
            .iter()
            .map(|check| crate::ast_visitor::map_stmt_spans(check, &mut |span| fresh_span(span)))
            .collect();
        mk_block(&fresh_span(&body.span), checks, Some(body))
    };
    let mut result = function.clone();
    Arc::make_mut(&mut result).x.body = Some(body);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::super::footprint::{Footprint, MemoryBudget, MemoryKind, MemorySelection};
    use super::*;

    #[test]
    fn budget_obligations_select_the_requested_memory_kind() {
        let span = Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "kind budget".into(),
        };
        let gpu = MemoryKind::new("device.0.vram");
        let cost =
            Footprint::charge(MemoryKind::host_local(), super::super::contracts::literal(&span, 8))
                .add(
                    &span,
                    Footprint::charge(gpu.clone(), super::super::contracts::literal(&span, 64)),
                );
        let check = |selection, bytes| Obligation {
            span: span.clone(),
            cost: cost.clone(),
            bound: MemoryBudget {
                selection,
                amount: super::super::contracts::literal(&span, bytes),
            },
            kind: CheckKind::Function,
        };
        assert!(obligation(&check(MemorySelection::kind(MemoryKind::host_local()), 8)).is_none());
        assert!(obligation(&check(MemorySelection::kind(gpu.clone()), 63)).is_some());
        assert!(obligation(&check(MemorySelection::kind(gpu), 64)).is_none());
        assert!(obligation(&check(MemorySelection::All, 71)).is_some());
    }
}
