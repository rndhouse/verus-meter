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

/// Declare one erased integer used by allocation snapshots and mutable proof state.
pub(super) fn integer_local(span: &Span, name: VarIdent) -> (Expr, Stmt) {
    scalar_local(span, name, &int_typ())
}

/// Declare an erased scalar snapshot with the source scalar's logical type.
/// Its initial value is only a placeholder; capture use requires construction's
/// actual assignment, maintained by the environment descriptor.
pub(super) fn scalar_local(span: &Span, name: VarIdent, typ: &Typ) -> (Expr, Stmt) {
    assert!(matches!(&**typ, TypX::Int(_) | TypX::Bool));
    let initial =
        if matches!(&**typ, TypX::Bool) { Constant::Bool(false) } else { const_int_from_u128(0) };
    let value = SpannedTyped::new(span, typ, ExprX::Var(name.clone()));
    let declaration = Spanned::new(
        span.clone(),
        StmtX::Decl {
            pattern: SpannedTyped::new(
                span,
                typ,
                PatternX::Var(PatternBinding {
                    name,
                    by_ref: ByRef::No,
                    typ: typ.clone(),
                    user_mut: Some(true),
                    copy: true,
                    move_exec_to_proof_okay: MoveExecToProofOkay::No,
                }),
            ),
            mode: Some((Mode::Spec, DeclProph::Default)),
            init: Some(SpannedTyped::new(
                span,
                typ,
                PlaceX::Temporary(SpannedTyped::new(span, typ, ExprX::Const(initial))),
            )),
            els: None,
            assert_irrefutable: false,
        },
    );
    (value, declaration)
}

/// Write an erased scalar; instrumentation gives each use fresh AST IDs.
pub(super) fn assign(span: &Span, variable: &Expr, value: Expr) -> Stmt {
    let ExprX::Var(name) = &variable.x else { unreachable!() };
    Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &unit_typ(),
            ExprX::Assign {
                place: SpannedTyped::new(span, &variable.typ, PlaceX::Local(name.clone())),
                rhs: value,
                op: None,
                typ: variable.typ.clone(),
                resolve: false,
            },
        )),
    )
}

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
            CheckKind::CurrentCheckpoint => format!("current(memory) assertion failed: live {cost} bytes exceeds bound {bound} bytes"),
            CheckKind::Checkpoint => format!("peak(memory) assertion failed: peak {cost} bytes exceeds bound {bound} bytes"),
        },
        _ => "conditional memory budget exceeded: cannot prove the required model bytes fit the declared bound".into(),
    };
    let assertion = SpannedTyped::new(
        span,
        &unit_typ(),
        ExprX::AssertAssume {
            is_assume: false,
            expr: mk_ineq(span, &cost, bound, InequalityOp::Le),
            msg: Some(if matches!(kind, CheckKind::Checkpoint | CheckKind::CurrentCheckpoint) {
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

/// Actual attachment sites, kept distinct because a declaration can host a
/// budget assertion but cannot implicitly host an operation's state commit.
#[derive(Default)]
struct AttachedSites {
    /// Required inequalities inserted at expressions, declarations, or calls.
    obligations: HashSet<u64>,
    /// Expression sites around which operation state actions are inserted.
    expressions: HashSet<u64>,
    /// Actual loops receiving resource invariants or exit annotations.
    loops: HashSet<u64>,
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
    let mut seen = AttachedSites::default();
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
            let scheduled = growth.worker_joins.contains_key(&expr.span.id)
                || [&growth.before, &growth.updates, &growth.after].iter().any(|schedule| {
                    schedule.get(&expr.span.id).is_some_and(|actions| !actions.is_empty())
                });
            let repeated = !seen.expressions.insert(expr.span.id);
            let entry_snapshot = parameter_spans.contains(&expr.span.id)
                && growth.before.get(&expr.span.id).is_some_and(|actions| !actions.is_empty());
            if (repeated && scheduled) || entry_snapshot {
                return Err(error(&expr.span, "ambiguous memory proof-state execution site"));
            }
            let mut checks = growth.before.get(&expr.span.id).cloned().unwrap_or_default();
            let mut rewritten = expr.clone();
            if let ExprX::Loop {
                invs,
                loop_isolation,
                known_no_back_edge,
                allow_complex_invariants,
                ..
            } = &mut Arc::make_mut(&mut rewritten).x
            {
                if !seen.loops.insert(expr.span.id) {
                    return Err(error(&expr.span, "ambiguous memory loop proof site"));
                }
                if growth.single_visit_loops.contains(&expr.span.id) {
                    *loop_isolation = false;
                    *known_no_back_edge = true;
                    *allow_complex_invariants = true;
                }
                if let Some(additional) = growth.loops.get(&expr.span.id) {
                    Arc::make_mut(invs).extend(additional.iter().map(|inv| LoopInvariant {
                        kind: if growth.exiting_loops.contains(&expr.span.id) {
                            LoopInvariantKind::InvariantExceptBreak
                        } else {
                            LoopInvariantKind::InvariantAndEnsures
                        },
                        inv: {
                            let statement = Spanned::new(
                                inv.span.clone(),
                                StmtX::Expr(super::metadata::expr::purpose(
                                    inv.clone(),
                                    "memory loop ownership and allocation state",
                                )),
                            );
                            let statement =
                                crate::ast_visitor::map_stmt_spans(&statement, &mut |span| {
                                    fresh_span(span)
                                });
                            let StmtX::Expr(inv) = &statement.x else { unreachable!() };
                            inv.clone()
                        },
                    }));
                }
                if let Some(additional) = growth.loop_ensures.get(&expr.span.id) {
                    for inv in additional {
                        let statement = Spanned::new(
                            inv.span.clone(),
                            StmtX::Expr(super::metadata::expr::purpose(
                                inv.clone(),
                                "memory allocation state at loop exit",
                            )),
                        );
                        let statement =
                            crate::ast_visitor::map_stmt_spans(&statement, &mut |span| {
                                fresh_span(span)
                            });
                        let StmtX::Expr(inv) = &statement.x else { unreachable!() };
                        Arc::make_mut(invs).push(LoopInvariant {
                            kind: LoopInvariantKind::Ensures,
                            inv: inv.clone(),
                        });
                    }
                }
            }
            if let ExprX::Call { args, .. } = &expr.x {
                for arg in args.iter().filter(|arg| matches!(arg.x, ExprX::TwoPhaseBorrowMut(_))) {
                    if let Some((_, statements)) = sites.get(&arg.span.id) {
                        seen.obligations.insert(arg.span.id);
                        checks.extend(statements.iter().cloned());
                    }
                }
            }
            let mut after_operands = Vec::new();
            if let Some((_, statements)) = sites.get(&expr.span.id) {
                seen.obligations.insert(expr.span.id);
                if matches!(&expr.x, ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. }
                    if matches!(attrs.resource_intrinsic, Some(ResourceIntrinsic::ResultUnwrap | ResourceIntrinsic::OptionUnwrap)))
                {
                    // An inline join/pop operand establishes the returned allocation
                    // observations. Checking extraction before that operand can
                    // read a previous iteration's bytes (or initialized zero).
                    // Unwrap changes no allocation extent; its recorded overlap
                    // is checked after evaluating the operand and extraction.
                    after_operands.extend(statements.iter().cloned());
                } else {
                    checks.extend(statements.iter().cloned());
                }
            }
            // Moving a field out of a retained closure environment creates a
            // destination value at the read. Its place has a distinct AST ID.
            if let ExprX::ReadPlace(place, _) = &expr.x
                && matches!(place.x, PlaceX::Local(_))
                && place.span.id != expr.span.id
                && let Some((_, statements)) = sites.get(&place.span.id)
            {
                seen.obligations.insert(place.span.id);
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
                rewritten = after_evaluation(rewritten, effects, fresh_span);
            }
            rewritten = super::workers::resolve_join(expr, rewritten, growth, fresh_span)?;
            if !after_operands.is_empty() {
                let statements = after_operands
                    .iter()
                    .map(|statement| {
                        crate::ast_visitor::map_stmt_spans(statement, &mut |span| fresh_span(span))
                    })
                    .collect();
                rewritten = SpannedTyped::new(
                    &fresh_span(&expr.span),
                    &expr.typ,
                    ExprX::EvalAndResolve(
                        rewritten,
                        mk_block(&fresh_span(&expr.span), statements, None),
                    ),
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
            if let StmtX::Decl { init, .. } = &stmt.x {
                let mut statements = Vec::new();
                for id in std::iter::once(stmt.span.id).chain(
                    init.iter()
                        .filter(|place| {
                            matches!(place.x, PlaceX::Local(_)) && place.span.id != stmt.span.id
                        })
                        .map(|place| place.span.id),
                ) {
                    if let Some((_, checks)) = sites.get(&id) {
                        seen.obligations.insert(id);
                        statements.extend(checks.iter().cloned());
                    }
                }
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
        if !seen.obligations.contains(id) {
            return Err(error(span, "unsupported conditional memory reservation site"));
        }
    }
    // State actions carry the same proof significance as budget assertions.
    for id in growth.worker_joins.keys() {
        if !seen.expressions.contains(id) {
            return Err(error(&function.span, "unsupported worker join proof site"));
        }
    }
    // Missing snapshots or commits must never leave their initialized zero
    // counters standing in for an operation that was actually executed.
    for (phase, schedule, entry_allowed) in [
        ("snapshot", &growth.before, true),
        ("transition", &growth.updates, false),
        ("commit", &growth.after, false),
    ] {
        for (id, actions) in schedule {
            if let Some(action) = actions.first() {
                if !seen.expressions.contains(id)
                    && !(entry_allowed && parameter_spans.contains(id))
                {
                    return Err(error(
                        &action.span,
                        format!("unsupported memory proof-state {phase} site"),
                    ));
                }
            }
        }
    }
    for id in growth
        .loops
        .keys()
        .chain(growth.loop_ensures.keys())
        .chain(&growth.single_visit_loops)
        .chain(&growth.exiting_loops)
    {
        if !seen.loops.contains(id) {
            return Err(error(&function.span, "unsupported memory loop proof site"));
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

/// Scope cleanup runs after the result operand, but before a return or loop
/// exit transfers control. Wrapping the exit itself would make the proof dead
/// code. For ordinary expressions, EvalAndResolve preserves the produced value.
fn after_evaluation(expr: Expr, effects: Expr, fresh_span: &dyn Fn(&Span) -> Span) -> Expr {
    let resolve = |value: &Expr| {
        SpannedTyped::new(
            &fresh_span(&value.span),
            &value.typ,
            ExprX::EvalAndResolve(value.clone(), effects.clone()),
        )
    };
    let exit = match &expr.x {
        ExprX::Return(Some(value)) => ExprX::Return(Some(resolve(value))),
        ExprX::BreakOrContinue { label, is_break, value: Some(value) } => ExprX::BreakOrContinue {
            label: label.clone(),
            is_break: *is_break,
            value: Some(resolve(value)),
        },
        ExprX::Return(None) | ExprX::BreakOrContinue { value: None, .. } => {
            return mk_block(
                &fresh_span(&expr.span),
                vec![Spanned::new(effects.span.clone(), StmtX::Expr(effects))],
                Some(expr),
            );
        }
        _ => return resolve(&expr),
    };
    SpannedTyped::new(&fresh_span(&expr.span), &expr.typ, exit)
}

#[cfg(test)]
mod tests {
    use super::super::contracts;
    use super::super::footprint::{Footprint, MemoryBudget, MemoryKind, MemorySelection};
    use super::*;

    fn span(id: u64) -> Span {
        Span {
            raw_span: Arc::new(()),
            id,
            data: Arc::new([]),
            as_string: "memory instrumentation".into(),
        }
    }

    /// Minimal executable signature for exercising the instrumentation/erasure
    /// boundary independently of layout accounting and Rust frontend lowering.
    fn function(body: Expr) -> Function {
        let span = span(1);
        let visibility = Visibility { restricted_to: None };
        let ret = Spanned::new(
            span.clone(),
            ParamX {
                name: VarIdent(Arc::new("result".into()), VarIdentDisambiguate::VirTemp(0)),
                typ: unit_typ(),
                mode: Mode::Exec,
                user_mut: false,
                unwrapped_info: None,
            },
        );
        Spanned::new(
            span.clone(),
            FunctionX {
                name: crate::fun!(CrateId::Internal => "tests"; "memory_instrumentation"),
                proxy: None,
                kind: FunctionKind::Static,
                visibility: visibility.clone(),
                body_visibility: BodyVisibility::Visibility(visibility.clone()),
                opaqueness: Opaqueness::Revealed { visibility },
                owning_module: None,
                mode: Mode::Exec,
                typ_params: Arc::new(vec![]),
                typ_bounds: Arc::new(vec![]),
                params: Arc::new(vec![]),
                outer_ret: ret.clone(),
                inner_ret: ret,
                require: Arc::new(vec![]),
                ensure: (Arc::new(vec![]), Arc::new(vec![])),
                returns: None,
                decrease: Arc::new(vec![]),
                decrease_when: None,
                decrease_by: None,
                fndef_axioms: None,
                mask_spec: None,
                atomic_update: None,
                unwind_spec: None,
                item_kind: ItemKind::Function,
                attrs: Arc::new(FunctionAttrsX {
                    resource_contract: Some(super::super::model::ResourceContract {
                        budget: Spanned::new(span, super::super::BudgetExprX::Literal(0)),
                    }),
                    ..Default::default()
                }),
                body: Some(body),
                return_opaque_type_eqs: Arc::new(vec![]),
                extra_dependencies: vec![],
                hidden: Arc::new(vec![]),
            },
        )
    }

    fn failing_obligation(span: Span) -> Obligation {
        Obligation {
            cost: Footprint::allowance(contracts::literal(&span, 1)),
            bound: MemoryBudget::total(contracts::literal(&span, 0)),
            kind: CheckKind::Function,
            span,
        }
    }

    #[test]
    fn unmatched_obligation_site_is_rejected() {
        let function = function(mk_block(&span(2), vec![], None));
        let obligation = failing_obligation(span(99));
        let next_id = std::cell::Cell::new(100);
        let result =
            instrument(&function, None, &[obligation], &[], &Default::default(), &|original| {
                let mut fresh = original.clone();
                fresh.id = next_id.get();
                next_id.set(fresh.id + 1);
                fresh
            });
        let error = result.unwrap_err();
        assert!(error.note.contains("unsupported conditional memory reservation site"));
    }

    #[test]
    fn unmatched_proof_state_sites_are_rejected() {
        // These schedules were previously ignored when no AST site matched.
        // A future lowering mismatch must stop before publishing a proof body.
        for phase in ["before", "updates", "after", "invariants", "ensures", "single", "exits"] {
            let function = function(mk_block(&span(2), vec![], None));
            let mut growth = super::super::growth::Growth::default();
            let action = Spanned::new(
                span(99),
                StmtX::Expr(SpannedTyped::new(
                    &span(99),
                    &unit_typ(),
                    ExprX::AssertAssume {
                        is_assume: false,
                        expr: mk_bool(&span(99), false),
                        msg: None,
                    },
                )),
            );
            match phase {
                "before" => {
                    growth.before.insert(99, vec![action]);
                }
                "updates" => {
                    growth.updates.insert(99, vec![action]);
                }
                "after" => {
                    growth.after.insert(99, vec![action]);
                }
                "invariants" => {
                    growth.loops.insert(99, vec![mk_bool(&span(99), false)]);
                }
                "ensures" => {
                    growth.loop_ensures.insert(99, vec![mk_bool(&span(99), false)]);
                }
                "single" => {
                    growth.single_visit_loops.insert(99);
                }
                "exits" => {
                    growth.exiting_loops.insert(99);
                }
                _ => unreachable!(),
            }
            let result =
                instrument(&function, None, &[], &[], &growth, &|original| original.clone());
            assert!(result.is_err(), "unmatched {phase} schedule was accepted");
        }
    }

    #[test]
    fn loop_proofs_require_a_loop_site() {
        let function = function(mk_block(&span(2), vec![], None));
        let mut growth = super::super::growth::Growth::default();
        growth.loops.insert(2, vec![mk_bool(&span(2), false)]);
        let error = instrument(&function, None, &[], &[], &growth, &|original| original.clone())
            .unwrap_err();
        assert!(error.note.contains("unsupported memory loop proof site"));
    }

    fn marker(value: u64, id: u64) -> Stmt {
        Spanned::new(span(id), StmtX::Expr(contracts::literal(&span(id), value)))
    }

    #[test]
    fn proof_state_order_preserves_checks_and_operation() {
        let function = function(mk_block(&span(2), vec![marker(30, 3)], None));
        let mut growth = super::super::growth::Growth::default();
        growth.before.insert(3, vec![marker(10, 4)]);
        growth.updates.insert(3, vec![marker(20, 5)]);
        growth.after.insert(3, vec![marker(40, 6)]);
        let next_id = std::cell::Cell::new(100);
        let updated = instrument(
            &function,
            None,
            &[failing_obligation(span(3))],
            &[],
            &growth,
            &|original| {
                let mut fresh = original.clone();
                fresh.id = next_id.get();
                next_id.set(fresh.id + 1);
                fresh
            },
        )
        .unwrap();
        let mut events = Vec::new();
        crate::ast_visitor::expr_visitor_check(updated.x.body.as_ref().unwrap(), &mut |_, expr| {
            if matches!(expr.x, ExprX::AssertAssume { is_assume: false, .. }) {
                events.push("check".to_string());
            } else if let Some(value @ (10 | 20 | 30 | 40)) = contracts::constant(expr) {
                events.push(value.to_string());
            }
            Ok::<(), VirErr>(())
        })
        .unwrap();
        assert_eq!(events, ["10", "check", "20", "30", "40"]);
    }

    #[test]
    fn ambiguous_state_action_site_is_rejected() {
        let function = function(mk_block(&span(2), vec![marker(30, 3), marker(31, 3)], None));
        let mut growth = super::super::growth::Growth::default();
        growth.before.insert(3, vec![marker(10, 4)]);
        let error = instrument(&function, None, &[], &[], &growth, &|original| original.clone())
            .unwrap_err();
        assert!(error.note.contains("ambiguous memory proof-state execution site"));
    }

    #[test]
    fn entry_sites_accept_only_snapshots_and_execute_them_once() {
        let function = function(mk_block(&span(2), vec![], None));
        let mut growth = super::super::growth::Growth::default();
        growth.before.insert(function.span.id, vec![marker(10, 4)]);
        instrument(&function, None, &[], &[], &growth, &|original| original.clone()).unwrap();

        for phase in ["transition", "commit"] {
            let mut growth = super::super::growth::Growth::default();
            let schedule =
                if phase == "transition" { &mut growth.updates } else { &mut growth.after };
            schedule.insert(function.span.id, vec![marker(20, 5)]);
            let error =
                instrument(&function, None, &[], &[], &growth, &|original| original.clone())
                    .unwrap_err();
            assert!(error.note.contains(&format!("unsupported memory proof-state {phase} site")));
        }

        let body = mk_block(&function.span, vec![], None);
        let mut colliding = function.clone();
        Arc::make_mut(&mut colliding).x.body = Some(body);
        let error = instrument(&colliding, None, &[], &[], &growth, &|original| original.clone())
            .unwrap_err();
        assert!(error.note.contains("ambiguous memory proof-state execution site"));
    }

    #[test]
    fn annotation_erasure_preserves_generated_assertions() {
        let marker_span = span(3);
        let marker = SpannedTyped::new(
            &marker_span,
            &unit_typ(),
            ExprX::ResourceAssert(Spanned::new(
                marker_span.clone(),
                super::super::BudgetExprX::Literal(0),
            )),
        );
        let body = mk_block(&span(2), vec![Spanned::new(marker_span, StmtX::Expr(marker))], None);
        let function = function(body);
        let next_id = std::cell::Cell::new(100);
        let updated = instrument(
            &function,
            None,
            &[failing_obligation(span(2))],
            &[],
            &Default::default(),
            &|original| {
                let mut fresh = original.clone();
                fresh.id = next_id.get();
                next_id.set(fresh.id + 1);
                fresh
            },
        )
        .unwrap();
        let mut functions = [updated];
        super::super::erase_annotations(&mut functions).unwrap();
        let mut assertions = Vec::new();
        crate::ast_visitor::expr_visitor_check(
            functions[0].x.body.as_ref().unwrap(),
            &mut |_, expr| {
                match &expr.x {
                    ExprX::AssertAssume { is_assume: false, expr, .. } => {
                        assertions.push(expr.clone());
                    }
                    ExprX::AssertAssume { is_assume: true, .. }
                    | ExprX::ResourceAssert(_)
                    | ExprX::ResourceAssertCurrent(_)
                    | ExprX::ResourceSection(_) => panic!("unexpected erased obligation"),
                    _ => {}
                }
                Ok::<(), VirErr>(())
            },
        )
        .unwrap();
        assert_eq!(assertions.len(), 1);
        assert!(matches!(
            contracts::simplify(&assertions[0]).x,
            ExprX::Const(Constant::Bool(false))
        ));
    }

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
