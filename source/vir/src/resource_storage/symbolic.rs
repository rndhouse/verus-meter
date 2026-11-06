//! Conditional contracts become ordinary Verus obligations at reservation sites.
//!
//! Costs still come exclusively from the structural model. Immutable scalar
//! inputs give the budget a stable entry-state meaning without a ghost counter.

use super::accounting::StorageReport;
use super::budget::{BudgetExpr, BudgetExprX, evaluate_envelope, is_conditional};
use super::layout::Layouts;
use super::model::ResourceContract;
use crate::ast::*;
use crate::ast_util::*;
use crate::def::Spanned;
use crate::messages::{Span, error};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn predicate(expr: &Expr, function: &Function) -> Result<Expr, VirErr> {
    let variable = match &expr.x {
        ExprX::Var(name) => Some(name),
        ExprX::ReadPlace(place, _) => match &place.x {
            PlaceX::Local(name) => Some(name),
            _ => None,
        },
        _ => None,
    };
    if let Some(name) = variable {
        if function.x.params.iter().any(|p| {
            p.x.name == *name
                && p.x.mode == Mode::Exec
                && !p.x.user_mut
                && matches!(&*p.x.typ, TypX::Bool | TypX::Int(IntRange::U(32) | IntRange::USize))
        }) {
            return Ok(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(name.clone())));
        }
        return Err(error(
            &expr.span,
            "memory budget predicates currently require immutable bool, u32, or usize input parameters",
        ));
    }
    let x = match &expr.x {
        ExprX::Const(Constant::Bool(_) | Constant::Int(_)) => return Ok(expr.clone()),
        ExprX::Unary(UnaryOp::Not, e) => ExprX::Unary(UnaryOp::Not, predicate(e, function)?),
        ExprX::Binary(op @ (BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Inequality(_)), a, b) => {
            ExprX::Binary(*op, predicate(a, function)?, predicate(b, function)?)
        }
        ExprX::Logical(op, a, b) => {
            ExprX::Logical(*op, predicate(a, function)?, predicate(b, function)?)
        }
        _ => {
            return Err(error(
                &expr.span,
                "memory budget predicates currently support scalar input comparisons and Boolean operators",
            ));
        }
    };
    Ok(SpannedTyped::new(&expr.span, &expr.typ, x))
}

pub(super) fn function_bound(
    function: &Function,
    budgets: &HashMap<Fun, u64>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
) -> Result<Option<Expr>, VirErr> {
    let Some(ResourceContract::LexicalSlotsV5Expr { budget }) = &function.x.attrs.resource_contract
    else {
        return Ok(None);
    };
    if !is_conditional(budget) {
        return Ok(None);
    }
    fn lower(
        expr: &BudgetExpr,
        function: &Function,
        budgets: &HashMap<Fun, u64>,
        functions: &HashMap<Fun, Function>,
        layouts: &Layouts,
    ) -> Result<Expr, VirErr> {
        let x = match &expr.x {
            BudgetExprX::If(cond, a, b) => ExprX::If(
                predicate(cond, function)?,
                lower(a, function, budgets, functions, layouts)?,
                Some(lower(b, function, budgets, functions, layouts)?),
            ),
            BudgetExprX::Add(a, b) | BudgetExprX::Mul(a, b) => {
                let op = if matches!(expr.x, BudgetExprX::Add(..)) {
                    ArithOp::Add(OverflowBehavior::Allow)
                } else {
                    ArithOp::Mul(OverflowBehavior::Allow)
                };
                ExprX::Binary(
                    BinaryOp::Arith(op),
                    lower(a, function, budgets, functions, layouts)?,
                    lower(b, function, budgets, functions, layouts)?,
                )
            }
            _ => ExprX::Const(const_int_from_u128(evaluate_envelope(
                expr, budgets, functions, layouts,
            )? as u128)),
        };
        Ok(SpannedTyped::new(&expr.span, &int_typ(), x))
    }
    Ok(Some(lower(budget, function, budgets, functions, layouts)?))
}

fn obligation(span: &Span, bytes: u64, bound: &Expr) -> Stmt {
    let cost =
        SpannedTyped::new(span, &int_typ(), ExprX::Const(const_int_from_u128(bytes as u128)));
    let assertion = SpannedTyped::new(span, &unit_typ(), ExprX::AssertAssume {
        is_assume: false,
        expr: mk_ineq(span, &cost, bound, InequalityOp::Le),
        msg: Some(error(span, format!("conditional memory budget exceeded: cannot prove {bytes} model bytes fit the declared bound")).secondary_span(&bound.span)),
    });
    Spanned::new(span.clone(), StmtX::Expr(assertion))
}

pub(super) fn instrument(
    function: &Function,
    bound: &Expr,
    report: &StorageReport,
    layouts: &Layouts,
) -> Result<Function, VirErr> {
    let mut sites: HashMap<u64, (Span, u64)> = HashMap::new();
    let parameter_spans: HashSet<_> = function.x.params.iter().map(|p| p.span.id).collect();
    for (span, bytes) in &report.reservations {
        if parameter_spans.contains(&span.id) {
            continue;
        }
        let site = sites.entry(span.id).or_insert((span.clone(), 0));
        site.1 = site.1.max(*bytes);
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
                    if let Some((span, bytes)) = sites.get(&arg.span.id) {
                        seen.insert(arg.span.id);
                        checks.push(obligation(span, *bytes, bound));
                    }
                }
            }
            if let Some((span, bytes)) = sites.get(&expr.span.id) {
                seen.insert(expr.span.id);
                checks.push(obligation(span, *bytes, bound));
            }
            if !checks.is_empty() {
                Ok(mk_block(&expr.span, checks, Some(expr.clone())))
            } else {
                Ok(expr.clone())
            }
        },
        &|seen, _, stmt| {
            if let StmtX::Decl { .. } = &stmt.x
                && let Some((span, bytes)) = sites.get(&stmt.span.id)
            {
                seen.insert(stmt.span.id);
                Ok(vec![obligation(span, *bytes, bound), stmt.clone()])
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
    let body = mk_block(
        &body.span,
        vec![obligation(&function.span, parameters, bound)],
        Some(body.clone()),
    );
    let mut result = function.clone();
    Arc::make_mut(&mut result).x.body = Some(body);
    Ok(result)
}
