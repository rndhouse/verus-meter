//! Compile-time budget arithmetic and acyclic references to declared contracts.

use super::layout::Layouts;
use super::model::{MODEL_NAME, ResourceContract, eligible, unsupported};
use crate::ast::*;
use crate::def::Spanned;
use crate::messages::{Span, error};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir_macros::ToDebugSNode;

pub type BudgetExpr = Arc<Spanned<BudgetExprX>>;

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub enum BudgetExprX {
    Literal(u64),
    MemSize(Typ),
    Function(Fun),
    Add(BudgetExpr, BudgetExpr),
    Mul(BudgetExpr, BudgetExpr),
    If(Expr, BudgetExpr, BudgetExpr),
    FunctionCall(Fun, Exprs),
    Quantity(Expr),
}

struct Resolver<'a> {
    functions: &'a HashMap<Fun, Function>,
    layouts: &'a Layouts,
    resolved: HashMap<Fun, u64>,
    visiting: HashSet<Fun>,
}

impl Resolver<'_> {
    fn function(&mut self, name: &Fun, span: &Span) -> Result<u64, VirErr> {
        if let Some(budget) = self.resolved.get(name) {
            return Ok(*budget);
        }
        let function = self
            .functions
            .get(name)
            .ok_or_else(|| unsupported(span, "mem_peak references outside this crate"))?;
        let contract = function.x.attrs.resource_contract.as_ref().ok_or_else(|| {
            error(span, "mem_peak requires a declared resource contract")
                .secondary_span(&function.span)
        })?;
        eligible(function)?;
        if !self.visiting.insert(name.clone()) {
            return Err(error(span, "circular mem_peak reference").secondary_span(&function.span));
        }
        let budget = match contract {
            ResourceContract::SourceValuesV8Expr { budget, .. } => self.expr(budget)?,
            _ => {
                return Err(error(
                    span,
                    format!("legacy resource model; rebuild with {MODEL_NAME}"),
                ));
            }
        };
        self.visiting.remove(name);
        self.resolved.insert(name.clone(), budget);
        Ok(budget)
    }

    fn expr(&mut self, expr: &BudgetExpr) -> Result<u64, VirErr> {
        match &expr.x {
            // Retain a safe envelope for existing argument-free mem_peak queries
            // queries. Calls instantiate this formula with their actual arguments.
            BudgetExprX::If(_, then_budget, else_budget) => {
                Ok(self.expr(then_budget)?.max(self.expr(else_budget)?))
            }
            BudgetExprX::Quantity(_) => Ok(u64::MAX),
            BudgetExprX::Literal(n) => Ok(*n),
            BudgetExprX::MemSize(typ) => self.layouts.size(typ, &expr.span),
            BudgetExprX::Function(name) => {
                let n = self.function(name, &expr.span)?;
                let formula = super::contracts::function_bound(
                    &self.functions[name],
                    &self.resolved,
                    self.functions,
                    self.layouts,
                )?;
                if super::contracts::numeric_input(&formula) {
                    return Err(error(
                        &expr.span,
                        "runtime memory budgets require mem_peak(helper(arguments))",
                    ));
                }
                Ok(n)
            }
            BudgetExprX::FunctionCall(name, args) => {
                self.function(name, &expr.span)?;
                // Resolution visits the full dependency graph before substitution.
                // Argument validity is checked in the owning formula's context.
                let mut allowed = HashSet::new();
                for arg in args.iter() {
                    crate::ast_visitor::expr_visitor_check(arg, &mut |_, e| {
                        match &e.x {
                            ExprX::Var(n) => {
                                allowed.insert(n.clone());
                            }
                            ExprX::ReadPlace(p, _) => {
                                if let PlaceX::Local(n) = &p.x {
                                    allowed.insert(n.clone());
                                }
                            }
                            _ => {}
                        }
                        Ok::<(), VirErr>(())
                    })?;
                }
                let bound = super::contracts::instantiate(
                    &self.functions[name],
                    args,
                    &allowed,
                    &self.resolved,
                    self.functions,
                    self.layouts,
                    true,
                )?;
                super::contracts::envelope(&bound)
            }
            BudgetExprX::Add(left, right) | BudgetExprX::Mul(left, right) => {
                // Visit both operands even when one is zero: cycles and invalid
                // references must not be hidden by arithmetic simplification.
                let left = self.expr(left)?;
                let right = self.expr(right)?;
                let result = if matches!(&expr.x, BudgetExprX::Add(..)) {
                    left.checked_add(right)
                } else {
                    left.checked_mul(right)
                };
                if runtime(expr, self.functions) {
                    Ok(result.unwrap_or(u64::MAX))
                } else {
                    result.ok_or_else(|| error(&expr.span, "memory budget arithmetic exceeds u64"))
                }
            }
        }
    }
}

pub(super) fn resolve(
    functions: &[Function],
    function_map: &HashMap<Fun, Function>,
    layouts: &Layouts,
) -> Result<HashMap<Fun, u64>, VirErr> {
    let mut resolver = Resolver {
        functions: function_map,
        layouts,
        resolved: HashMap::new(),
        visiting: HashSet::new(),
    };
    for function in functions {
        if function.x.attrs.resource_contract.is_some() {
            resolver.function(&function.x.name, &function.span)?;
        }
    }
    Ok(resolver.resolved)
}

/// Body budget formulas refer to already resolved function contracts. Their
/// references do not add executable calls or introduce new contract cycles.
pub(super) fn evaluate_body_budget(
    expr: &BudgetExpr,
    budgets: &HashMap<Fun, u64>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
) -> Result<u64, VirErr> {
    if is_conditional(expr) {
        return Err(error(
            &expr.span,
            "conditional memory bounds currently require a function contract; section and checkpoint bounds remain fixed",
        ));
    }
    // Resolve even rejected formulas so cycles and overflow cannot hide in them.
    evaluate_envelope(expr, budgets, functions, layouts)?;
    let bound = super::contracts::lower(expr, &HashSet::new(), budgets, functions, layouts)?;
    super::contracts::constant(&bound).ok_or_else(|| error(
        &expr.span,
        "conditional memory bounds currently require a function contract; section and checkpoint bounds remain fixed",
    ))
}

// Inspect the written formula, not argument-free queries into other contracts.
pub(super) fn is_conditional(expr: &BudgetExpr) -> bool {
    match &expr.x {
        BudgetExprX::If(..) => true,
        BudgetExprX::Add(a, b) | BudgetExprX::Mul(a, b) => is_conditional(a) || is_conditional(b),
        _ => false,
    }
}

pub(super) fn evaluate_envelope(
    expr: &BudgetExpr,
    budgets: &HashMap<Fun, u64>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
) -> Result<u64, VirErr> {
    Resolver { functions, layouts, resolved: budgets.clone(), visiting: HashSet::new() }.expr(expr)
}

/// Runtime quantities need proof-checked bounds rather than a finite envelope.
pub(super) fn runtime(expr: &BudgetExpr, functions: &HashMap<Fun, Function>) -> bool {
    match &expr.x {
        BudgetExprX::Quantity(_) => true,
        BudgetExprX::Add(a, b) | BudgetExprX::Mul(a, b) => {
            runtime(a, functions) || runtime(b, functions)
        }
        BudgetExprX::If(_, a, b) => runtime(a, functions) || runtime(b, functions),
        BudgetExprX::FunctionCall(f, _) => {
            match functions.get(f).and_then(|f| f.x.attrs.resource_contract.as_ref()) {
                Some(ResourceContract::SourceValuesV8Expr { budget, .. }) => {
                    runtime(budget, functions)
                }
                _ => false,
            }
        }
        _ => false,
    }
}
