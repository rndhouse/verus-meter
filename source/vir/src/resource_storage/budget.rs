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
    SizeOf(Typ),
    Function(Fun),
    Add(BudgetExpr, BudgetExpr),
    Mul(BudgetExpr, BudgetExpr),
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
            .ok_or_else(|| unsupported(span, "peakmem references outside this crate"))?;
        let contract = function.x.attrs.resource_contract.as_ref().ok_or_else(|| {
            error(span, "peakmem requires a declared resource contract")
                .secondary_span(&function.span)
        })?;
        eligible(function)?;
        if !self.visiting.insert(name.clone()) {
            return Err(error(span, "circular peakmem reference").secondary_span(&function.span));
        }
        let budget = match contract {
            ResourceContract::LexicalSlotsV5Expr { budget } => self.expr(budget)?,
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
            BudgetExprX::Literal(n) => Ok(*n),
            BudgetExprX::SizeOf(typ) => self.layouts.size(typ, &expr.span),
            BudgetExprX::Function(name) => self.function(name, &expr.span),
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
                result.ok_or_else(|| error(&expr.span, "memory budget arithmetic exceeds u64"))
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
