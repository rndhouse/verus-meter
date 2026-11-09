//! Apply checked allocation summaries across owning calls.
//!
//! Constructors supply byte expressions and memory kinds. Returned allocations
//! are transferred or adopted here without consulting container layouts.

use super::allocations::{self, ReturnedAllocation};
use super::analysis::Analysis;
use super::contracts;
use super::footprint::Charge;
use super::heap::Owner;
use super::model::unsupported;
use crate::ast::*;

/// Export an owning result using its constructor extent or verified replacement
/// effect. Only expressions in the function's input scope can cross the call.
pub(super) fn summarize(
    function: &Function,
    owner: Option<&Owner>,
    replacement: Option<Charge<Expr>>,
    bound: &Expr,
) -> Result<Option<ReturnedAllocation>, VirErr> {
    let Some(owner) = owner else { return Ok(None) };
    if let Some(allocation) = replacement {
        return Ok(Some(ReturnedAllocation::Replaced { input: owner.input, allocation }));
    }
    if let Some(input) = owner.input {
        return Ok(Some(ReturnedAllocation::Input(input)));
    }
    let amount = owner.extent.clone().ok_or_else(|| {
        unsupported(&function.span, "a fresh returned allocation without a byte-size summary")
    })?;
    let inputs = contracts::inputs(function);
    let mut in_scope = true;
    crate::ast_visitor::expr_visitor_check(&amount, &mut |_, expr| {
        if let ExprX::Var(name) = &expr.x {
            in_scope &= inputs.contains(name);
        }
        Ok::<(), VirErr>(())
    })?;
    // A locally charged result is part of the checked peak. If its runtime
    // extent cannot escape the body, the declared bound is a sound (possibly
    // loose) exported extent. Incoming storage took the provenance path above.
    let amount = if in_scope { amount } else { bound.clone() };
    Ok(Some(ReturnedAllocation::Fresh(Charge { kind: owner.kind.clone(), amount })))
}

impl Analysis<'_> {
    /// Adopt a fresh allocation from its byte summary. Conservative replacement
    /// bounds are observed after the call's state commits; exact constructor
    /// extents retain the existing reservation diagnostic at the call site.
    fn returned_owner(
        &mut self,
        expr: &Expr,
        allocation: &Charge<Expr>,
        replacement: bool,
    ) -> Result<Owner, VirErr> {
        let mut owner = Owner {
            kind: allocation.kind.clone(),
            extent: Some(allocation.amount.clone()),
            ..Default::default()
        };
        if replacement {
            let id = super::accounting::Accounting::fresh_allocation();
            self.storage.set_allocation(id, allocation.kind.clone(), allocation.amount.clone());
            owner.dynamic = Some(id);
        } else if let Some(bytes) = contracts::constant(&allocation.amount) {
            self.storage.reserve(
                &expr.span,
                allocation.kind.clone(),
                bytes,
                "returned heap allocation",
            )?;
            owner.bytes = bytes;
        } else {
            self.storage.reserve_dynamic(
                &expr.span,
                allocation.kind.clone(),
                allocation.amount.clone(),
            );
            owner.dynamic = Some(expr.span.id);
        }
        Ok(owner)
    }

    pub(super) fn complete_ownership_call(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
        transferred: &mut [Option<Owner>],
    ) -> Result<Option<Owner>, VirErr> {
        let summary = if self.layouts.owner(&expr.typ) {
            Some(
                self.summaries
                    .get(&callee.x.name)
                    .and_then(|summary| summary.allocations.returned.as_ref())
                    .ok_or_else(|| {
                        unsupported(&expr.span, "a call without a checked ownership summary")
                    })?
                    .clone(),
            )
        } else {
            None
        };
        let input = match &summary {
            Some(ReturnedAllocation::Input(index)) => Some(*index),
            Some(ReturnedAllocation::Replaced { input, .. }) => *input,
            _ => None,
        };
        let forwarded = input
            .map(|index| {
                transferred[index].take().ok_or_else(|| {
                    unsupported(&expr.span, "a returned input without transferred ownership")
                })
            })
            .transpose()?;
        // Lifetime profiles already checked the inputs during the call. Only the
        // allocation selected as the result survives in the caller's ownership.
        for owner in transferred.iter_mut().filter_map(Option::take) {
            self.release_owner(owner, &expr.span);
        }
        let mut replacement = None;
        let mut result = match summary {
            Some(ReturnedAllocation::Input(_)) => forwarded,
            Some(ReturnedAllocation::Fresh(allocation)) => {
                let allocation =
                    allocations::instantiate(&allocation, callee, args, &self.stable_scalars)?;
                Some(self.returned_owner(expr, &allocation, false)?)
            }
            Some(ReturnedAllocation::Replaced { allocation, .. }) => {
                let allocation =
                    allocations::instantiate(&allocation, callee, args, &self.stable_scalars)?;
                let owner = if let Some(owner) = forwarded {
                    owner
                } else {
                    self.returned_owner(expr, &allocation, true)?
                };
                replacement = Some(allocation);
                Some(owner)
            }
            None => None,
        };
        if let Some(owner) = &mut result {
            self.attach_vector_result(expr, owner, callee, args, replacement)?;
        }
        Ok(result)
    }
}
