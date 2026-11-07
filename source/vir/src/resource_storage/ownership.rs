//! Checked ownership summaries for same-crate calls.
//!
//! A result either transfers one input allocation or brings back a fresh one.
//! Summaries come from the same traversal that checks the callee's memory bound;
//! they are never assumptions supplied by the programmer.

use super::analysis::Analysis;
use super::contracts;
use super::heap::Owner;
use super::model::unsupported;
use crate::ast::*;

#[derive(Clone)]
pub(super) enum Returned {
    Input(usize),
    Fresh { capacity: Option<Expr> },
}

pub(super) fn summarize(
    function: &Function,
    owner: Option<Owner>,
) -> Result<Option<Returned>, VirErr> {
    let Some(owner) = owner else {
        return Ok(None);
    };
    if let Some(input) = owner.input {
        return Ok(Some(Returned::Input(input)));
    }
    if let Some(capacity) = &owner.capacity {
        let inputs = contracts::inputs(function);
        crate::ast_visitor::expr_visitor_check(capacity, &mut |_, expr| {
            if let ExprX::Var(name) = &expr.x {
                if !inputs.contains(name) {
                    return Err(unsupported(
                        &expr.span,
                        "returned vector capacities depending on locals; use an immutable input or a literal",
                    ));
                }
            }
            Ok(())
        })?;
    }
    Ok(Some(Returned::Fresh { capacity: owner.capacity }))
}

impl Analysis<'_> {
    pub(super) fn complete_ownership_call(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
        transferred: &mut [Option<Owner>],
    ) -> Result<Option<Owner>, VirErr> {
        let summary = if self.layouts.owner(&expr.typ) {
            Some(self.returned.get(&callee.x.name).ok_or_else(|| {
                unsupported(&expr.span, "a call without a checked ownership summary")
            })?)
        } else {
            None
        };
        let forwarded = if let Some(Returned::Input(index)) = summary {
            Some(transferred[*index].take().ok_or_else(|| {
                unsupported(&expr.span, "a returned input without transferred ownership")
            })?)
        } else {
            None
        };
        // Call composition already checked the inputs at each point where they
        // were live. Retain only the allocation that survives as the result.
        for owner in transferred.iter_mut().filter_map(Option::take) {
            self.release_owner(owner, &expr.span);
        }
        if forwarded.is_some() || summary.is_none() {
            return Ok(forwarded);
        }
        let Some(Returned::Fresh { capacity }) = summary else { unreachable!() };
        let capacity = capacity
            .as_ref()
            .map(|capacity| contracts::substitute(capacity, callee, args, &self.stable_scalars))
            .transpose()?;
        let cost = if let Some(capacity) = &capacity {
            contracts::multiply(
                &expr.span,
                contracts::literal(&expr.span, self.layouts.vector_element(&expr.typ, &expr.span)?),
                capacity.clone(),
            )
        } else {
            contracts::literal(
                &expr.span,
                self.layouts.box_contents(&expr.typ, &expr.span)?.ok_or_else(|| {
                    unsupported(&expr.span, "a returned vector without a capacity summary")
                })?,
            )
        };
        let mut owner = Owner { capacity, ..Default::default() };
        if let Some(bytes) = contracts::constant(&cost) {
            self.storage.reserve(&expr.span, bytes, "returned heap allocation")?;
            owner.bytes = bytes;
        } else {
            self.storage.reserve_dynamic(&expr.span, cost);
            owner.dynamic = Some(expr.span.id);
        }
        Ok(Some(owner))
    }
}
