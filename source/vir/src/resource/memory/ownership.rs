//! Checked ownership summaries for same-crate calls.
//!
//! A result either transfers one input allocation or brings back a fresh one.
//! Summaries come from the same traversal that checks the callee's memory bound;
//! they are never assumptions supplied by the programmer.

use super::analysis::Analysis;
use super::contracts;
use super::footprint::MemoryKind;
use super::heap::Owner;
use super::model::unsupported;
use crate::ast::*;

#[derive(Clone)]
pub(super) enum Returned {
    Input(usize),
    /// An original allocation or a replacement bounded by the verified body.
    Grown {
        input: Option<usize>,
        bytes: Expr,
    },
    Fresh {
        kind: MemoryKind,
        capacity: Option<Expr>,
    },
}

pub(super) fn summarize(
    function: &Function,
    owner: Option<Owner>,
    growth: &super::growth::Growth,
    bound: &Expr,
) -> Result<Option<Returned>, VirErr> {
    let Some(owner) = owner else {
        return Ok(None);
    };
    if let Some(id) = owner.vector {
        if growth.vectors[id].changed {
            return Ok(Some(Returned::Grown {
                input: owner.input,
                bytes: super::growth::retained_bound(&growth.vectors[id], function, bound),
            }));
        }
    }
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
    Ok(Some(Returned::Fresh { kind: owner.kind, capacity: owner.capacity }))
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
            Some(
                self.summaries
                    .get(&callee.x.name)
                    .and_then(|summary| summary.returned.as_ref())
                    .ok_or_else(|| {
                        unsupported(&expr.span, "a call without a checked ownership summary")
                    })?,
            )
        } else {
            None
        };
        if let Some(Returned::Grown { input, bytes }) = summary {
            let bytes = contracts::substitute(bytes, callee, args, &self.stable_scalars)?;
            let owner = if let Some(index) = input {
                transferred[*index]
                    .take()
                    .ok_or_else(|| unsupported(&expr.span, "missing grown input"))?
            } else {
                let element = self.layouts.vector_element(&expr.typ, &expr.span)?;
                let allocation = super::accounting::Accounting::fresh_allocation();
                let id = self.growth.new_vector(
                    &expr.span,
                    contracts::literal(&expr.span, 0),
                    bytes.clone(),
                    element,
                    None,
                    allocation,
                );
                self.storage.set_allocation(
                    allocation,
                    MemoryKind::host_heap(),
                    self.growth.vectors[id].bytes.clone(),
                );
                Owner { vector: Some(id), dynamic: Some(allocation), ..Owner::default() }
            };
            self.retain_vector_growth(&expr.span, owner.vector.unwrap(), bytes);
            for other in transferred.iter_mut().filter_map(Option::take) {
                self.release_owner(other, &expr.span);
            }
            return Ok(Some(owner));
        }
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
        let Some(Returned::Fresh { kind, capacity }) = summary else { unreachable!() };
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
        let mut owner = Owner { kind: kind.clone(), capacity, ..Default::default() };
        if let Some(bytes) = contracts::constant(&cost) {
            self.storage.reserve(
                &expr.span,
                owner.kind.clone(),
                bytes,
                "returned heap allocation",
            )?;
            owner.bytes = bytes;
        } else {
            self.storage.reserve_dynamic(&expr.span, owner.kind.clone(), cost.clone());
            owner.dynamic = Some(expr.span.id);
        }
        if let Some(capacity) = owner.capacity.clone() {
            let allocation = super::accounting::Accounting::fresh_allocation();
            let id = self.growth.new_vector(
                &expr.span,
                capacity,
                cost,
                self.layouts.vector_element(&expr.typ, &expr.span)?,
                None,
                allocation,
            );
            if let Some(old) = owner.dynamic {
                self.storage.release_dynamic(old);
            }
            self.storage.release(
                &expr.span,
                owner.kind.clone(),
                owner.bytes,
                "track returned vector",
            );
            owner.bytes = 0;
            owner.dynamic = Some(allocation);
            owner.vector = Some(id);
            self.storage.set_allocation(
                allocation,
                owner.kind.clone(),
                self.growth.vectors[id].bytes.clone(),
            );
        }
        Ok(Some(owner))
    }
}
