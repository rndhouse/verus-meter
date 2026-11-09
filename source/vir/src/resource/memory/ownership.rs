//! Apply checked allocation summaries across owning calls.
//!
//! Constructors supply byte expressions and memory kinds. Returned allocations
//! are transferred or adopted without reconstructing byte extents from layouts.

use super::allocations::{self, ReturnedOwner};
use super::analysis::Analysis;
use super::contracts;
use super::footprint::Charge;
use super::heap::Owner;
use super::model::unsupported;
use crate::ast::*;

/// Call inputs remain available until recursive result adoption has selected
/// every subtree that survives. All nodes share the same scalar substitution.
struct OwnerCall<'a> {
    expr: &'a Expr,
    callee: &'a Function,
    args: &'a Exprs,
    transferred: &'a mut [Option<Owner>],
}

/// Effects within one forwarded or borrowed subtree. Paths are relative to its
/// root, so nesting an input under a new owner preserves the same transitions.
pub(super) fn replacements(
    owner: &Owner,
    growth: &super::growth::Growth,
    function: &Function,
    bound: &Expr,
) -> std::collections::BTreeMap<super::heap::OwnerPath, Charge<Expr>> {
    let mut effects = std::collections::BTreeMap::new();
    owner.visit_paths(&mut vec![], &mut |path, node| {
        if let Some(id) = node.vector {
            let state = &growth.vectors[id];
            if state.backing.changed {
                effects.insert(
                    path.clone(),
                    Charge {
                        kind: state.backing.kind.clone(),
                        amount: super::growth::retained_bound(state, function, bound),
                    },
                );
            }
        }
    });
    effects
}

/// Summarize each fixed child independently. Whole incoming subtrees retain
/// provenance; fresh nodes carry only their own allocation, excluding children.
pub(super) fn summarize(
    function: &Function,
    owner: Option<&Owner>,
    growth: &super::growth::Growth,
    bound: &Expr,
) -> Result<(Option<ReturnedOwner>, std::collections::BTreeMap<super::heap::OwnerPath, Expr>), VirErr>
{
    fn node(
        function: &Function,
        owner: &Owner,
        growth: &super::growth::Growth,
        bound: &Expr,
        path: &mut super::heap::OwnerPath,
        capacities: &mut std::collections::BTreeMap<super::heap::OwnerPath, Expr>,
    ) -> Result<ReturnedOwner, VirErr> {
        if let Some(index) = owner.input {
            return Ok(ReturnedOwner::Input {
                index,
                replacements: replacements(owner, growth, function, bound),
                additions: super::elements::additions(owner, growth, bound, function),
            });
        }
        let (capacity, replacement) =
            super::vector_calls::summarize_result(function, Some(owner), growth, bound)?;
        if let Some(capacity) = capacity {
            capacities.insert(path.clone(), capacity);
        }
        let elements = owner
            .elements
            .as_ref()
            .map(|elements| super::elements::summarize(elements, growth, bound, function));
        if let Some(allocation) = replacement {
            return Ok(ReturnedOwner::Replaced { allocation, elements });
        }
        let allocation = if let Some(amount) = &owner.extent {
            let inputs = contracts::inputs(function);
            let mut in_scope = true;
            crate::ast_visitor::expr_visitor_check(amount, &mut |_, expr| {
                if let ExprX::Var(name) = &expr.x {
                    in_scope &= inputs.contains(name);
                }
                Ok::<(), VirErr>(())
            })?;
            // A locally charged node is bounded by the checked peak. Children
            // are summarized separately, so a fallback may conservatively overcount.
            Some(Charge {
                kind: owner.kind.clone(),
                amount: if in_scope { amount.clone() } else { bound.clone() },
            })
        } else {
            None
        };
        let mut children = std::collections::BTreeMap::new();
        for (slot, child) in &owner.children {
            path.push(slot.clone());
            children.insert(slot.clone(), node(function, child, growth, bound, path, capacities)?);
            path.pop();
        }
        Ok(ReturnedOwner::Node { allocation, children, elements })
    }
    let mut capacities = std::collections::BTreeMap::new();
    let returned = owner
        .map(|owner| node(function, owner, growth, bound, &mut vec![], &mut capacities))
        .transpose()?;
    Ok((returned, capacities))
}

impl ReturnedOwner {
    /// Inputs can survive anywhere in the result, including under newly allocated boxes.
    fn inputs(&self, inputs: &mut std::collections::HashSet<usize>) {
        match self {
            Self::Input { index, additions, .. } => {
                inputs.insert(*index);
                for effect in additions.values() {
                    inputs.extend(&effect.inputs);
                }
            }
            Self::Node { children, elements, .. } => {
                if let Some(elements) = elements {
                    inputs.extend(&elements.inputs);
                }
                for child in children.values() {
                    child.inputs(inputs);
                }
            }
            Self::Replaced { elements, .. } => {
                if let Some(elements) = elements {
                    inputs.extend(&elements.inputs);
                }
            }
        }
    }
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
            // Sibling result allocations share a call span, but never an identity.
            let id = super::accounting::Accounting::fresh_allocation();
            self.storage.set_allocation(id, allocation.kind.clone(), allocation.amount.clone());
            self.storage.record_live(&expr.span)?;
            owner.dynamic = Some(id);
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
        let mut retained = std::collections::HashSet::new();
        if let Some(summary) = &summary {
            summary.inputs(&mut retained);
        }
        // Release consumed inputs before adopting fresh result allocations.
        for (index, input) in transferred.iter_mut().enumerate() {
            if !retained.contains(&index) {
                if let Some(owner) = input.take() {
                    self.release_owner(owner, &expr.span);
                }
            }
        }
        let result = summary
            .map(|summary| {
                self.adopt_owner_tree(
                    &mut OwnerCall { expr, callee, args, transferred },
                    &expr.typ,
                    &summary,
                    &mut vec![],
                )
            })
            .transpose()?;
        if transferred.iter().any(Option::is_some) {
            return Err(unsupported(&expr.span, "unconsumed ownership summary inputs"));
        }
        Ok(result)
    }

    fn adopt_owner_tree(
        &mut self,
        call: &mut OwnerCall<'_>,
        typ: &Typ,
        summary: &ReturnedOwner,
        path: &mut super::heap::OwnerPath,
    ) -> Result<Owner, VirErr> {
        let OwnerCall { expr, callee, args, .. } = *call;
        let mut replacement = None;
        let mut owner = match summary {
            ReturnedOwner::Input { index, replacements, additions } => {
                let mut owner = call.transferred[*index].take().ok_or_else(|| {
                    unsupported(&expr.span, "a returned input without transferred ownership")
                })?;
                for (path, charge) in replacements {
                    let id = owner.at(path).and_then(|node| node.vector).ok_or_else(|| {
                        unsupported(
                            &expr.span,
                            "an input replacement without tracked allocation state",
                        )
                    })?;
                    let charge =
                        allocations::instantiate(charge, callee, args, &self.stable_scalars)?;
                    self.retain_vector_growth(&expr.span, id, charge)?;
                }
                for (path, effect) in additions {
                    let elements =
                        owner.at_mut(path).and_then(|owner| owner.elements.as_mut()).ok_or_else(
                            || unsupported(&expr.span, "an input collection without child state"),
                        )?;
                    self.apply_element_summary(
                        &expr.span,
                        elements,
                        effect,
                        callee,
                        args,
                        call.transferred,
                    )?;
                }
                owner
            }
            ReturnedOwner::Node { allocation, children, .. } => {
                let mut owner = if let Some(allocation) = allocation {
                    let allocation =
                        allocations::instantiate(allocation, callee, args, &self.stable_scalars)?;
                    self.returned_owner(expr, &allocation, false)?
                } else {
                    Owner::default()
                };
                let types = self.layouts.owned_children(typ, &expr.span)?;
                for (slot, child) in children {
                    let typ = types.get(slot).ok_or_else(|| {
                        unsupported(&expr.span, "an ownership summary with an unknown child")
                    })?;
                    path.push(slot.clone());
                    owner
                        .children
                        .insert(slot.clone(), self.adopt_owner_tree(call, typ, child, path)?);
                    path.pop();
                }
                owner
            }
            ReturnedOwner::Replaced { allocation, .. } => {
                let allocation =
                    allocations::instantiate(allocation, callee, args, &self.stable_scalars)?;
                let owner = self.returned_owner(expr, &allocation, true)?;
                replacement = Some(allocation);
                owner
            }
        };
        if let ReturnedOwner::Node { elements: Some(summary), .. }
        | ReturnedOwner::Replaced { elements: Some(summary), .. } = summary
        {
            owner.elements =
                Some(self.adopt_elements(&expr.span, summary, callee, args, call.transferred)?);
        }
        let capacity = self.summaries[&callee.x.name]
            .vectors
            .returned_capacities
            .get(path)
            .map(|capacity| contracts::substitute(capacity, callee, args, &self.stable_scalars))
            .transpose()?;
        self.attach_vector_result(&expr.span, typ, &mut owner, capacity, replacement)?;
        Ok(owner)
    }
}
