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
    capacities: &'a std::collections::BTreeMap<super::heap::OwnerPath, Expr>,
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
        if let Some(charge) = replacement(node, growth, function, bound) {
            effects.insert(path.clone(), charge);
        }
    });
    effects
}

fn replacement(
    owner: &Owner,
    growth: &super::growth::Growth,
    function: &Function,
    bound: &Expr,
) -> Option<Charge<Expr>> {
    let state = &growth.vectors[owner.vector?];
    state.backing.changed.then(|| Charge {
        kind: state.backing.kind.clone(),
        amount: super::growth::retained_bound(state, function, bound),
    })
}

/// Summarize fixed children independently. Each incoming node retains its own
/// provenance, so partial moves and replacements cannot transfer sibling charges.
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
        let mut children = std::collections::BTreeMap::new();
        for (slot, child) in &owner.children {
            path.push(slot.clone());
            children.insert(slot.clone(), node(function, child, growth, bound, path, capacities)?);
            path.pop();
        }
        if let Some(index) = owner.input {
            return Ok(ReturnedOwner::Input {
                index,
                children,
                replacement: replacement(owner, growth, function, bound),
                addition: super::elements::addition(owner, growth),
            });
        }
        let (capacity, replacement) =
            super::vector_calls::summarize_result(function, Some(owner), growth, bound)?;
        if let Some(capacity) = capacity {
            capacities.insert(path.clone(), capacity);
        }
        let elements = owner.elements.as_ref().map(super::elements::summarize);
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
            Self::Input { index, addition, children, .. } => {
                for child in children.values() {
                    child.inputs(inputs);
                }
                inputs.insert(*index);
                if let Some(effect) = addition {
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
                    &mut OwnerCall {
                        expr,
                        callee,
                        args,
                        transferred,
                        capacities: &self.summaries[&callee.x.name]
                            .vectors
                            .returned_capacities
                            .clone(),
                    },
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

    /// Apply whole-child effects after charging the call's peak. Borrowed old
    /// storage remains caller-charged throughout the call, conservatively.
    pub(super) fn apply_child_call_effects(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
        transferred: &mut [Option<Owner>],
    ) -> Result<Vec<super::transfer::checked::Assignment>, VirErr> {
        let mut inputs = Vec::new();
        for ((index, child_path), effect) in
            self.summaries[&callee.x.name].allocations.children.clone()
        {
            let (name, mut path) = super::paths::expr(&args[index], &callee.x.params[index].x.typ)
                .ok_or_else(|| unsupported(&expr.span, "an aliased child replacement argument"))?;
            path.extend(child_path.iter().cloned());
            if !super::paths::indexed(&path) {
                self.heap.check_transfer(&name, &expr.span)?;
            }
            let input = self.split_input(&expr.span, &(name.clone(), path.clone()), None)?;
            let old = self
                .heap
                .root_mut(&name)
                .and_then(|root| root.take_child(&path))
                .ok_or_else(|| unsupported(&expr.span, "a replacement without a live child"))?;
            self.release_owner(old, &expr.span);
            let mut typ = super::paths::referent(&callee.x.params[index].x.typ).clone();
            for slot in &child_path {
                typ =
                    self.layouts.owned_children(&typ, &expr.span)?.remove(slot).ok_or_else(
                        || unsupported(&expr.span, "an unknown replacement child type"),
                    )?;
            }
            if let Some(input) = input {
                inputs.push(super::transfer::checked::Assignment {
                    destination: super::transfer::checked::Place {
                        source: args[index].clone(),
                        typ: typ.clone(),
                        location: (name.clone(), path.clone()),
                    },
                    input: Some(input),
                });
            }
            let child = self.adopt_owner_tree(
                &mut OwnerCall { expr, callee, args, transferred, capacities: &effect.capacities },
                &typ,
                &effect.owner,
                &mut vec![],
            )?;
            self.heap.root_mut(&name).unwrap().replace_child(&path, child);
            self.heap.mark_replaced(&name, &path);
        }
        Ok(inputs)
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
            ReturnedOwner::Input { index, replacement, addition, .. } => {
                let owner = call.transferred[*index].take().ok_or_else(|| {
                    unsupported(&expr.span, "a returned input without transferred ownership")
                })?;
                if let Some(charge) = replacement {
                    let id = owner.vector.ok_or_else(|| {
                        unsupported(
                            &expr.span,
                            "an input replacement without tracked allocation state",
                        )
                    })?;
                    let charge =
                        allocations::instantiate(charge, callee, args, &self.stable_scalars)?;
                    self.retain_vector_growth(&expr.span, id, charge)?;
                }
                if addition.is_some() {
                    return Err(unsupported(
                        &expr.span,
                        "collection additions without a precise helper summary",
                    ));
                }
                owner
            }
            ReturnedOwner::Node { allocation, .. } => {
                let owner = if let Some(allocation) = allocation {
                    let allocation =
                        allocations::instantiate(allocation, callee, args, &self.stable_scalars)?;
                    self.returned_owner(expr, &allocation, false)?
                } else {
                    Owner::default()
                };
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
        if let ReturnedOwner::Input { children, .. } | ReturnedOwner::Node { children, .. } =
            summary
        {
            let types = self.layouts.owned_children(typ, &expr.span)?;
            for (slot, child) in children {
                let typ = types.get(slot).ok_or_else(|| {
                    unsupported(&expr.span, "an ownership summary with an unknown child")
                })?;
                path.push(slot.clone());
                owner.children.insert(slot.clone(), self.adopt_owner_tree(call, typ, child, path)?);
                path.pop();
            }
        }
        if matches!(
            summary,
            ReturnedOwner::Node { elements: Some(_), .. }
                | ReturnedOwner::Replaced { elements: Some(_), .. }
        ) {
            return Err(unsupported(
                &expr.span,
                "returned collections without a precise helper summary",
            ));
        }
        let capacity = call
            .capacities
            .get(path)
            .map(|capacity| contracts::substitute(capacity, callee, args, &self.stable_scalars))
            .transpose()?;
        self.attach_vector_result(&expr.span, typ, &mut owner, capacity, replacement)?;
        if self.layouts.cardinality(typ) && owner.source.is_none() && owner.geometry.is_none() {
            owner.geometry_known = false;
        }
        Ok(owner)
    }
}
