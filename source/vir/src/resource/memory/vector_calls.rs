//! Adapt vector reservation facts to the shared allocation-summary machinery.

use super::analysis::Analysis;
use super::contracts;
use super::footprint::Charge;
use super::heap::Owner;
use super::model::unsupported;
use crate::ast::*;

/// Vector facts are distinct from allocation effects, which always count bytes.
#[derive(Clone)]
pub(super) struct VectorSummary {
    /// Entry minima in elements, proved from allocation state at calls.
    pub(super) reservations: std::collections::HashMap<super::paths::InputPath, Expr>,
    /// Fresh vector capacities indexed by structural result path. Forwarded
    /// subtrees preserve the caller's existing proof state.
    pub(super) returned_capacities: std::collections::BTreeMap<super::heap::OwnerPath, Expr>,
    /// Inputs whose length may decrease; callers must invalidate append-only
    /// bounds even when removal retains no newly allocated bytes.
    pub(super) removals: std::collections::HashSet<super::paths::InputPath>,
}

/// Translate vector state to a result reservation and a generic replacement
/// effect. Fixed and runtime-sized non-vector owners need no capacity facts.
pub(super) fn summarize_result(
    function: &Function,
    owner: Option<&Owner>,
    growth: &super::growth::Growth,
    bound: &Expr,
) -> Result<(Option<Expr>, Option<Charge<Expr>>), VirErr> {
    let Some(owner) = owner else { return Ok((None, None)) };
    let retained = owner.vector.and_then(|id| {
        let state = &growth.vectors[id];
        state.backing.changed.then(|| Charge {
            kind: owner.kind.clone(),
            amount: super::growth::retained_bound(state, function, bound),
        })
    });
    if owner.input.is_some() {
        return Ok((None, retained));
    }
    if let Some(capacity) = &owner.capacity {
        let inputs = contracts::inputs(function);
        let mut in_scope = true;
        crate::ast_visitor::expr_visitor_check(capacity, &mut |_, expr| {
            if let ExprX::Var(name) = &expr.x {
                if !inputs.contains(name) {
                    in_scope = false;
                }
            }
            Ok::<(), VirErr>(())
        })?;
        if !in_scope {
            // A complete transfer descriptor can still carry the construction
            // observation. A native summary cannot grant or release these slots.
            return Ok((None, retained));
        }
    }
    Ok((owner.capacity.clone(), retained))
}

impl Analysis<'_> {
    /// Validate only the vector adapter's entry requirements and provenance.
    pub(super) fn check_vector_call(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
        imported_mutexes: &std::collections::HashSet<usize>,
    ) -> Result<(), VirErr> {
        let summary = self
            .summaries
            .get(&callee.x.name)
            .ok_or_else(|| unsupported(&expr.span, "a call without a checked function summary"))?;
        for ((index, path), required) in &summary.vectors.reservations {
            let arg = &args[*index];
            let id = self.vector_argument(arg, &callee.x.params[*index].x.typ, path)?;
            let available = self.growth.vectors[id].capacity.clone();
            let required =
                contracts::substitute(required, callee, args, &self.allocation_scalars())?;
            self.checks.push((
                expr.span.clone(),
                crate::ast_util::mk_ineq(&expr.span, &required, &available, InequalityOp::Le),
            ));
        }
        for (index, (arg, param)) in args.iter().zip(callee.x.params.iter()).enumerate() {
            if imported_mutexes.contains(&index) {
                continue;
            }
            if let Some(typ) = self.layouts.borrowed_owner(&param.x.typ) {
                for path in super::paths::vectors(self.layouts, typ, &arg.span)?.keys() {
                    self.vector_argument(arg, typ, path)?;
                }
            }
        }
        let worker_parameter = summary.worker_parameter();
        for (index, child) in &summary.vectors.removals.clone() {
            let (name, mut path) = self
                .call_location(&args[*index], &callee.x.params[*index].x.typ)
                .ok_or_else(|| unsupported(&expr.span, "removal through an aliased collection"))?;
            path.extend(child.iter().cloned());
            self.forget_collection_length(&name, &path);
            // The checked worker transformation installs the exact survivors.
            if worker_parameter == Some(*index) && child.is_empty() {
                continue;
            }
            if let Some(elements) =
                self.heap.root_mut(&name).unwrap().at_mut(&path).unwrap().elements.as_mut()
            {
                if elements.references != super::elements::References::None {
                    return Err(unsupported(
                        &expr.span,
                        "shared or worker references without a checked collection effect",
                    ));
                }
                elements.precise = false;
            }
        }
        Ok(())
    }

    /// Bind generic retained effects to the currently supported mutable owner.
    /// Other container adapters can use the same byte-effect representation.
    pub(super) fn apply_vector_call_effects(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
    ) -> Result<(), VirErr> {
        let c = &expr.span;
        let summary = &self.summaries[&callee.x.name];
        let retained = summary.allocations.retained.clone();
        let paths: std::collections::BTreeSet<_> =
            retained.keys().chain(summary.vectors.removals.iter()).cloned().collect();
        for (index, path) in paths {
            let typ = &callee.x.params[index].x.typ;
            if self.layouts.borrowed_owner(typ).is_none() {
                continue;
            }
            let (name, mut location) = self
                .call_location(&args[index], typ)
                .ok_or_else(|| unsupported(c, "a mutable vector without a tracked owner"))?;
            location.extend_from_slice(&path);
            let owner = self
                .heap
                .root(&name)
                .and_then(|root| root.at(&location))
                .ok_or_else(|| unsupported(c, "a mutable vector without a tracked owner"))?;
            let id = owner
                .vector
                .ok_or_else(|| unsupported(c, "a mutable vector without slot metadata"))?;
            let length = owner.source.as_ref().map(|_| self.owner_length(c, owner));
            let bound = retained
                .get(&(index, path))
                .map(|bound| {
                    super::allocations::instantiate(bound, callee, args, &self.allocation_scalars())
                })
                .transpose()?;
            let state = &self.growth.vectors[id];
            if let Some(length) = length {
                // The executable call supplies the final length. For an incoming
                // allocation only changes above its caller-owned entry charge
                // belong to this frame.
                let next = if state.local_constructor {
                    super::growth::slots_bytes(
                        c,
                        state.minimum.clone(),
                        length.clone(),
                        state.element,
                    )
                } else {
                    let state = state.clone();
                    let entry = self.allocation_snapshot(c, length.clone());
                    super::growth::resize_bytes(
                        c,
                        state.backing.bytes.clone(),
                        state.funded_slots(c),
                        entry,
                        length.clone(),
                        state.element,
                    )
                };
                let prior = self.growth.vectors[id].backing.bytes.clone();
                let prior = self.allocation_snapshot(c, prior);
                let allowance =
                    bound.as_ref().map_or_else(|| contracts::literal(c, 0), |b| b.amount.clone());
                let next = contracts::minimum(c, next, contracts::add(c, prior, allowance));
                let state = &mut self.growth.vectors[id];
                self.growth.after.entry(c.id).or_default().push(super::symbolic::assign(
                    c,
                    &state.backing.bytes,
                    next,
                ));
                state.removals += 1;
                state.sequence_length = Some(length);
                if bound.is_some() {
                    state.backing.changed = true;
                    state.pushes += 1;
                }
            } else if let Some(bound) = bound {
                self.retain_vector_growth(c, id, bound)?;
            }
        }
        Ok(())
    }

    /// Attach vector-specific proof facts to a generically adopted allocation.
    /// Forwarded owners already have a state identity and keep their capacity.
    pub(super) fn attach_vector_result(
        &mut self,
        span: &crate::messages::Span,
        typ: &Typ,
        owner: &mut Owner,
        capacity: Option<Expr>,
    ) -> Result<(), VirErr> {
        if !self.layouts.vector(typ) {
            return Ok(());
        }
        if owner.vector.is_none() {
            let capacity = capacity.ok_or_else(|| {
                unsupported(
                    span,
                    "a returned vector whose explicit reservation cannot be established",
                )
            })?;
            let amount = owner.extent.clone().ok_or_else(|| {
                unsupported(span, "a returned allocation without a byte-size summary")
            })?;
            let allocation = super::accounting::Accounting::fresh_allocation();
            let id = self.growth.new_vector(
                span,
                capacity.clone(),
                Charge { kind: owner.kind.clone(), amount },
                self.layouts.vector_element(typ, span)?,
                None,
                allocation,
            );
            if let Some(old) = owner.dynamic {
                self.storage.release_dynamic(old);
            }
            self.storage.release_owned(
                span,
                owner.fixed_role.take(),
                owner.kind.clone(),
                owner.bytes,
                "track returned vector",
            );
            owner.bytes = 0;
            owner.dynamic = Some(allocation);
            owner.vector = Some(id);
            owner.capacity = Some(capacity);
            self.storage.set_allocation(
                allocation,
                owner.kind.clone(),
                self.growth.vectors[id].backing.bytes.clone(),
            );
        }
        Ok(())
    }
}
