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
    if let Some(id) = owner.vector {
        if growth.vectors[id].backing.changed {
            return Ok((
                owner.input.is_none().then(|| contracts::literal(&function.span, 0)),
                Some(Charge {
                    kind: owner.kind.clone(),
                    amount: super::growth::retained_bound(&growth.vectors[id], function, bound),
                }),
            ));
        }
    }
    if owner.input.is_some() {
        return Ok((None, None));
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
            return Ok((Some(contracts::literal(&function.span, 0)), None));
        }
    }
    Ok((owner.capacity.clone(), None))
}

impl Analysis<'_> {
    /// Validate only the vector adapter's entry requirements and provenance.
    pub(super) fn check_vector_call(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
    ) -> Result<(), VirErr> {
        let summary = self
            .summaries
            .get(&callee.x.name)
            .ok_or_else(|| unsupported(&expr.span, "a call without a checked function summary"))?;
        for ((index, path), required) in &summary.vectors.reservations {
            let arg = &args[*index];
            let id = self.vector_argument(arg, &callee.x.params[*index].x.typ, path)?;
            let available = self.growth.vectors[id].capacity.clone();
            let required = contracts::substitute(required, callee, args, &self.stable_scalars)?;
            self.checks.push((
                expr.span.clone(),
                crate::ast_util::mk_ineq(&expr.span, &required, &available, InequalityOp::Le),
            ));
        }
        for (arg, param) in args.iter().zip(callee.x.params.iter()) {
            if let Some(typ) = self.layouts.borrowed_owner(&param.x.typ) {
                for path in super::paths::vectors(self.layouts, typ, &arg.span)?.keys() {
                    self.vector_argument(arg, typ, path)?;
                }
            }
        }
        for (index, child) in &summary.vectors.removals.clone() {
            let (name, mut path) =
                super::paths::expr(&args[*index], &callee.x.params[*index].x.typ).ok_or_else(
                    || unsupported(&expr.span, "removal through an aliased collection"),
                )?;
            path.extend(child.iter().cloned());
            self.forget_collection_length(&name, &path);
            if let Some(elements) =
                self.heap.root_mut(&name).unwrap().at_mut(&path).unwrap().elements.as_mut()
            {
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
        for ((index, path), bound) in &self.summaries[&callee.x.name].allocations.retained.clone() {
            let id = self.vector_argument(&args[*index], &callee.x.params[*index].x.typ, path)?;
            let bound = super::allocations::instantiate(bound, callee, args, &self.stable_scalars)?;
            if self.growth.section_protected.contains(&id)
                && super::contracts::constant(&bound.amount) != Some(0)
            {
                return Err(unsupported(
                    c,
                    "growing an enclosing vector through a helper inside a memory section",
                ));
            }
            self.retain_vector_growth(c, id, bound)?;
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
        replacement: Option<Charge<Expr>>,
    ) -> Result<(), VirErr> {
        if !self.layouts.vector(typ) {
            if replacement.is_some() {
                return Err(unsupported(span, "a replacement effect without a container adapter"));
            }
            return Ok(());
        }
        if owner.vector.is_none() {
            let capacity = capacity
                .ok_or_else(|| unsupported(span, "a returned vector without a capacity summary"))?;
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
            self.storage.release(span, owner.kind.clone(), owner.bytes, "track returned vector");
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
        if let Some(replacement) = replacement {
            self.retain_vector_growth(span, owner.vector.unwrap(), replacement)?;
        }
        Ok(())
    }
}
