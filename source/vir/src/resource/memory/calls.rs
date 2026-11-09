//! Direct-call composition and compiler-identified resource intrinsics.

use super::analysis::Analysis;
use super::footprint::{Footprint, MemoryKind};
use super::model::{eligible, slice, unsupported};
use crate::ast::*;

impl Analysis<'_> {
    fn call(
        &mut self,
        expr: &Expr,
        target: &Fun,
        args: &Exprs,
        destination: bool,
    ) -> Result<u64, VirErr> {
        let callee = self.functions.get(target).ok_or_else(|| {
            unsupported(
                &expr.span,
                "calls outside this crate; imported memory summaries are not supported",
            )
        })?;
        let Some(&envelope) = self.budgets.get(target) else {
            return Err(unsupported(&expr.span, "calls without a current-model memory contract")
                .secondary_span(&callee.span));
        };
        eligible(callee)?;
        if args.len() != callee.x.params.len()
            || !crate::ast_util::types_equal(&expr.typ, &callee.x.outer_ret.x.typ)
        {
            return Err(unsupported(&expr.span, "this call signature"));
        }
        self.check_vector_call(expr, callee, args)?;
        let result_size = self.layouts.return_size(&expr.typ, &expr.span)?;
        let bound = super::contracts::instantiate(
            callee,
            args,
            &self.stable_scalars,
            self.budgets,
            self.functions,
            self.layouts,
            false,
        )
        .unwrap_or_else(|_| super::contracts::literal(&expr.span, envelope));
        let argument_revision = self.growth.revision();
        let mut parameters = 0u64;
        let mut values = vec![None; args.len()];
        let mut transferred = vec![None; args.len()];
        for (index, (arg, param)) in args.iter().zip(callee.x.params.iter()).enumerate() {
            if param.x.mode != Mode::Exec {
                continue;
            }
            if !crate::ast_util::types_equal(&arg.typ, &param.x.typ) {
                return Err(unsupported(&arg.span, "this call argument coercion"));
            }
            let value = if let ExprX::TwoPhaseBorrowMut(place) = &arg.x {
                self.borrow(place, &arg.typ)?;
                self.fresh_value(&arg.span, &arg.typ)?
            } else {
                self.produce(arg)?
            };
            parameters = parameters
                .checked_add(value.bytes)
                .ok_or_else(|| unsupported(&expr.span, "parameter storage exceeding u64"))?;
            values[index] = Some(value);
            if self.layouts.owner(&param.x.typ) {
                transferred[index] = Some(
                    self.result_owner
                        .take()
                        .ok_or_else(|| unsupported(&arg.span, "missing argument ownership"))?,
                );
            }
        }
        if argument_revision != self.growth.revision() {
            return Err(unsupported(
                &expr.span,
                "vector allocation changes inside call arguments; bind the arguments first",
            ));
        }
        // Match the callee's provenance IDs to disjoint caller allocation nodes.
        let mut nodes = std::collections::HashMap::new();
        for (parameter, owner) in transferred.into_iter().enumerate() {
            if let Some(owner) = owner {
                let mut tree = std::collections::BTreeMap::new();
                owner.flatten(&mut vec![], &mut tree);
                nodes.extend(tree.into_iter().map(|(path, node)| ((parameter, path), node)));
            }
        }
        let mut transferred = Vec::new();
        for path in &self.summaries[target].input_paths {
            transferred.push(Some(nodes.remove(path).ok_or_else(|| {
                unsupported(&expr.span, "a call with an incomplete owning input")
            })?));
        }
        if !nodes.is_empty() {
            return Err(unsupported(&expr.span, "unmatched input allocation nodes"));
        }
        let c = &expr.span;
        let mut base = self.storage.live_expression(c).remove(
            c,
            MemoryKind::host_local(),
            super::contracts::literal(c, parameters),
        );
        let mut input_costs = vec![Footprint::zero(c); transferred.len()];
        let mut external_inputs = std::collections::HashSet::new();
        for (index, owner) in transferred.iter().enumerate() {
            if let Some(owner) = owner {
                for (kind, cost) in self.owner_charges(c, owner) {
                    base = base.remove(c, kind.clone(), cost.clone());
                    input_costs[index] = input_costs[index].add(c, Footprint::charge(kind, cost));
                }
                external_inputs.extend(owner.inputs());
            }
        }
        let summary = self
            .summaries
            .get(target)
            .ok_or_else(|| unsupported(&expr.span, "a call without a checked function summary"))?;
        let forwarded = summary.return_parameter.and_then(|i| values[i].clone());
        for value in values.into_iter().flatten() {
            self.release_value(value, c);
        }
        // Materialize the returned value only after the call's work. The checked
        // profile below describes its presence during the call itself.
        let mut result = if destination {
            None
        } else {
            let id = self.storage.reserve_value_unchecked(MemoryKind::host_local(), result_size);
            Some(super::lifetime::Value {
                bytes: result_size,
                ids: [id].into_iter().collect(),
                origins: [id].into_iter().collect(),
                parameter: None,
            })
        };
        if let (Some(result), Some(forwarded)) = (&mut result, forwarded) {
            result.parameter = forwarded.parameter;
            result.origins.extend(forwarded.origins);
        }
        let result_ids = result.as_ref().map(|v| v.ids.clone()).unwrap_or_default();
        let credit = super::contracts::literal(c, if destination { result_size } else { 0 });
        // Contract slack remains available to the caller. Input allocations are
        // accounted separately using their checked lifetimes in the body.
        let allowance = base.add(
            c,
            Footprint::allowance(bound.clone()).remove(c, MemoryKind::host_local(), credit.clone()),
        );
        self.storage.call_cost(c, allowance, &external_inputs, &result_ids, true);
        let profiles = &self.summaries[target].profiles;
        for point in profiles {
            let cost = point
                .cost
                .map(c, &|cost| {
                    super::contracts::substitute(cost, callee, args, &self.stable_scalars)
                })
                .unwrap_or_else(|_| Footprint::allowance(bound.clone()));
            let mut cost = cost.limit(c, bound.clone());
            let mut excluded = external_inputs.clone();
            for index in &point.inputs {
                cost = cost.add(c, input_costs[*index].clone());
                if let Some(owner) = &transferred[*index] {
                    for input in owner.inputs() {
                        excluded.remove(&input);
                    }
                }
            }
            if point.result {
                cost = cost.remove(c, MemoryKind::host_local(), credit.clone());
            }
            self.storage.call_cost(c, base.add(c, cost), &excluded, &result_ids, point.result);
        }
        self.apply_vector_call_effects(expr, callee, args)?;
        self.apply_collection_call_effects(expr, callee, args, &mut transferred)?;
        self.apply_child_call_effects(expr, callee, args, &mut transferred)?;
        self.result_owner = self.complete_ownership_call(expr, callee, args, &mut transferred)?;
        self.record_element_updates(c)?;
        self.produced = result;
        let retained = if destination { 0 } else { result_size };
        self.calls.push((target.clone(), expr.span.clone()));
        Ok(retained)
    }

    pub(super) fn call_expr(&mut self, expr: &Expr, destination: bool) -> Result<u64, VirErr> {
        let focused = if let ExprX::Call { args, .. } = &expr.x {
            self.focus_arguments(args, &expr.span)?
        } else {
            Vec::new()
        };
        let bytes = self.call_expr_inner(expr, destination)?;
        self.finish_projections(&expr.span, focused)?;
        Ok(bytes)
    }

    fn call_expr_inner(&mut self, expr: &Expr, destination: bool) -> Result<u64, VirErr> {
        let operands;
        match &expr.x {
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
                args,
                post_args: None,
                body: None,
            } if attrs.resource_intrinsic == Some(ResourceIntrinsic::SliceLen)
                && args.len() == 1 =>
            {
                if !matches!(&*args[0].typ, TypX::Decorate(TypDecoration::Ref, None, inner) if slice(inner))
                {
                    return Err(unsupported(&expr.span, "length of this slice type"));
                }
                // Validate the receiver; length evaluation creates no source slot.
                operands = self.expr(&args[0])?;
            }
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
                args,
                post_args: None,
                body: None,
            } if attrs.resource_intrinsic == Some(ResourceIntrinsic::ArrayUnsize)
                && args.len() == 1 =>
            {
                // Shared unsizing may lower through a helper adapter that
                // borrows a temporary thin reference, producing &&[T; N].
                // Admit only this exact, nonescaping adapter shape. Evaluate
                // the inner reference normally so borrowed backing temporaries
                // still fail. Compiler adapters do not create source storage.
                if let TypX::Decorate(TypDecoration::Ref, None, inner) = &*args[0].typ
                    && let TypX::Decorate(TypDecoration::Ref, None, array) = &**inner
                    && matches!(&**array, TypX::Primitive(Primitive::Array, _))
                    && matches!(&*expr.typ, TypX::Decorate(TypDecoration::Ref, None, to) if slice(to))
                    && let ExprX::ReadPlace(place, kind) = &args[0].x
                    && matches!(kind.preliminary_kind, ReadKind::ImmutBor)
                    && let PlaceX::Temporary(value) = &place.x
                    && crate::ast_util::types_equal(&value.typ, inner)
                {
                    self.layouts.size(array, &expr.span)?;
                    self.discard(value)?;
                    self.layouts.size(&expr.typ, &expr.span)?;
                    return Ok(0);
                }
                let (from, to) = match (&*args[0].typ, &*expr.typ) {
                    (TypX::MutRef(from), TypX::MutRef(to)) => (from, to),
                    (
                        TypX::Decorate(TypDecoration::Ref, None, from),
                        TypX::Decorate(TypDecoration::Ref, None, to),
                    ) => (from, to),
                    _ => return Err(unsupported(&expr.span, "this array-to-slice coercion")),
                };
                if !matches!(&**from, TypX::Primitive(Primitive::Array, _)) || !slice(to) {
                    return Err(unsupported(&expr.span, "this array-to-slice coercion"));
                }
                self.layouts.size(from, &expr.span)?;
                // Coercion uses the destination reference's storage. Backing
                // array storage stays with its original owner.
                operands = self.expr(&args[0])?;
            }
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, target, typs, impls, attrs),
                args,
                post_args: None,
                body: None,
            } if typs.is_empty() && impls.is_empty() && !attrs.const_var => {
                return self.call(expr, target, args, destination);
            }
            _ => {
                return Err(unsupported(
                    &expr.span,
                    "calls with generic, dynamic, or unsupported targets",
                ));
            }
        }
        self.result(expr, operands)
    }
}
