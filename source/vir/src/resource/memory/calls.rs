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
        eligible(callee, self.layouts)?;
        if args.len() != callee.x.params.len()
            || !crate::ast_util::types_equal(&expr.typ, &callee.x.outer_ret.x.typ)
        {
            return Err(unsupported(&expr.span, "this call signature"));
        }
        let summary = self
            .summaries
            .get(target)
            .ok_or_else(|| unsupported(&expr.span, "a call without a checked function summary"))?;
        self.open_guard_arguments(callee, args, &expr.span)?;
        // Pin the mutex's actual location before moving any guard argument.
        // Callee profiles and post-call writes use this same acquisition.
        let mut borrowed = std::collections::HashMap::new();
        let mut imported_mutexes = std::collections::HashSet::new();
        for (index, (arg, parameter)) in args.iter().zip(callee.x.params.iter()).enumerate() {
            if parameter.x.mode == Mode::Exec {
                if let Some(typ) = self.layouts.borrowed_descriptor(&parameter.x.typ) {
                    let Some(location) = self.call_location(arg, &typ) else {
                        if self.imported_mutex_argument(summary, index, arg, &typ)? {
                            imported_mutexes.insert(index);
                            continue;
                        }
                        return Err(unsupported(&arg.span, "this borrowed owner argument"));
                    };
                    borrowed.insert(
                        index,
                        super::transfer::checked::Place {
                            source: arg.clone(),
                            typ: typ.clone(),
                            location,
                        },
                    );
                }
            }
        }
        let call_scalars = self.allocation_scalars();
        // Original borrowed regions stay with their shared root through a
        // lock-only guard return or a checked update published at unlock.
        let internal = summary
            .closed_mutex
            .map(|(parameter, _)| parameter)
            .filter(|index| imported_mutexes.contains(index));
        let shared_inputs = internal.is_some()
            || !imported_mutexes.is_empty()
                && borrowed.is_empty()
                && summary.returns_guard_without_payload_transfer();
        let transfer =
            if shared_inputs { None } else { self.prepare_transfer_call(expr, callee, args)? };
        let covered = borrowed
            .keys()
            .filter_map(|&index| {
                let Some(super::synchronization::local::View::Guard(interval)) =
                    self.synchronization_view(&args[index])
                else {
                    return None;
                };
                // Fixed child replacements use their checked native ownership
                // summary. Runtime mutations require the specialized forest.
                let complete = !summary.modified_parameters.contains(&index)
                    || transfer.is_some()
                    || summary
                        .allocations
                        .children
                        .keys()
                        .any(|(parameter, _)| *parameter == index);
                complete.then_some(interval)
            })
            .collect();
        self.check_vector_call(expr, callee, args, &imported_mutexes, internal)?;
        let result_size = self.layouts.return_size(&expr.typ, &expr.span)?;
        let bound = super::contracts::instantiate(
            callee,
            args,
            &call_scalars,
            self.budgets,
            self.functions,
            self.layouts,
            false,
        )
        .unwrap_or_else(|_| super::contracts::literal(&expr.span, envelope));
        let holder_arguments = self.call_holders(expr, args, summary.effects.as_deref());
        let argument_revision = self.growth.revision();
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
                let mut value = self.fresh_value(&arg.span, &arg.typ)?;
                value.synchronization_view = self.synchronization_place(place);
                value
            } else {
                self.produce(arg)?
            };
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
        let mut synchronization = super::synchronization::helpers::Call::instantiate(
            self,
            expr,
            summary,
            &values,
            &transferred,
        )?;
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
        let callee_effects = summary.effects.as_deref();

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
                synchronization_view: None,
                environment: None,
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
        let frames =
            self.storage.call_frames(c, &transferred, &self.growth.elements, &result_ids)?;
        let allowance =
            Footprint::allowance(bound.clone()).remove(c, MemoryKind::host_local(), credit.clone());
        let allowance_condition =
            synchronization.as_ref().map(|call| call.allowance(&summary.profiles));
        for frame in &frames {
            frame.observe(
                &mut self.storage,
                c,
                allowance.clone(),
                None,
                &result_ids,
                None,
                allowance_condition.as_ref().zip(synchronization.as_deref()),
            )?;
        }
        for (index, point) in summary.profiles.iter().enumerate() {
            let cost = point
                .cost
                .map(c, &|cost| super::contracts::substitute(cost, callee, args, &call_scalars))
                .unwrap_or_else(|_| Footprint::allowance(bound.clone()))
                .limit(c, bound.clone());
            let cost = if point.result {
                cost.remove(c, MemoryKind::host_local(), credit.clone())
            } else {
                cost
            };
            let condition = synchronization.as_ref().map(|call| call.condition(&point.condition));
            let results = point.result.then_some(&result_ids);
            let start = self.storage.points().len();
            for frame in &frames {
                frame.observe(
                    &mut self.storage,
                    c,
                    cost.clone(),
                    (!shared_inputs).then_some((&point.inputs, transfer.as_ref())),
                    results.unwrap_or(&Default::default()),
                    Some(index),
                    condition.as_ref().zip(synchronization.as_deref()),
                )?;
            }
            if !holder_arguments.is_empty()
                && let Some(phase) = callee_effects.and_then(|effects| effects.points.get(index))
            {
                let actuals = phase
                    .holders
                    .iter()
                    .filter_map(|i| holder_arguments.get(i).copied())
                    .collect::<Vec<_>>();
                self.storage.mark_holders(start, &actuals);
            }
        }
        // The callee phases already describe destruction of moved-in guards.
        // Retiring their old caller storage must not execute the destructor again.
        if let Some(call) = &synchronization {
            for owner in transferred.iter_mut().flatten() {
                if let Some(super::synchronization::local::Owned::Guard(id)) = owner.synchronization
                    && call.consumed().any(|consumed| consumed == id)
                {
                    owner.synchronization = None;
                }
            }
        }
        let result_sync = synchronization
            .as_ref()
            .and_then(|call| summary.synchronized_result.map(|owner| call.result(owner)));
        if let Some(call) = &synchronization {
            self.storage.commit_call_intervals(c, call, result_sync)?;
        }
        let mut replaced_inputs = Vec::new();
        if let Some(parameter) = internal {
            let call = synchronization.as_mut().expect("checked mutex acquisition");
            self.publish_internal_section(expr, callee, args, summary, parameter, call)?;
            self.result_owner = None;
        } else if let Some(transfer) = transfer {
            self.result_owner = self.apply_transfer_call(
                expr,
                callee,
                args,
                transfer,
                &borrowed,
                &mut transferred,
            )?;
        } else {
            self.apply_vector_call_effects(expr, callee, args)?;
            replaced_inputs =
                self.apply_child_call_effects(expr, callee, args, &borrowed, &mut transferred)?;
            self.result_owner =
                self.complete_ownership_call(expr, callee, args, &mut transferred)?;
        }
        if let Some(sync) = result_sync {
            self.result_owner
                .as_mut()
                .ok_or_else(|| unsupported(c, "missing synchronization result owner"))?
                .synchronization = Some(sync);
        }
        self.record_element_updates(c)?;
        if let Some(call) = &synchronization {
            self.publish_consumed_payloads(call, &covered, result_sync, c)?;
        }
        self.storage.record_call_exit(c, &self.growth);
        self.produced = result;
        let retained = if destination { 0 } else { result_size };
        let origins = self.transitions.call_origins.remove(&expr.span.id).unwrap_or_default();
        self.transitions.operation(
            &expr.span,
            super::transfer::checked::Operation::Call {
                budget: bound.clone(),
                target: target.clone(),
                returned: self
                    .storage
                    .returned_storage(self.result_owner.as_ref(), &self.growth.elements),
                synchronization,
                args: args.clone(),
                borrowed,
                replaced_inputs,
                origins,
                modified: self.summaries[target].modified_parameters.clone(),
            },
        );
        self.calls.push((target.clone(), expr.span.clone()));
        Ok(retained)
    }

    pub(super) fn call_expr(&mut self, expr: &Expr, destination: bool) -> Result<u64, VirErr> {
        if let Some(bytes) = self.imported_leaf_call(expr, destination)? {
            return Ok(bytes);
        }
        if let Some(bytes) = self.atomic_call(expr, destination)? {
            return Ok(bytes);
        }
        if let Some(value) = self.extract_worker_result(expr)? {
            if let Some(owner) = self.result_owner.take() {
                self.release_owner(owner, &expr.span);
            }
            return self.expression_value(value, &expr.span);
        }
        if self.worker_result_predicate(expr)? {
            return Ok(0);
        }
        if let Some(value) = self.join_worker(expr)? {
            if let Some(owner) = self.result_owner.take() {
                self.release_owner(owner, &expr.span);
            }
            return self.expression_value(value, &expr.span);
        }
        if self.guard_access(expr)? || self.shared_borrow(expr)? {
            return Ok(0);
        }
        if let Some(bytes) = self.iterator_call(expr, destination)? {
            return Ok(bytes);
        }
        let focused = if let ExprX::Call { args, .. } = &expr.x {
            self.focus_arguments(args, &expr.span)?
        } else {
            Vec::new()
        };
        let bytes = self.call_expr_inner(expr, destination)?;
        self.finish_projections(&expr.span, focused)?;
        Ok(bytes)
    }

    /// Preserve the array's length when the checked coercion creates a slice.
    fn record_array_slice(&mut self, expr: &Expr, source: &Expr, array: &Typ) {
        let TypX::Primitive(Primitive::Array, types) = &**array else { unreachable!() };
        let TypX::ConstInt(length) = &*types[1] else { unreachable!() };
        let length = SpannedTyped::new(
            &expr.span,
            &crate::ast_util::int_typ(),
            ExprX::Const(crate::ast_util::const_int_from_string(length.to_string())),
        );
        self.transitions.operation(
            &expr.span,
            super::transfer::checked::Operation::ArraySlice { source: source.clone(), length },
        );
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
                self.transitions.operation(
                    &expr.span,
                    super::transfer::checked::Operation::SliceLength { receiver: args[0].clone() },
                );
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
                    self.record_array_slice(expr, value, array);
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
                if matches!(&*expr.typ, TypX::Decorate(TypDecoration::Ref, None, _)) {
                    self.record_array_slice(expr, &args[0], from);
                }
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
