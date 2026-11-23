//! Borrow, publish and resume an acquisition-relative payload at a source
//! branch or checked call, using the same charged tree as a direct guard access.
use super::*;
use crate::resource::memory::{
    summary::FunctionSummary,
    synchronization::{helpers::Call, local::View, optional::GuardOption},
};

impl FunctionSummary {
    /// When every borrowed owner is an untouched imported mutex, all original
    /// input lifetimes stay with those mutexes. Fresh scratch and call allowance
    /// are still observed at their normal phases, including inside nested calls.
    pub(in crate::resource::memory) fn returns_guard_without_payload_transfer(&self) -> bool {
        self.input_paths.is_empty()
            && self.modified_parameters.is_empty()
            && self.synchronized_result.and_then(Owned::interval).is_some()
            && self.effects.as_ref().is_some_and(|body| !body.ownership.retained_workers)
            && (self.transfer.is_some()
                || (!self.transfer_required && self.profiles.iter().all(|p| p.inputs.is_empty())))
    }
}

impl Analysis<'_> {
    /// Bind an imported mutex without reading its contents before acquisition.
    /// A payload update needs a checked release interface on this parameter.
    pub(in crate::resource::memory) fn imported_mutex_argument(
        &self,
        summary: &FunctionSummary,
        index: usize,
        arg: &Expr,
        typ: &Typ,
    ) -> Result<bool, VirErr> {
        let Some(View::Mutex(instance)) = self.synchronization_view(arg) else { return Ok(false) };
        let Some(payload) = self.layouts.mutex_payload(typ) else { return Ok(false) };
        let Some(effects) = &summary.effects else { return Ok(false) };
        let formal = crate::resource::memory::synchronization::Instance::Input(index);
        if effects.ownership.synchronization_inputs.input_view(index) != Some(View::Mutex(formal))
            || self.heap.shared.imported_mutex(instance, payload, &arg.span)?.is_none()
        {
            return Ok(false);
        }
        if summary.closed_mutex.is_none_or(|(parameter, _)| parameter != index)
            && (summary.modified_parameters.contains(&index)
                || effects.ownership.payload_borrows().iter().any(|id| id.instance == formal))
        {
            return Err(unsupported(
                &arg.span,
                "a helper accessing shared mutex contents without an acquisition-relative ownership interface",
            ));
        }
        Ok(true)
    }

    pub(in crate::resource::memory) fn open_guard_arguments(
        &mut self,
        callee: &Function,
        args: &Exprs,
        site: &Span,
    ) -> Result<(), VirErr> {
        if self.current_worker.is_none() {
            return Ok(());
        }
        for (param, arg) in
            callee.x.params.iter().zip(args.iter()).filter(|(p, _)| p.x.mode == Mode::Exec)
        {
            match self.synchronization_view(arg) {
                Some(View::Guard(interval)) => {
                    if let Some(typ) = self.layouts.writable_guard_payload(&param.x.typ) {
                        self.open_imported_payload(interval, typ, site)?;
                    }
                }
                Some(View::Payload(interval)) => self.open_imported_payload(
                    interval,
                    crate::resource::memory::paths::referent(&param.x.typ),
                    site,
                )?,
                _ => {}
            }
        }
        Ok(())
    }

    /// A guard already held at a control split sees the same incoming contents
    /// on either arm. Materialize that input at their common dominator if an
    /// arm uses the guard. A guard acquired inside an arm is still opened there.
    pub(in crate::resource::memory) fn open_branch_payloads(
        &mut self,
        arms: impl Iterator<Item = Expr>,
        site: &Span,
    ) -> Result<(), VirErr> {
        if self.current_worker.is_none() || self.heap.shared.is_empty() {
            return Ok(());
        }
        let mut inputs = BTreeMap::new();
        for arm in arms {
            crate::ast_visitor::expr_visitor_check(&arm, &mut |_, value| {
                if let Some(View::Payload(interval)) = self.synchronization_view(value) {
                    inputs.insert(
                        interval,
                        crate::resource::memory::paths::referent(&value.typ).clone(),
                    );
                } else if let ExprX::Call {
                    target: CallTarget::Fun(_, target, _, _, _), args, ..
                } = &value.x
                    && let Some(callee) = self.functions.get(target)
                {
                    for (parameter, actual) in callee.x.params.iter().zip(args.iter()) {
                        if let Some(payload) = self.layouts.writable_guard_payload(&parameter.x.typ)
                            && let Some(View::Guard(interval)) = self.synchronization_view(actual)
                        {
                            inputs.insert(interval, payload.clone());
                        }
                    }
                }
                Ok::<(), VirErr>(())
            })?;
        }
        for (interval, payload) in inputs {
            if self.storage.holds_interval(interval) {
                self.open_imported_payload(interval, &payload, site)?;
            }
        }
        Ok(())
    }

    /// End an already-open view when a checked helper drops the moved guard.
    /// The specialized exit tree includes all writes via this acquisition.
    /// Distinct-input checks exclude subsequent writes via a mutex alias.
    pub(in crate::resource::memory) fn publish_consumed_payloads(
        &mut self,
        call: &Call,
        covered: &std::collections::BTreeSet<Interval>,
        result: Option<Owned>,
        site: &Span,
    ) -> Result<(), VirErr> {
        let mut proofs = Vec::new();
        for interval in call.consumed() {
            let conditional =
                result == Some(Owned::GuardOption(GuardOption::Conditional(interval)));
            if (!conditional && result.and_then(Owned::interval) == Some(interval))
                || !self.heap.borrowed.contains_key(&interval.payload_name())
            {
                continue;
            }
            if call.payload_borrows.contains(&interval) && !covered.contains(&interval) {
                return Err(unsupported(
                    site,
                    "a consuming helper without its release-time payload",
                ));
            }
            let view = self.publish_imported_payload(interval, site, &mut proofs);
            if conditional && let Some(view) = view {
                self.result_owner.as_mut().expect("returned guard option").suspended_payload =
                    Some(std::sync::Arc::new(view));
            }
        }
        if !proofs.is_empty() {
            self.growth.after.entry(site.id).or_default().extend(proofs);
        }
        Ok(())
    }

    pub(in crate::resource::memory) fn restore_guard_payload(
        &mut self,
        saved: &Suspended,
        site: &Span,
    ) -> Result<(), VirErr> {
        let name = saved.interval.payload_name();
        if self.heap.borrowed.contains_key(&name) {
            return Err(unsupported(site, "a duplicate returned guard payload"));
        }
        self.storage.receive_storage(saved.charges.clone(), site)?;
        self.heap.borrowed.insert(name, saved.wrapper.clone());
        Ok(())
    }

    /// Dropping an unopened Option executes the guard destructor only on the
    /// Some path. The release phase selects that path in the accounting ledger.
    pub(in crate::resource::memory) fn restore_dropped_guard_payload(
        &mut self,
        saved: &Suspended,
        site: &Span,
    ) {
        if let Err(error) = self.restore_guard_payload(saved, site) {
            self.transitions.protected_versions.error = Some(error);
        }
    }
}
