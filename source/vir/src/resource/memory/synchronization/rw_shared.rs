//! A shared reader observes the source value. An exclusive writer receives
//! the version at acquisition and publishes its replacement at explicit release.
use super::{Acquisition, Contract, Holders, Instance, local::Interval};
use crate::{
    ast::*,
    messages::Span,
    resource::memory::{accounting::Accounting, analysis::Analysis, model::unsupported},
};

impl Analysis<'_> {
    /// Preserve the source constructor length in a portable publication when
    /// the vector has had no modeled mutation. Verus checks it again at the move.
    pub(super) fn freeze_rw_payload(
        &mut self,
        value: &Expr,
        child: &mut crate::resource::memory::heap::Owner,
    ) {
        if let Some(id) = child.vector
            && let state = &self.growth.vectors[id]
            && state.local_constructor
            && state.pushes == 0
            && state.removals == 0
            && state.sequence_length.is_none()
            && state.append_only
            && child.source.is_some()
            && child.geometry.as_ref().and_then(crate::resource::memory::contracts::constant)
                == Some(0)
            && crate::resource::memory::projections::spec_value(value).is_ok()
        {
            let zero = crate::resource::memory::contracts::literal(&value.span, 0);
            let length = self.owner_length(&value.span, child);
            let check = crate::resource::memory::metadata::expr::check(
                &value.span,
                crate::ast_util::mk_eq(&value.span, &length, &zero),
                "the constructed vector is no longer empty at the ownership transfer",
            );
            self.growth.before.entry(value.span.id).or_default().push(check);
            child.source = None;
        }
        self.freeze_owner_geometry(value, child);
        self.protect_vector_length(value, child);
    }

    pub(super) fn rw_observed_read(&self, id: u64, typ: &Typ, site: &Span) -> Result<bool, VirErr> {
        let instance = Instance::Fresh(id);
        if self.heap.shared.imported_mutex(instance, typ, site)?.is_some() {
            return Ok(true);
        }
        Ok(self
            .heap
            .shared
            .protected_root(instance)
            .is_some_and(|(root, _)| self.heap.workers.shares_root(root)))
    }

    pub(super) fn rw_acquire_shared(
        &mut self,
        call: &Expr,
        id: u64,
        payload: &Typ,
        handle: &Typ,
    ) -> Result<Option<Interval>, VirErr> {
        let instance = Instance::Fresh(id);
        if self.heap.shared.imported_mutex(instance, payload, &call.span)?.is_none() {
            return Ok(None);
        }
        let ExprX::Call { target: CallTarget::Fun(_, f, ..), .. } = &call.x else { unreachable!() };
        let TypX::Datatype(dt, _, _) = &**handle else { unreachable!() };
        // The measured vstd method also proves which receiver issued the writer.
        // Require the actual writer/writer and writer/reader proofs before using
        // an exclusive interval for shared payload versions.
        if self.layouts.writer_issuers.get(f) != Some(&0)
            || !self.layouts.holder_proofs.get(dt).is_some_and(|r| {
                r.population.is_some()
                    && r.exclusions.contains_key(dt)
                    && r.exclusions
                        .keys()
                        .any(|peer| super::RwRecord::of(peer) == Some(super::RwRecord::Reader))
            })
        {
            return Err(unsupported(
                &call.span,
                "a shared writer without verified issuer and interference evidence",
            ));
        }
        let interval =
            Interval { instance, acquisition: Acquisition(Accounting::fresh_allocation()) };
        self.storage.acquire_interval(
            &call.span,
            interval,
            Contract { holders: Holders::Exclusive, may_block: true, may_poison: false },
        )?;
        self.open_imported_payload(interval, payload, &call.span)?;
        Ok(Some(interval))
    }

    pub(super) fn rw_release_shared(
        &mut self,
        interval: Interval,
        span: &Span,
    ) -> Result<(), VirErr> {
        let mut proofs = Vec::new();
        self.publish_imported_payload(interval, span, &mut proofs).ok_or_else(|| {
            unsupported(span, "a verified writer release without its outgoing shared payload")
        })?;
        self.growth.after.entry(span.id).or_default().extend(proofs);
        self.storage.release_interval(span, interval);
        Ok(())
    }
}
