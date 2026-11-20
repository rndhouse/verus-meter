//! An imported Arc owns a handle, while its protected contents are supplied at
//! acquisition. Source-level ownership operations transform that input in the
//! worker. A release exports the resulting forest separately from worker results.

mod input;

use super::local::{Interval, Owned};
use crate::{
    ast::*,
    messages::{AstId, Span},
    resource::memory::{
        accounting::{Accounting, ReturnedStorage},
        analysis::Analysis,
        heap::{Heap, Owner, OwnerSlot},
        lifetime::{Storage, Value},
        metadata::{self, expr},
        model::unsupported,
        shared::RootId,
        workers::SourceVisit,
    },
};
use std::collections::BTreeMap;

#[derive(Default)]
pub(in super::super) struct Versions {
    bindings: BTreeMap<Interval, Binding>,
    /// Cleanup runs on each source exit and cannot return errors directly.
    error: Option<VirErr>,
}

/// The forest supplied by a holder of this exact mutex, at this dynamic acquisition.
/// Region identities describe storage roles separately from numeric byte terms.
struct Binding {
    root: RootId,
    payload_type: Typ,
    entry: Expr,
    input_origins: Vec<ReturnedStorage>,
    access: SourceVisit<AstId>,
    releases: Vec<Release>,
}

/// Values frozen in the releasing actor's proof scope before its view expires.
struct Release {
    visit: SourceVisit<Span>,
    contents: Expr,
    origins: Vec<ReturnedStorage>,
}

impl Interval {
    fn payload_name(self) -> VarIdent {
        VarIdent(
            std::sync::Arc::new("$memory_acquired_payload".into()),
            VarIdentDisambiguate::VirTemp(self.acquisition.0),
        )
    }
}

impl Versions {
    pub(in super::super) fn roots(&self) -> impl Iterator<Item = RootId> + '_ {
        self.bindings.values().map(|b| b.root)
    }

    pub(in super::super) fn open_roots(&self, heap: &Heap) -> impl Iterator<Item = RootId> {
        self.bindings.iter().filter_map(|(interval, b)| {
            heap.borrowed.contains_key(&interval.payload_name()).then_some(b.root)
        })
    }

    pub(in super::super) fn validate(
        &self,
        actor: crate::resource::memory::workers::WorkerId,
        entry: &crate::resource::memory::shared::SharedRoots,
        heap: &Heap,
        storage: &Accounting,
        span: &Span,
    ) -> Result<(), VirErr> {
        if let Some(err) = &self.error {
            return Err(err.clone());
        }
        for (&interval, binding) in &self.bindings {
            let observed = storage
                .points()
                .iter()
                .any(|p| p.span.id == binding.access.site && p.condition.held.contains(&interval));
            if entry.imported_mutex(interval.instance, &binding.payload_type, span)?
                != Some(binding.root)
                || !binding.access.valid_for(Some(actor))
                || !observed
                || binding.input_origins.is_empty()
                || !crate::ast_util::types_equal(&binding.entry.typ, &expr::memory_type())
            {
                return Err(unsupported(
                    span,
                    "a protected input without its captured root and acquired source visit",
                ));
            }
            if heap.borrowed.contains_key(&interval.payload_name()) || binding.releases.is_empty() {
                return Err(unsupported(span, "an acquired payload without its outgoing contents"));
            }
            for release in &binding.releases {
                let released = storage.points().iter().any(|p| p.span.id == release.visit.site.id
                    && matches!(p.condition.boundary, super::local::Boundary::Release(id) if id == interval));
                if !released
                    || !release.visit.valid_for(Some(actor))
                    || release.origins.is_empty()
                    || !crate::ast_util::types_equal(&binding.entry.typ, &release.contents.typ)
                {
                    return Err(unsupported(
                        &release.visit.site,
                        "shared contents without their releasing source guard",
                    ));
                }
            }
        }
        Ok(())
    }
}

impl Analysis<'_> {
    pub(in super::super) fn open_guard_arguments(
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
                Some(super::local::View::Guard(interval)) => {
                    if let Some(typ) = self.layouts.mutable_guard_payload(&param.x.typ) {
                        self.open_imported_payload(interval, typ, site)?;
                    }
                }
                Some(super::local::View::Payload(interval)) => self.open_imported_payload(
                    interval,
                    crate::resource::memory::paths::referent(&param.x.typ),
                    site,
                )?,
                _ => {}
            }
        }
        Ok(())
    }

    /// Lazily bind only on a path that actually dereferences a live guard.
    /// While that guard is held, no other actor can change these contents.
    pub(in super::super) fn open_imported_payload(
        &mut self,
        interval: Interval,
        typ: &Typ,
        site: &Span,
    ) -> Result<(), VirErr> {
        if !self.layouts.owner(typ) {
            return Ok(());
        }
        let Some(root) = self.heap.shared.imported_mutex(interval.instance, typ, site)? else {
            return Ok(());
        };
        if !self.storage.holds_interval(interval) {
            return Err(unsupported(site, "a shared payload access outside its live acquisition"));
        }
        if self.growth.shared_occurrences.contains_key(&root) {
            return Err(unsupported(
                site,
                "an imported mutex family without the selected root occurrence",
            ));
        }
        if self.growth.indexed_shared.contains_key(&root)
            || self.growth.occurrence_peers.contains_key(&root)
            || self.growth.peer_results.contains_key(&root)
            || self.growth.section_shared.contains(&root)
        {
            return Err(unsupported(
                site,
                "a protected worker input with outstanding backing reservations",
            ));
        }
        let name = interval.payload_name();
        if self.heap.borrowed.contains_key(&name) {
            return Ok(());
        }
        if !self.layouts.plain_protected_payload(typ)
            || self.transitions.protected_versions.bindings.contains_key(&interval)
        {
            return Err(unsupported(
                site,
                "an imported payload without a unique representable acquisition input",
            ));
        }
        let (entry, payload, fixed_bytes) = self.acquired_owner(typ, site)?;
        let charged = self
            .owner_charges(site, &payload)
            .into_values()
            .fold(expr::integer(site, 0), |sum, bytes| {
                crate::resource::memory::contracts::add(site, sum, bytes)
            });
        let bytes = expr::cost(site, entry.clone(), expr::integer(site, 0));
        self.growth.before.entry(site.id).or_default().push(expr::check(
            site,
            crate::ast_util::mk_eq(site, &charged, &bytes),
            "acquired shared contents do not account for the supplied storage",
        ));
        let input_origins = self.storage.returned_storage(Some(&payload), &self.growth.elements);
        let owner = Owner {
            synchronization: Some(Owned::Mutex(interval.instance)),
            children: [(OwnerSlot::Contents, payload)].into(),
            ..Owner::default()
        };
        self.growth.versioned_shared.insert(root, fixed_bytes);
        self.heap.borrowed.insert(name, owner);
        let access = self.source_visit(site.id, self.local_occurrences(site)?);
        self.transitions.protected_versions.bindings.insert(
            interval,
            Binding {
                root,
                payload_type: typ.clone(),
                entry,
                input_origins,
                access,
                releases: Vec::new(),
            },
        );
        self.storage.record_live(site)
    }

    /// End an already-open view when a checked helper drops the moved guard.
    /// The call-site value equals the release value if the whole call left the
    /// payload untouched. Returning the guard keeps the original view open.
    pub(in super::super) fn publish_consumed_payloads(
        &mut self,
        call: &super::helpers::Call,
        result: Option<Owned>,
        site: &Span,
    ) -> Result<(), VirErr> {
        let mut proofs = Vec::new();
        for interval in call.consumed() {
            if result.and_then(Owned::interval) == Some(interval)
                || !self.heap.borrowed.contains_key(&interval.payload_name())
            {
                continue;
            }
            if call.payload_borrows.contains(&interval) {
                return Err(unsupported(
                    site,
                    "a consuming helper without its release-time payload",
                ));
            }
            self.publish_imported_payload(interval, site, &mut proofs);
        }
        if !proofs.is_empty() {
            self.growth.after.entry(site.id).or_default().extend(proofs);
        }
        Ok(())
    }

    /// Transport the live allocation tree into the shared cell. Only the
    /// version's frame charge ends; displaced owners remain in the worker.
    pub(in super::super) fn publish_imported_payload(
        &mut self,
        interval: Interval,
        site: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        let Some(mut wrapper) = self.heap.borrowed.remove(&interval.payload_name()) else { return };
        let visit = match self.local_occurrences(site) {
            Ok(local) => self.source_visit(site.clone(), local),
            Err(error) => {
                self.transitions.protected_versions.error = Some(error);
                return;
            }
        };
        let payload =
            wrapper.children.remove(&OwnerSlot::Contents).expect("acquired mutex contents");
        let origins = self.storage.returned_storage(Some(&payload), &self.growth.elements);
        let current = self.owner_metadata(site, &payload, proofs);
        let (contents, declaration) = expr::local(
            site,
            "released_contents",
            expr::memory_type(),
            expr::empty(site, expr::record_type()),
            Mode::Spec,
        );
        self.growth.declarations.push(declaration);
        proofs.push(expr::assign(site, &contents, current));
        let storage = Storage {
            typ: crate::ast_util::unit_typ(),
            value: Value::unit(),
            owner: Some(payload),
        };
        let versions = &mut self.transitions.protected_versions;
        match self.storage.take_storage(&storage, &self.growth, site) {
            Ok(transferred) => {
                // The shared cell assumes the storage removed from this frame.
                // Check its exported bytes against the actual transported charges
                // at release, while the proof variables still denote this visit.
                let bytes = expr::cost(site, contents.clone(), expr::integer(site, 0));
                let charged = transferred.live_expression(site).total();
                proofs.push(expr::check(
                    site,
                    crate::ast_util::mk_eq(site, &bytes, &charged),
                    "released shared contents do not account for the transported storage",
                ));
                versions
                    .bindings
                    .get_mut(&interval)
                    .expect("acquired input")
                    .releases
                    .push(Release { visit, contents, origins });
            }
            Err(err) => versions.error = Some(err),
        }
    }
}
