//! Reconcile indexed capture claims with the coordinator's canonical Arc backing.
//! Workers run independently. Until collection their checked entry claims reserve
//! backing, including when a completed worker keeps the handle in its result.

mod collections;
mod deferred;
use deferred::Deferred;
mod occurrences;
mod payloads;
mod peers;
mod population;
mod publication;
use population::Population;
pub(in super::super) use publication::PublicationSite;
mod slots;
pub(in super::super) use peers::{PeerResult, Peers};

use super::super::{
    accounting::{Accounting, SharedBackingCharges},
    analysis::Analysis,
    contracts,
    growth::select,
    heap::Owner,
    metadata::expr,
    model::unsupported,
    shared::{RootId, SelectedAlias, StrongLink},
};
use super::{WorkerId, execution::Execution, populations::Occurrence};
use crate::{ast::*, messages::Span};
use std::collections::{BTreeMap, BTreeSet};

/// Strong aliases published in retained workers and not yet reconciled by a
/// coordinator join. An outstanding claim keeps the backing charged once even
/// if the worker may already have run its last destructor.
pub(in super::super) struct Claims {
    /// Pending reservations and their multiplicity for each publication family.
    pub(in super::super) population: Population,
    /// The same ownership tree moves between fixed and conditional accounting.
    pub(in super::super) backing: Owner,
    /// Fixed and symbolic charges reached by this immutable payload.
    charges: Option<SharedBackingCharges>,
}

impl Claims {
    /// A final directly tracked drop can make the backing conditional only if
    /// this accounting domain still has every charge of the payload.
    pub(in super::super) fn retain_backing(
        &self,
        root: RootId,
        held: &mut BTreeSet<RootId>,
        storage: &mut Accounting,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        let Some(charges) = &self.charges else {
            held.insert(root);
            return;
        };
        let empty = crate::ast_util::mk_eq(span, &self.population.pending, &expr::integer(span, 0));
        if !charges.defer(storage, empty, span) {
            proofs.push(expr::check(
                span,
                crate::ast_util::mk_bool(span, false),
                "cannot locate the shared payload's live backing charges",
            ));
        }
    }
}

impl Execution {
    /// The known allocation returned directly by this checked worker body.
    pub(super) fn returned_arc_root(&self) -> Option<RootId> {
        self.result.owner.as_ref()?.shared?.known()
    }
}

impl Analysis<'_> {
    /// An accounting domain may return a collected Arc, but every indexed
    /// entry claim must have a matching source join on each normal exit.
    pub(in super::super) fn check_indexed_exits(&mut self, body: &Span) {
        if self.growth.indexed_shared.is_empty() && self.growth.occurrence_peers.is_empty() {
            return;
        }
        let exits = self
            .flow
            .exits
            .iter()
            .map(|edge| &edge.span)
            .chain(self.flow.reachable.then_some(body));
        for span in exits {
            for deferred in
                self.growth.occurrence_peers.values().filter_map(|p| p.deferred.as_ref())
            {
                self.growth.after.entry(span.id).or_default().push(expr::check(
                    span,
                    deferred.empty(span),
                    "unreleased shared backing at accounting scope exit",
                ));
            }
            for claims in self
                .growth
                .indexed_shared
                .values()
                .map(|claims| &claims.population)
                .chain(self.growth.occurrence_peers.values().map(|peers| &peers.population))
            {
                self.growth.after.entry(span.id).or_default().push(expr::check(
                    span,
                    crate::ast_util::mk_eq(span, &claims.pending, &expr::integer(span, 0)),
                    "outstanding shared worker claims at accounting scope exit",
                ));
            }
        }
        for deferred in self.growth.occurrence_peers.values().filter_map(|p| p.deferred.as_ref()) {
            deferred.release(&mut self.storage);
        }
    }

    pub(super) fn index_worker_claims(
        &mut self,
        actor: WorkerId,
        span: &Span,
        forest: &Expr,
    ) -> Result<Option<Expr>, VirErr> {
        let worker = &self.heap.workers.records[&actor];
        let execution = worker.execution.as_ref().unwrap();
        if !execution.effects.ownership.collection_claims.is_empty() {
            return Err(unsupported(
                span,
                "retaining a collector with outstanding shared reservations in an indexed slot",
            ));
        }
        let returned = execution.returned_arc_root();
        if (!execution.shared.is_empty()
            && !returned.is_some_and(|id| worker.entry_shared.has_strong(id)))
            || (self.current_worker.is_some() && !worker.entry_shared.is_empty())
        {
            return Err(unsupported(
                span,
                "retained worker shared-reference populations without their conservation relation",
            ));
        }
        let imports = self.heap.shared.index_imports(&worker.entry_shared, span)?;
        let mut carried = None;
        let single = imports.len() == 1;
        for (root, count, backing) in imports {
            if !self.transitions.owns_fixed_root(root) {
                if !single || !self.growth.shared_occurrences.contains_key(&root) {
                    return Err(unsupported(
                        span,
                        "indexed aliases of a repeated allocation with outstanding owners in another domain",
                    ));
                }
                Self::check_occurrence_payload(span, &backing)?;
                let peer = self.heap.shared.has_strong(root);
                let registered = self.growth.occurrence_peers.get(&root);
                if let Some(previous) = self.growth.occurrence_roots.get(&actor) {
                    if *previous != root
                        || peer
                            != registered.is_some_and(|p| p.population.weights.contains_key(&actor))
                    {
                        return Err(unsupported(
                            span,
                            "a worker family with inconsistent shared backing ownership",
                        ));
                    }
                } else if peer
                    && registered.is_none()
                    && self.growth.occurrence_roots.values().any(|site| *site == root)
                {
                    return Err(unsupported(
                        span,
                        "a peer outside its allocation's checked publication group",
                    ));
                }
                self.growth.occurrence_roots.insert(actor, root);
                if peer {
                    let ExprX::Var(destination) = &forest.x else {
                        return Err(unsupported(
                            span,
                            "a peer publication without a named ownership forest",
                        ));
                    };
                    self.register_peer(span, actor, root, destination, &backing);
                    continue;
                }
                self.check_peer_limit(span, actor, root);
                carried = Some(self.transfer_occurrence_backing(span, &backing)?);
                continue;
            }
            let claims = match self.growth.indexed_shared.entry(root) {
                std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::btree_map::Entry::Vacant(entry) => {
                    let charges =
                        SharedBackingCharges::for_payload(&backing, &self.growth.elements, span)?;
                    let population = Population::new(span, &mut self.growth.declarations);
                    entry.insert(Claims { population, backing, charges })
                }
            };
            let proofs = self.growth.after.entry(span.id).or_default();
            claims.population.publish(actor, count, span, proofs);
            if !self.heap.shared.has_strong(root) {
                claims.retain_backing(
                    root,
                    &mut self.heap.shared.held_payloads,
                    &mut self.storage,
                    span,
                    proofs,
                );
            }
        }
        Ok(carried)
    }

    /// Indexed backing and outstanding claims still belong to the publisher.
    pub(super) fn require_indexed_claim_owner(&self, span: &Span) -> Result<(), VirErr> {
        if self.current_worker.is_some() {
            return Err(unsupported(
                span,
                "collection of indexed shared claims outside their publishing coordinator",
            ));
        }
        Ok(())
    }

    /// Resolve each possible worker's returned Arc against its capture claims.
    /// Both the identity proof and the join debit use this same mapping.
    pub(super) fn indexed_result_roots(
        &self,
        span: &Span,
        occurrence: &Occurrence,
    ) -> Result<BTreeMap<WorkerId, RootId>, VirErr> {
        let mut roots = BTreeMap::new();
        for actor in &occurrence.templates {
            let root = self.growth.worker_executions[actor]
                .returned_arc_root()
                .filter(|root| {
                    self.growth
                        .indexed_shared
                        .get(root)
                        .is_some_and(|claims| claims.population.weights.contains_key(actor))
                })
                .ok_or_else(|| {
                    unsupported(span, "an indexed Arc result outside its canonical domain")
                })?;
            roots.insert(*actor, root);
        }
        Ok(roots)
    }

    pub(super) fn receive_indexed_alias(
        &mut self,
        span: &Span,
        returned: &BTreeMap<WorkerId, RootId>,
        result: Expr,
    ) -> Result<Owner, VirErr> {
        let roots: BTreeSet<_> = returned.values().copied().collect();
        let root = *roots
            .first()
            .ok_or_else(|| unsupported(span, "an indexed Arc result without a publication"))?;
        if roots.len() > 1 || self.current_worker.is_some() {
            return Ok(self.reserve_arc_result(span, result, roots));
        }
        let path = expr::path(span, []);
        let actual = expr::lookup(span, result, path.clone());
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            crate::ast_util::mk_eq(span, &actual, &root.record(span, path)),
            "cannot establish the selected result's canonical shared allocation",
        ));
        self.restore_indexed_alias(span, root)
    }

    fn restore_indexed_alias(&mut self, span: &Span, root: RootId) -> Result<Owner, VirErr> {
        let claims = self.growth.indexed_shared.get(&root).ok_or_else(|| {
            unsupported(span, "an indexed Arc result outside its canonical domain")
        })?;
        if !self.heap.shared.has_strong(root) {
            if let Some(charges) = &claims.charges {
                charges.receive(&mut self.storage, span)?;
            } else if self.growth.section_shared.contains(&root)
                || !self.heap.shared.held_payloads.remove(&root)
            {
                return Err(unsupported(span, "an indexed result after its shared payload ended"));
            }
        }
        self.heap.shared.receive_indexed(root, &claims.backing, span)
    }

    fn reserve_arc_result(&mut self, span: &Span, result: Expr, roots: BTreeSet<RootId>) -> Owner {
        let actual = expr::lookup(span, result, expr::path(span, []));
        // Check the full descriptor here. Later byte and drop obligations
        // need only the frozen identity, even after another pop.
        let identity =
            self.metadata_local(span, "joined_shared", expr::shared_identity(span, actual.clone()));
        let expected = super::super::shared::selected_record(span, identity.clone());
        let member = crate::ast_util::disjoin(
            span,
            &roots
                .iter()
                .map(|root| {
                    crate::ast_util::mk_eq(span, &identity, &expr::integer(span, root.serial()))
                })
                .collect(),
        );
        let proof = crate::ast_util::conjoin(
            span,
            &vec![member, crate::ast_util::mk_eq(span, &actual, &expected)],
        );
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            proof,
            "cannot establish the selected result's canonical shared allocation",
        ));
        self.heap.shared.select_alias(identity, roots, self.current_worker)
    }

    /// A fixed receiver can consume the original handle once. Keep the
    /// publication's entry claims charged until the receiver itself is joined.
    pub(super) fn delegate_captured_handles(
        &mut self,
        span: &Span,
        owner: &mut Owner,
    ) -> Result<(), VirErr> {
        use super::SelectedWorker;
        if let Some(StrongLink::Selected(id)) = owner.shared
            && self.heap.shared.selection(id).collector.is_some()
        {
            return Err(unsupported(
                span,
                "forwarding a collector's selected Arc to a nested worker",
            ));
        }
        if let Some(root) = owner.shared.and_then(StrongLink::known)
            && self.growth.peer_results.contains_key(&root)
        {
            return Err(unsupported(
                span,
                "forwarding a returned Arc with indexed peer reservations to another actor",
            ));
        }
        if let Some(SelectedWorker::Recorded(occurrence)) = &mut owner.selected_worker {
            if occurrence.result_reservation.is_some() {
                return Err(unsupported(span, "forwarding an outstanding delegated join"));
            }
            if self.current_worker.is_none()
                && occurrence.templates.iter().all(|actor| {
                    matches!(
                        &*self.growth.worker_executions[actor].result.typ,
                        TypX::Decorate(TypDecoration::Arc, _, _)
                    )
                })
            {
                let returned = self.indexed_result_roots(span, occurrence)?;
                let result = expr::operation(
                    span,
                    "worker_result",
                    vec![occurrence.record.clone()],
                    expr::memory_type(),
                );
                let reservation =
                    self.reserve_arc_result(span, result, returned.into_values().collect());
                let Some(StrongLink::Selected(id)) = reservation.shared else { unreachable!() };
                occurrence.result_reservation = Some(id);
            }
        }
        for child in owner.children.values_mut() {
            self.delegate_captured_handles(span, child)?;
        }
        Ok(())
    }

    /// The checked receiver consumed every delegated handle on every exit.
    /// Reconcile its captures once, leaving the returned alias's reservation
    /// for the ordinary worker entry-to-exit strong-reference accounting.
    pub(super) fn collect_delegated_handles(
        &mut self,
        span: &Span,
        owner: &Owner,
    ) -> Result<(), VirErr> {
        if let Some(super::SelectedWorker::Recorded(occurrence)) = &owner.selected_worker
            && let Some(id) = occurrence.result_reservation
        {
            self.require_indexed_claim_owner(span)?;
            let roots = self.indexed_result_roots(span, occurrence)?;
            let alias = Owner { shared: Some(StrongLink::Selected(id)), ..Default::default() };
            self.collect_indexed_claims(span, occurrence, Some((&alias, &roots)))?;
        }
        for child in owner.children.values() {
            self.collect_delegated_handles(span, child)?;
        }
        Ok(())
    }

    pub(in super::super) fn release_selected_alias(
        &self,
        span: &Span,
        alias: SelectedAlias,
        proofs: &mut Vec<Stmt>,
    ) {
        if alias.collector.is_some() {
            // The matching collector join reconciles its captured share and result.
            if alias.collector != self.current_worker {
                proofs.push(expr::check(
                    span,
                    crate::ast_util::mk_bool(span, false),
                    "a collected Arc released outside its receiving worker",
                ));
            }
            return;
        }
        for root in &alias.roots {
            self.growth.indexed_shared[root].population.release(
                span,
                alias.reservation(span, *root),
                "cannot reconcile the selected Arc's backing reservation",
                proofs,
            );
        }
    }

    pub(super) fn collect_indexed_claims(
        &mut self,
        span: &Span,
        occurrence: &Occurrence,
        returned: Option<(&Owner, &BTreeMap<WorkerId, RootId>)>,
    ) -> Result<(), VirErr> {
        let returned_peer = occurrence
            .templates
            .iter()
            .all(|actor| self.growth.worker_executions[actor].returned_arc_root().is_some());
        for peers in self.growth.occurrence_peers.values() {
            if !returned_peer
                && let Some(weight) = peers.population.selected_weight(span, occurrence)
            {
                self.require_indexed_claim_owner(span)?;
                peers.population.release(
                    span,
                    weight,
                    "cannot reconcile the selected allocation peer",
                    self.growth.after.entry(span.id).or_default(),
                );
            }
        }
        let selection = returned.and_then(|(owner, roots)| match owner.shared {
            Some(StrongLink::Selected(id)) => Some((self.heap.shared.selection(id), roots)),
            _ => None,
        });
        for (root, claims) in &self.growth.indexed_shared {
            if self.transitions.collection_claims.contains_key(root) {
                continue;
            }
            // A mixed result keeps one of the selected worker's entry claims.
            // Its last local alias reconciles that claim at destruction.
            let mut retained = None;
            if let Some((alias, returned_roots)) = selection
                && alias.roots.contains(root)
            {
                let unchanged = returned_roots.iter().all(|(actor, result_root)| {
                    claims.population.weights.get(actor).copied().unwrap_or(0)
                        == u64::from(result_root == root)
                });
                if unchanged {
                    continue;
                }
                retained = Some(alias.reservation(span, *root));
            }
            let Some(captured) = claims.population.selected_weight(span, occurrence) else {
                continue;
            };
            let weight = match retained {
                Some(count) => contracts::subtract(span, captured, count),
                None => captured,
            };
            self.require_indexed_claim_owner(span)?;
            claims.population.release(
                span,
                weight,
                "cannot reconcile the selected worker's outstanding strong references",
                self.growth.after.entry(span.id).or_default(),
            );
        }
        Ok(())
    }
}
