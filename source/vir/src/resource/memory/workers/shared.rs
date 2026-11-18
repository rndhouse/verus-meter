//! Reconcile indexed capture claims with the coordinator's canonical Arc backing.
//! Workers run independently. Until collection their checked entry claims reserve
//! backing, including when a completed worker keeps the handle in its result.

mod slots;

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
    /// Unreconciled entry aliases plus the reservation of each live mixed-root result.
    pub(in super::super) pending: Expr,
    /// The same ownership tree moves between fixed and conditional accounting.
    pub(in super::super) backing: Owner,
    /// Fixed and symbolic charges reached by this immutable payload.
    charges: SharedBackingCharges,
    /// Number of handles actually moved into one occurrence of this family.
    weights: BTreeMap<WorkerId, u64>,
}

impl Claims {
    /// Prove the outstanding claims cover this release before updating their count.
    fn release(&self, span: &Span, count: Expr, message: &str, proofs: &mut Vec<Stmt>) {
        let remaining = contracts::subtract(span, self.pending.clone(), count);
        proofs.push(expr::check(
            span,
            crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &remaining, InequalityOp::Le),
            message,
        ));
        proofs.push(expr::assign(span, &self.pending, remaining));
    }

    /// A final directly tracked drop can make the backing conditional only if
    /// this accounting domain still has every charge of the payload.
    pub(in super::super) fn defer_backing(
        &self,
        storage: &mut Accounting,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        let empty = crate::ast_util::mk_eq(span, &self.pending, &expr::integer(span, 0));
        if !self.charges.defer(storage, empty, span) {
            proofs.push(expr::check(
                span,
                crate::ast_util::mk_bool(span, false),
                "cannot locate the shared payload's live backing charges",
            ));
        }
    }

    /// A collection length describes strong claims only if all of its possible
    /// publications capture the same multiplicity of this particular root.
    fn uniform_weight<'a>(&self, families: impl Iterator<Item = &'a WorkerId>) -> Option<u64> {
        let mut weights = families.map(|id| self.weights.get(id).copied().unwrap_or(0));
        let first = weights.next()?;
        weights.all(|w| w == first).then_some(first)
    }

    /// Sum this root's entry aliases over the actual occupied handle slots.
    /// The common uniform case needs only the checked vector length.
    pub(in super::super) fn collection_count<'a>(
        &self,
        span: &Span,
        families: impl Iterator<Item = &'a WorkerId> + Clone,
        records: &Expr,
        length: &Expr,
    ) -> Option<(Expr, bool)> {
        if let Some(weight) = self.uniform_weight(families.clone()) {
            return (weight != 0).then(|| {
                (contracts::multiply(span, contracts::literal(span, weight), length.clone()), false)
            });
        }
        let count = families
            .filter_map(|id| {
                let weight = *self.weights.get(id)?;
                let count = expr::operation(
                    span,
                    "worker_family_count",
                    vec![records.clone(), length.clone(), expr::path(span, id.descriptor())],
                    std::sync::Arc::new(TypX::Int(IntRange::Nat)),
                );
                Some(contracts::multiply(span, contracts::literal(span, weight), count))
            })
            .reduce(|a, b| contracts::add(span, a, b))?;
        Some((count, true))
    }

    /// Use the selected publication identity for mixed families. A uniform
    /// weight already follows from the checked membership of the occurrence.
    fn selected_weight(&self, span: &Span, occurrence: &Occurrence) -> Option<Expr> {
        if let Some(weight) = self.uniform_weight(occurrence.templates.iter()) {
            return (weight != 0).then(|| contracts::literal(span, weight));
        }
        let weight = occurrence
            .templates
            .iter()
            .filter_map(|id| Some((id, self.weights.get(id)?)))
            .fold(expr::integer(span, 0), |others, (id, count)| {
                let matched = expr::operation(
                    span,
                    "worker_matches",
                    vec![occurrence.record.clone(), expr::path(span, id.descriptor())],
                    crate::ast_util::bool_typ(),
                );
                select(span, matched, contracts::literal(span, *count), others)
            });
        Some(weight)
    }
}

impl Execution {
    /// The known allocation returned directly by this checked worker body.
    pub(super) fn returned_arc_root(&self) -> Option<RootId> {
        self.result.owner.as_ref()?.shared?.known()
    }
}

impl SelectedAlias {
    /// Each mixed result keeps one claim on its observed root. Clones share
    /// this reservation until their last executable drop in the coordinator.
    fn reservation(&self, span: &Span, root: RootId) -> Expr {
        select(
            span,
            crate::ast_util::mk_eq(span, &self.identity, &expr::integer(span, root.serial())),
            expr::integer(span, 1),
            expr::integer(span, 0),
        )
    }
}

impl Analysis<'_> {
    /// An accounting domain may return a collected Arc, but every indexed
    /// entry claim must have a matching source join on each normal exit.
    pub(in super::super) fn check_indexed_exits(&mut self, body: &Span) {
        if self.growth.indexed_shared.is_empty() {
            return;
        }
        let exits = self
            .flow
            .exits
            .iter()
            .map(|edge| &edge.span)
            .chain(self.flow.reachable.then_some(body));
        for span in exits {
            for claims in self.growth.indexed_shared.values() {
                self.growth.after.entry(span.id).or_default().push(expr::check(
                    span,
                    crate::ast_util::mk_eq(span, &claims.pending, &expr::integer(span, 0)),
                    "outstanding shared worker claims at accounting scope exit",
                ));
            }
        }
    }

    pub(super) fn index_worker_claims(
        &mut self,
        actor: WorkerId,
        span: &Span,
    ) -> Result<(), VirErr> {
        let worker = &self.heap.workers.records[&actor];
        let execution = worker.execution.as_ref().unwrap();
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
        for (root, count, backing) in self.heap.shared.index_imports(&worker.entry_shared, span)? {
            if !self.transitions.owns_fixed_root(root) {
                return Err(unsupported(
                    span,
                    "indexed aliases of a repeated or imported allocation",
                ));
            }
            let claims = match self.growth.indexed_shared.entry(root) {
                std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::btree_map::Entry::Vacant(entry) => {
                    let charges = SharedBackingCharges::new(&backing, &self.growth.elements, span)?;
                    let zero = expr::integer(span, 0);
                    let (pending, decl) =
                        expr::local(span, "outstanding_strong", zero.typ.clone(), zero, Mode::Spec);
                    self.growth.declarations.push(decl);
                    entry.insert(Claims { pending, backing, charges, weights: BTreeMap::new() })
                }
            };
            claims.weights.insert(actor, count);
            let next =
                contracts::add(span, claims.pending.clone(), contracts::literal(span, count));
            self.growth.after.entry(span.id).or_default().push(expr::assign(
                span,
                &claims.pending,
                next,
            ));
        }
        Ok(())
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
                        .is_some_and(|claims| claims.weights.contains_key(actor))
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
        if roots.len() > 1 {
            return Ok(self.reserve_arc_result(span, result, roots));
        }
        let claims = self.growth.indexed_shared.get(&root).ok_or_else(|| {
            unsupported(span, "an indexed Arc result outside its canonical domain")
        })?;
        let path = expr::path(span, []);
        let actual = expr::lookup(span, result, path.clone());
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            crate::ast_util::mk_eq(span, &actual, &root.record(span, path)),
            "cannot establish the selected result's canonical shared allocation",
        ));
        if !self.heap.shared.has_strong(root) {
            claims.charges.receive(&mut self.storage, span)?;
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
        self.heap.shared.select_alias(identity, roots)
    }

    /// A fixed receiver can consume the original handle once. Keep the
    /// publication's entry claims charged until the receiver itself is joined.
    pub(super) fn delegate_captured_handles(
        &mut self,
        span: &Span,
        owner: &mut Owner,
    ) -> Result<(), VirErr> {
        use super::SelectedWorker;
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
        for root in &alias.roots {
            self.growth.indexed_shared[root].release(
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
        let selection = returned.and_then(|(owner, roots)| match owner.shared {
            Some(StrongLink::Selected(id)) => Some((self.heap.shared.selection(id), roots)),
            _ => None,
        });
        for (root, claims) in &self.growth.indexed_shared {
            // A mixed result keeps one of the selected worker's entry claims.
            // Its last local alias reconciles that claim at destruction.
            let mut retained = None;
            if let Some((alias, returned_roots)) = selection
                && alias.roots.contains(root)
            {
                let unchanged = returned_roots.iter().all(|(actor, result_root)| {
                    claims.weights.get(actor).copied().unwrap_or(0)
                        == u64::from(result_root == root)
                });
                if unchanged {
                    continue;
                }
                retained = Some(alias.reservation(span, *root));
            }
            let Some(captured) = claims.selected_weight(span, occurrence) else { continue };
            let weight = match retained {
                Some(count) => contracts::subtract(span, captured, count),
                None => captured,
            };
            self.require_indexed_claim_owner(span)?;
            claims.release(
                span,
                weight,
                "cannot reconcile the selected worker's outstanding strong references",
                self.growth.after.entry(span.id).or_default(),
            );
        }
        Ok(())
    }
}
