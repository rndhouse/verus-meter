//! Source-checked reservations for independently retained workers that share one allocation visit.
use super::*;

/// One received Arc may be the charged owner or a peer, depending on the
/// publication selected by the executable pop. Freeze the distinction at join.
pub(in crate::resource::memory) struct PeerResult {
    /// Allocation constructor whose population holds this reservation.
    pub(in crate::resource::memory) site: RootId,
    /// One while this group of local strong handles is a peer, zero when it carries the charge.
    pub(super) borrowed: Expr,
    /// Live charge of this result, including a subsequent transfer from an alias.
    pub(super) bytes: Expr,
    /// Checked upper on the same visit's peers still to reconcile. None uses
    /// the site-wide bound when a publication multiplicity is unknown.
    remaining: Option<Expr>,
}

/// Peer reservations have a global count and, for an observed constructor,
/// a counter reset at each actual Arc::new. Neither counter charges bytes.
pub(in crate::resource::memory) struct Peers {
    /// Outstanding reservations across every visit to this source site.
    pub(in crate::resource::memory) population: Population,
    /// Observed destination forests for candidate loop invariants.
    pub(in crate::resource::memory) destinations: BTreeSet<VarIdent>,
    /// Publications since this occurrence's executable constructor.
    issued: Option<Expr>,
    /// A constant family-count candidate applies only to peers at the constructor's loop depth.
    single_visit: bool,
    /// Maximum peers proved at each carrying publication.
    limits: BTreeMap<WorkerId, u64>,
}

impl Analysis<'_> {
    pub(super) fn register_peer(
        &mut self,
        span: &Span,
        actor: WorkerId,
        root: RootId,
        destination: &VarIdent,
    ) {
        let constructor = self.transitions.shared_constructor(root);
        let same_visit = constructor.is_some_and(|(_, coordinates)| {
            self.growth.worker_occurrences.get(&actor).is_some_and(|worker| {
                worker.iter().map(|(site, _)| site).eq(coordinates.iter().map(|(site, _)| site))
            })
        });
        let site = constructor.map(|(site, _)| site);
        let peers = self.growth.occurrence_peers.entry(root).or_insert_with(|| {
            let population = Population::new(span, &mut self.growth.declarations);
            let issued = site.map(|site| {
                let zero = expr::integer(span, 0);
                let (issued, declaration) = expr::local(
                    span,
                    "peers_this_visit",
                    zero.typ.clone(),
                    zero.clone(),
                    Mode::Spec,
                );
                self.growth.declarations.push(declaration);
                self.growth.after.entry(site).or_default().push(expr::assign(span, &issued, zero));
                issued
            });
            Peers {
                population,
                destinations: BTreeSet::new(),
                issued,
                single_visit: true,
                limits: BTreeMap::new(),
            }
        });
        peers.single_visit &= same_visit;
        peers.destinations.insert(destination.clone());
        let statements = self.growth.after.entry(span.id).or_default();
        peers.population.publish(actor, 1, span, statements);
        if let Some(issued) = &peers.issued {
            statements.push(expr::assign(
                span,
                issued,
                contracts::add(span, issued.clone(), expr::integer(span, 1)),
            ));
        }
    }

    pub(super) fn check_peer_limit(&mut self, span: &Span, actor: WorkerId, root: RootId) {
        let Some(peers) = self.growth.occurrence_peers.get_mut(&root) else { return };
        let Some(issued) = &peers.issued else { return };
        let limit = match peers.limits.get(&actor) {
            Some(limit) => *limit,
            None if peers.single_visit => peers.population.weights.len() as u64,
            None => return,
        };
        // The number of source families proposes the bound. Every actual
        // insertion must prove it against this constructor's publication count.
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            crate::ast_util::mk_ineq(
                span,
                issued,
                &contracts::literal(span, limit),
                InequalityOp::Le,
            ),
            "cannot prove the number of peer publications for this allocation visit",
        ));
        peers.limits.insert(actor, limit);
    }

    pub(in crate::resource::memory::workers) fn selected_peer(
        &mut self,
        span: &Span,
        occurrence: &Occurrence,
    ) -> Result<Option<PeerResult>, VirErr> {
        let sites: BTreeSet<_> = occurrence
            .templates
            .iter()
            .filter_map(|actor| self.growth.occurrence_roots.get(actor).copied())
            .collect();
        if !sites.iter().any(|site| self.growth.occurrence_peers.contains_key(site)) {
            return Ok(None);
        }
        self.require_indexed_claim_owner(span)?;
        if sites.len() != 1 {
            return Err(unsupported(
                span,
                "mixed allocation sites with different peer reservations",
            ));
        }
        let site = *sites.first().unwrap();
        let peers = &self.growth.occurrence_peers[&site];
        let weight = peers
            .population
            .selected_weight(span, occurrence)
            .unwrap_or_else(|| expr::integer(span, 0));
        let limit = occurrence
            .templates
            .iter()
            .filter(|actor| !peers.population.weights.contains_key(actor))
            .map(|actor| peers.limits.get(actor).copied())
            .collect::<Option<Vec<_>>>()
            .map(|limits| limits.into_iter().max().unwrap_or(0));
        let remaining = limit.map(|n| {
            self.metadata_local(span, "shared_remaining_peers", contracts::literal(span, n))
        });
        let borrowed = self.metadata_local(span, "returned_peer", weight);
        let bytes = self.metadata_local(span, "shared_result_bytes", expr::integer(span, 0));
        Ok(Some(PeerResult { site, borrowed, bytes, remaining }))
    }

    fn check_carrier_release(
        &self,
        span: &Span,
        site: RootId,
        borrowed: Expr,
        remaining: Option<&Expr>,
        proofs: &mut Vec<Stmt>,
    ) {
        let peers = &self.growth.occurrence_peers[&site];
        let idle = crate::ast_util::mk_eq(span, &peers.population.pending, &expr::integer(span, 0));
        let peer = crate::ast_util::mk_eq(span, &borrowed, &expr::integer(span, 1));
        let mut released = vec![peer, idle];
        if let Some(remaining) = remaining {
            released.push(crate::ast_util::mk_eq(span, remaining, &expr::integer(span, 0)));
        }
        proofs.push(expr::check(
            span,
            crate::ast_util::disjoin(span, &released),
            "cannot release a shared backing while an indexed peer can still own it",
        ));
    }

    pub(in crate::resource::memory::workers) fn check_joined_carrier(
        &self,
        span: &Span,
        role: &PeerResult,
        proofs: &mut Vec<Stmt>,
    ) {
        self.check_carrier_release(
            span,
            role.site,
            role.borrowed.clone(),
            role.remaining.as_ref(),
            proofs,
        )
    }

    pub(in crate::resource::memory) fn peer_release_checks(
        &self,
        root: RootId,
        backing: &Owner,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        if let Some(role) = self.growth.peer_results.get(&root) {
            if !backing.dynamic.is_some_and(|id| self.storage.contains_allocation(id)) {
                proofs.push(expr::check(
                    span,
                    crate::ast_util::mk_bool(span, false),
                    "cannot retire an indexed Arc result outside its charging scope",
                ));
                return;
            }
            // Prefer a live result that demonstrably names the *same visit*.
            // A handoff retires its peer reservation and moves the original
            // bytes. Equal extents or the same allocation site are insufficient.
            let mut retired = role.borrowed.clone();
            for (other, survivor) in &self.growth.peer_results {
                if *other == root
                    || survivor.site != role.site
                    || !self.heap.shared.owns_result_charge(*other, &self.storage)
                {
                    continue;
                }
                let same = crate::ast_util::mk_eq(
                    span,
                    &self.growth.shared_occurrences[&root],
                    &self.growth.shared_occurrences[other],
                );
                let chosen = role.reconcile_survivor(
                    span,
                    survivor,
                    same,
                    &retired,
                    &self.growth.occurrence_peers[&role.site].population.pending,
                    proofs,
                );
                retired = contracts::add(span, retired, chosen);
            }
            self.check_carrier_release(
                span,
                role.site,
                retired.clone(),
                role.remaining.as_ref(),
                proofs,
            );
            self.growth.occurrence_peers[&role.site].population.release(
                span,
                retired,
                "cannot retire the returned allocation peer",
                proofs,
            );
        } else if self.growth.occurrence_peers.contains_key(&root) {
            self.check_carrier_release(span, root, expr::integer(span, 0), None, proofs);
        }
    }
}

impl PeerResult {
    /// Reconcile one candidate against the dying root. A successful handoff
    /// consumes one peer reservation and moves the entire byte charge.
    fn reconcile_survivor(
        &self,
        span: &Span,
        survivor: &Self,
        same: Expr,
        retired: &Expr,
        pending: &Expr,
        proofs: &mut Vec<Stmt>,
    ) -> Expr {
        let zero = expr::integer(span, 0);
        let one = expr::integer(span, 1);
        let take = crate::ast_util::conjoin(
            span,
            &vec![
                crate::ast_util::mk_eq(span, retired, &zero),
                crate::ast_util::mk_eq(span, &survivor.borrowed, &one),
                same.clone(),
            ],
        );
        // Snapshot the decision before updating the survivor's reservation.
        let transfer = select(span, take, one.clone(), zero.clone());
        let (chosen, declaration) =
            expr::local(span, "shared_handoff", transfer.typ.clone(), transfer, Mode::Spec);
        proofs.push(declaration);
        let moved = select(
            span,
            crate::ast_util::mk_eq(span, &chosen, &one),
            self.bytes.clone(),
            zero.clone(),
        );
        if let Some(remaining) = &survivor.remaining {
            // A peer dropping in front of a live carrier reconciles
            // one real reservation for this key. If the carrier itself
            // drops, its successor inherits the residual obligation.
            let peer_retired = crate::ast_util::conjoin(
                span,
                &vec![
                    same,
                    crate::ast_util::mk_eq(span, &self.borrowed, &one),
                    crate::ast_util::mk_eq(span, &survivor.borrowed, &zero),
                ],
            );
            let previous = contracts::subtract(
                span,
                remaining.clone(),
                select(span, peer_retired, one.clone(), zero.clone()),
            );
            let replacement = self.remaining.as_ref().unwrap_or(pending).clone();
            let left = select(
                span,
                crate::ast_util::mk_eq(span, &chosen, &one),
                contracts::subtract(span, replacement, one.clone()),
                previous,
            );
            proofs.push(expr::assign(
                span,
                remaining,
                contracts::maximum(span, zero.clone(), left),
            ));
        }
        proofs.push(expr::assign(
            span,
            &survivor.bytes,
            contracts::add(span, survivor.bytes.clone(), moved),
        ));
        proofs.push(expr::assign(
            span,
            &survivor.borrowed,
            contracts::subtract(span, survivor.borrowed.clone(), chosen.clone()),
        ));
        chosen
    }
}
