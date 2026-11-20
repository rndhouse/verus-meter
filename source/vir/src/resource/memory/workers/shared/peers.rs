//! Source-checked reservations for independently retained workers that share one allocation visit.
use super::*;

mod forwarded;
mod nested;

/// One received Arc may be the charged owner or a peer, depending on the
/// publication selected by the executable pop. Freeze the distinction at join.
#[derive(Clone)]
pub(in crate::resource::memory) struct PeerResult {
    /// Allocation constructor whose population holds this reservation.
    pub(in crate::resource::memory) site: RootId,
    /// One while this group of local strong handles is a peer, zero when it carries the charge.
    pub(super) borrowed: Expr,
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
    /// Candidate extent per construction for the loop allocating these peers.
    pub(in crate::resource::memory) publication: Option<(u64, Expr)>,
    /// Families actually collected in each loop, used to propose checked drain invariants.
    pub(in crate::resource::memory) joins: BTreeMap<u64, BTreeSet<WorkerId>>,
    /// Byte charges awaiting retirement of their own visit’s outstanding peers.
    pub(in crate::resource::memory) deferred: Option<super::deferred::Deferred>,
}

impl Analysis<'_> {
    pub(super) fn register_peer(
        &mut self,
        span: &Span,
        actor: WorkerId,
        root: RootId,
        destination: &VarIdent,
        backing: &Owner,
    ) {
        let constructor = self.transitions.shared_constructor(root);
        let same_visit = constructor.is_some_and(|(_, coordinates)| {
            self.growth.worker_occurrences.get(&actor).is_some_and(|worker| {
                worker.iter().map(|(site, _)| site).eq(coordinates.iter().map(|(site, _)| site))
            })
        });
        let site = constructor.map(|(site, _)| site);
        let (deferred, publication) = site
            .and_then(|site| self.growth.publication_ledgers.remove(&site))
            .map(|prepared| {
                let extent = self
                    .owner_upper(span, backing)
                    .remove(&crate::resource::memory::footprint::MemoryKind::host_heap())
                    .expect("Arc backing extent");
                prepared.bind(extent, &self.bound)
            })
            .unzip();
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
                deferred,
                publication,
                joins: BTreeMap::new(),
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
        // A forwarded capture names a joined result locally. Its reservation
        // still belongs to the original constructor, even in a second vector.
        let sites: BTreeSet<_> = occurrence
            .templates
            .iter()
            .filter_map(|actor| self.growth.occurrence_roots.get(actor))
            .map(|root| self.growth.peer_results.get(root).map_or(*root, |role| role.site))
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
        let peers = self.growth.occurrence_peers.get_mut(&site).unwrap();
        for id in &self.growth.loop_regions {
            peers.joins.entry(*id).or_default().extend(&occurrence.templates);
        }
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
        // Uniform membership already fixes the role across every possible
        // publication. Only a mixed selection needs to freeze the role at join.
        let borrowed = if contracts::constant(&weight).is_some() {
            weight
        } else {
            self.metadata_local(span, "returned_peer", weight)
        };
        let remaining = limit.filter(|_| contracts::constant(&borrowed) != Some(1)).map(|n| {
            self.metadata_local(span, "shared_remaining_peers", contracts::literal(span, n))
        });
        Ok(Some(PeerResult { site, borrowed, remaining }))
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

    /// A worker that consumes its alias has no result link to observe. Recover
    /// the visit from the actual captured field of the selected publication.
    pub(in crate::resource::memory::workers) fn finish_joined_carrier(
        &mut self,
        span: &Span,
        role: &PeerResult,
        occurrence: &Occurrence,
        owner: &Owner,
        proofs: &mut Vec<Stmt>,
    ) -> Result<(), VirErr> {
        let inputs = expr::operation(
            span,
            "worker_inputs",
            vec![occurrence.record.clone()],
            expr::memory_type(),
        );
        let mut identity = None;
        for actor in &occurrence.templates {
            let execution = &self.growth.worker_executions[actor];
            let captured_root = self.growth.occurrence_roots.get(actor).copied();
            let mut path = None;
            if let Some(captures) = &execution.entry.storage.owner {
                captures.visit_paths(&mut Vec::new(), &mut |slots, node| {
                    if captured_root.is_some()
                        && node.shared.and_then(StrongLink::known) == captured_root
                    {
                        path = Some(expr::path(
                            span,
                            slots.iter().map(|s| self.layouts.metadata_slot(s)),
                        ));
                    }
                });
            }
            let Some(path) = path else {
                self.check_carrier_release(
                    span,
                    role.site,
                    role.borrowed.clone(),
                    role.remaining.as_ref(),
                    proofs,
                );
                return Ok(());
            };
            let visit = expr::field(
                span,
                expr::lookup(span, inputs.clone(), path),
                "reference_identity",
                expr::sequence_type(crate::ast_util::int_typ()),
            );
            // Selection already proved membership in this finite set.
            identity = Some(match identity {
                None => visit,
                Some(previous) => {
                    let family = expr::operation(
                        span,
                        "worker_matches",
                        vec![occurrence.record.clone(), expr::path(span, actor.descriptor())],
                        crate::ast_util::bool_typ(),
                    );
                    let identity_type = visit.typ.clone();
                    SpannedTyped::new(
                        span,
                        &identity_type,
                        ExprX::If(family, visit, Some(previous)),
                    )
                }
            });
        }
        let charge =
            owner.dynamic.filter(|id| self.storage.contains_allocation(*id)).ok_or_else(|| {
                unsupported(span, "a joined allocation peer outside its charging scope")
            })?;
        let packed = self.storage.dynamic_cost(span, charge);
        let (bytes, _) = super::occurrences::split_carried_charge(span, packed, proofs);
        self.finish_peer_backing(
            span,
            role,
            identity.expect("selected worker family"),
            bytes,
            proofs,
        );
        Ok(())
    }

    fn finish_peer_backing(
        &mut self,
        span: &Span,
        role: &PeerResult,
        visit: Expr,
        bytes: Expr,
        proofs: &mut Vec<Stmt>,
    ) {
        let site = role.site;
        // A peer that ends before a joined carrier discharges one reservation
        // of that carrier only when both frozen allocation identities agree.
        let zero = expr::integer(span, 0);
        let one = expr::integer(span, 1);
        if contracts::constant(&role.borrowed) == Some(1)
            && self.current_worker.is_none()
            && self.heap.shared.has_strong(site)
            && self.growth.nested_peers.values().any(|root| *root == site)
            && let Some(issued) = &self.growth.occurrence_peers[&site].issued
        {
            let same = crate::ast_util::mk_eq(span, &visit, &self.growth.shared_occurrences[&site]);
            let debit = select(span, same, one.clone(), zero.clone());
            let next = contracts::subtract(span, issued.clone(), debit);
            proofs.push(expr::check(
                span,
                crate::ast_util::mk_ineq(span, &zero, &next, InequalityOp::Le),
                "cannot retire another visit's local inner reservation",
            ));
            proofs.push(expr::assign(span, issued, next));
        }
        for (root, carrier) in &self.growth.peer_results {
            let Some(remaining) = &carrier.remaining else { continue };
            if contracts::constant(&role.borrowed) == Some(0)
                || carrier.site != site
                || !self.heap.shared.owns_result_charge(*root, &self.storage)
            {
                continue;
            }
            let ends_peer = crate::ast_util::conjoin(
                span,
                &vec![
                    crate::ast_util::mk_eq(span, &role.borrowed, &one),
                    crate::ast_util::mk_eq(span, &carrier.borrowed, &zero),
                    crate::ast_util::mk_eq(span, &visit, &self.growth.shared_occurrences[root]),
                ],
            );
            let debit = select(span, ends_peer, one.clone(), zero.clone());
            proofs.push(expr::assign(
                span,
                remaining,
                contracts::maximum(
                    span,
                    zero.clone(),
                    contracts::subtract(span, remaining.clone(), debit),
                ),
            ));
        }
        self.ensure_deferred(span, site);
        let peers = &self.growth.occurrence_peers[&site];
        let deferred = peers.deferred.as_ref().unwrap();
        if !deferred.owned(&self.storage) {
            // Another path or section owns this ledger. Its existing charge
            // survives, and this destructor must justify releasing its own.
            self.check_carrier_release(
                span,
                site,
                role.borrowed.clone(),
                role.remaining.as_ref(),
                proofs,
            );
            return;
        }
        let pending = &peers.population.pending;
        let remaining = role.remaining.clone().unwrap_or_else(|| pending.clone());
        let publication =
            peers.publication.as_ref().is_some_and(|(id, _)| self.growth.loop_regions.contains(id));
        deferred.finish(
            span,
            visit,
            bytes,
            remaining,
            role.borrowed.clone(),
            pending,
            publication,
            proofs,
        );
    }

    pub(in crate::resource::memory) fn peer_release_checks(
        &mut self,
        root: RootId,
        backing: &Owner,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        if let Some(role) = self.growth.peer_results.get(&root).cloned() {
            let Some(id) = backing.dynamic.filter(|id| self.storage.contains_allocation(*id))
            else {
                proofs.push(expr::check(
                    span,
                    crate::ast_util::mk_bool(span, false),
                    "cannot retire an indexed Arc result outside its charging scope",
                ));
                return;
            };
            self.finish_peer_backing(
                span,
                &role,
                self.growth.shared_occurrences[&root].clone(),
                self.storage.dynamic_cost(span, id),
                proofs,
            );
            self.growth.occurrence_peers[&role.site].population.release(
                span,
                role.borrowed,
                "cannot retire the returned allocation peer",
                proofs,
            );
        } else if let Some(peers) = self.growth.occurrence_peers.get(&root) {
            if peers
                .publication
                .as_ref()
                .is_some_and(|(id, _)| self.growth.loop_regions.last() == Some(id))
                && !self.growth.section_shared.contains(&root)
                && self.current_worker.is_none()
                && peers.deferred.as_ref().is_some_and(|d| d.owned(&self.storage))
                && let Some(bytes) = self.local_peer_bytes(span, backing)
            {
                // The fixed worker returned the original allocation. Its last
                // direct drop transfers the full payload charge to outstanding
                // peers of this visit. The original owner is destroyed next.
                let (_, coordinates) =
                    self.transitions.shared_constructor(root).expect("publication constructor");
                let visit = &self.growth.shared_occurrences[&root];
                proofs.push(expr::check(
                    span,
                    crate::ast_util::mk_eq(span, visit, &root.occurrence(span, coordinates)),
                    "cannot establish the local owner's allocation visit",
                ));
                let role = PeerResult {
                    site: root,
                    borrowed: expr::integer(span, 0),
                    remaining: peers.issued.clone(),
                };
                self.finish_peer_backing(
                    span,
                    &role,
                    self.growth.shared_occurrences[&root].clone(),
                    bytes,
                    proofs,
                );
                return;
            }
            self.check_carrier_release(span, root, expr::integer(span, 0), None, proofs);
        }
    }
}
