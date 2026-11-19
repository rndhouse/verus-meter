//! A worker can own a wrapper while holding a reservation on an independently
//! shared inner allocation. The wrapper and the inner backing have different
//! final drops. Only the latter goes through the per-visit peer accounting.
use super::*;
use crate::resource::memory::workers::PayloadHandle;

impl Analysis<'_> {
    /// The caller has already moved the actual child links out of the wrapper.
    /// Any still-open root needs a reservation that its join can reconstruct.
    pub(in crate::resource::memory::workers::shared) fn publish_nested_peer(
        &mut self,
        span: &Span,
        actor: WorkerId,
        outer: RootId,
        direct: Option<RootId>,
        open: BTreeMap<RootId, (u64, Owner)>,
        forest: &Expr,
    ) -> Result<(), VirErr> {
        if self.growth.occurrence_links.contains_key(&actor)
            && self.growth.nested_peers.get(&actor) != open.keys().next()
        {
            return Err(unsupported(span, "a worker family with varying inner reservations"));
        }
        for (root, (count, child)) in open {
            if direct != Some(root)
                || count != 1
                || self.growth.payload_handles.get(&actor) != Some(&PayloadHandle::Strong)
                || self.growth.occurrence_peers.contains_key(&outer)
            {
                return Err(unsupported(
                    span,
                    "an independent nested alias without its direct published handle",
                ));
            }
            let ExprX::Var(destination) = &forest.x else {
                return Err(unsupported(span, "a nested peer without its destination collection"));
            };
            Self::check_occurrence_payload(span, &child)?;
            let first = !self.growth.occurrence_peers.contains_key(&root);
            self.register_peer(span, actor, root, destination, &child);
            self.growth.nested_peers.insert(actor, root);
            if first && self.growth.loop_regions.len() == 1 {
                let peers = self.growth.occurrence_peers.get_mut(&root).unwrap();
                if let (Some((_, extent)), Some(ledger)) = (&peers.publication, &mut peers.deferred)
                    && ledger.owned(&self.storage)
                {
                    ledger.bound_by_reservations(
                        span,
                        extent.clone(),
                        peers.population.pending.clone(),
                        &mut self.storage,
                    );
                }
            }
        }
        Ok(())
    }

    /// All alternatives at a join must agree on which inner constructor it
    /// reserves. The selected publication supplies the particular visit.
    pub(in crate::resource::memory::workers) fn selected_nested_peer(
        &mut self,
        span: &Span,
        occurrence: &Occurrence,
    ) -> Result<Option<RootId>, VirErr> {
        let Some(site) =
            occurrence.templates.iter().find_map(|id| self.growth.nested_peers.get(id)).copied()
        else {
            return Ok(None);
        };
        self.require_indexed_claim_owner(span)?;
        if !occurrence.templates.iter().all(|id| self.growth.nested_peers.get(id) == Some(&site)) {
            return Err(unsupported(
                span,
                "a mixed nested Arc result without a common reservation",
            ));
        }
        let peers = self.growth.occurrence_peers.get_mut(&site).unwrap();
        for region in &self.growth.loop_regions {
            peers.joins.entry(*region).or_default().extend(&occurrence.templates);
        }
        Ok(Some(site))
    }

    /// The wrapper was destroyed by the worker. Its actual join retires the
    /// inner reference against the recorded visit before the population debit.
    pub(in crate::resource::memory::workers) fn finish_consumed_wrapper(
        &mut self,
        span: &Span,
        site: RootId,
        occurrence: &Occurrence,
    ) {
        let identity = Self::published_inner_identity(span, occurrence);
        let role = PeerResult { site, borrowed: expr::integer(span, 1), remaining: None };
        let mut proofs = Vec::new();
        self.finish_peer_backing(span, &role, identity, expr::integer(span, 0), &mut proofs);
        self.growth.before.entry(span.id).or_default().extend(proofs);
    }

    /// The wrapper's direct child keeps its reservation through cloning and
    /// extraction. The zero-byte allocation marks its receiving accounting scope.
    pub(in crate::resource::memory::workers::shared) fn restore_nested_peer(
        &mut self,
        span: &Span,
        site: RootId,
        identity: Expr,
    ) -> Owner {
        let zero = expr::integer(span, 0);
        let allocation = Accounting::fresh_allocation();
        self.storage.set_allocation(
            allocation,
            crate::resource::memory::footprint::MemoryKind::host_heap(),
            zero.clone(),
        );
        let child = self.heap.shared.insert(Owner {
            dynamic: Some(allocation),
            extent: Some(zero),
            ..Default::default()
        });
        let root = child.shared.unwrap().known().unwrap();
        self.growth
            .peer_results
            .insert(root, PeerResult { site, borrowed: expr::integer(span, 1), remaining: None });
        self.growth.shared_occurrences.insert(root, identity);
        child
    }
}
