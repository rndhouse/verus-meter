//! Move a collected ownership group into another indexed worker. Its source
//! capture keeps the original visit in the worker record through subsequent pops.
use super::*;

impl Analysis<'_> {
    pub(in crate::resource::memory::workers::shared) fn index_forwarded_peer(
        &mut self,
        span: &Span,
        actor: WorkerId,
        forest: &Expr,
        root: RootId,
        backing: Owner,
        role: PeerResult,
    ) -> Result<(), VirErr> {
        self.require_indexed_claim_owner(span)?;
        Self::check_occurrence_payload(span, &backing)?;
        let ExprX::Var(destination) = &forest.x else {
            return Err(unsupported(
                span,
                "a forwarded publication without a named ownership forest",
            ));
        };
        if self.growth.occurrence_roots.insert(actor, root).is_some_and(|prior| prior != root) {
            return Err(unsupported(span, "a worker family with inconsistent forwarded ownership"));
        }
        self.ensure_deferred(span, role.site);
        let bytes = self.transfer_occurrence_backing(span, backing)?;
        let peers = self.growth.occurrence_peers.get_mut(&role.site).unwrap();
        let deferred = peers.deferred.as_ref().unwrap();
        if !deferred.owned(&self.storage) {
            return Err(unsupported(
                span,
                "indexing a forwarded Arc outside its original charging scope",
            ));
        }

        // A carrier deposits its bytes and adds one reservation for the relay.
        // A peer already owns that reservation and transfers it without a debit.
        // Neither transition publishes another peer at the original constructor.
        peers.destinations.insert(destination.clone());
        peers.population.weights.insert(actor, 1);
        let proofs = self.growth.after.entry(span.id).or_default();
        let zero = expr::integer(span, 0);
        let one = expr::integer(span, 1);
        let pending = &peers.population.pending;
        let carrier = crate::ast_util::mk_eq(span, &role.borrowed, &zero);
        let peer = crate::ast_util::conjoin(
            span,
            &vec![
                crate::ast_util::mk_eq(span, &role.borrowed, &one),
                crate::ast_util::mk_eq(span, &bytes, &zero),
                crate::ast_util::mk_ineq(span, &one, pending, InequalityOp::Le),
            ],
        );
        proofs.push(expr::check(
            span,
            crate::ast_util::disjoin(span, &vec![carrier, peer]),
            "cannot transfer the forwarded Arc's backing or its outstanding reservation",
        ));
        if contracts::constant(&role.borrowed) == Some(1) {
            return Ok(());
        }
        let added = contracts::subtract(span, one.clone(), role.borrowed);
        proofs.push(expr::assign(span, pending, contracts::add(span, pending.clone(), added)));
        let remaining =
            role.remaining.map_or_else(|| pending.clone(), |old| contracts::add(span, old, one));
        let publication =
            peers.publication.as_ref().is_some_and(|(id, _)| self.growth.loop_regions.contains(id));
        deferred.finish(
            span,
            self.growth.shared_occurrences[&root].clone(),
            bytes,
            remaining,
            zero,
            pending,
            publication,
            proofs,
        );
        Ok(())
    }
}
