//! Keep the original backing in the publisher while unjoined peers may retain
//! it. Retirement uses the selected allocation visit and the verified bound on
//! its remaining reservations, independently of where the handle is stored.
use super::*;
use crate::resource::memory::{
    footprint::{Footprint, MemoryKind},
    growth::Growth,
    workers::states,
};

/// Publisher-owned accounting for all deferred visits to one constructor.
pub(in crate::resource::memory) struct Deferred {
    /// Mutable proof local containing the visit, extent and remaining peer count.
    entries: Expr,
    /// Typed empty sequence used at initialization, loop heads and exits.
    empty: Expr,
    /// One host-heap charge whose amount is the sum of the retained extents.
    allocation: u64,
}

impl Deferred {
    fn new(span: &Span, growth: &mut Growth, storage: &mut Accounting) -> Self {
        let entry = std::sync::Arc::new(TypX::Datatype(
            Dt::Path(
                crate::path!(CrateId::Vstd => "std_specs", "resource", "memory", "peers", "DeferredBacking"),
            ),
            Default::default(),
            Default::default(),
        ));
        let empty = expr::empty(span, entry);
        let (entries, declaration) = expr::local(
            span,
            "deferred_peer_backings",
            empty.typ.clone(),
            empty.clone(),
            Mode::Spec,
        );
        growth.declarations.push(declaration);
        // Earlier points in the first reusable visit have no ledger allocation.
        // They may be revisited only after this visit's temporary handoffs clear.
        for id in &growth.loop_regions {
            growth.loops.entry(*id).or_default().push(expr::purpose(
                crate::ast_util::mk_eq(span, &entries, &empty),
                "deferred peer backings at the loop head",
            ));
        }
        let allocation = Accounting::fresh_allocation();
        let deferred = Self { entries, empty, allocation };
        storage.set_allocation(allocation, MemoryKind::host_heap(), deferred.bytes(span));
        deferred
    }

    pub(in crate::resource::memory) fn bytes(&self, span: &Span) -> Expr {
        expr::operation(
            span,
            "deferred_bytes",
            vec![self.entries.clone()],
            crate::ast_util::int_typ(),
        )
    }

    /// Each accounting exit has proved that no bytes remain on this allocation.
    pub(super) fn release(&self, storage: &mut Accounting) {
        storage.release_dynamic(self.allocation);
    }

    pub(in crate::resource::memory) fn empty(&self, span: &Span) -> Expr {
        crate::ast_util::mk_eq(span, &self.entries, &self.empty)
    }

    pub(in crate::resource::memory) fn owned(&self, storage: &Accounting) -> bool {
        storage.contains_allocation(self.allocation)
    }

    /// A retiring peer can discharge an earlier carrier for this visit. A
    /// retiring carrier may instead have to leave its extent here. When no
    /// reservations remain anywhere at the site, all such extents can end.
    pub(super) fn finish(
        &self,
        span: &Span,
        visit: Expr,
        bytes: Expr,
        remaining: Expr,
        retired: Expr,
        pending: &Expr,
        proofs: &mut Vec<Stmt>,
    ) {
        let laws = SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::Fuel(expr::function("group_deferred_backings"), 1, true),
        );
        proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(laws)));
        let next = expr::operation(
            span,
            "finish_peer_backing",
            vec![self.entries.clone(), visit, bytes, remaining, retired, pending.clone()],
            self.entries.typ.clone(),
        );
        proofs.push(expr::assign(span, &self.entries, next));
    }
}

/// The caller's waiting frame and any peer backing held at its pre-join cost.
#[must_use = "receive the result before accounting for the resumed caller"]
pub(in crate::resource::memory::workers) struct WaitingJoin {
    /// All caller storage observed after evaluating the join operand.
    frame: Footprint,
    /// Allocation and live byte expression to restore after observing the result.
    resumed_backing: Option<(u64, Expr)>,
}

impl Analysis<'_> {
    /// A separate drain can inherit storage from an earlier iteration. Install
    /// the publisher's charge before taking any loop-head or waiting snapshots.
    pub(in crate::resource::memory) fn prepare_deferred_loop(
        &mut self,
        span: &Span,
    ) -> BTreeSet<RootId> {
        if self.current_worker.is_some() {
            return BTreeSet::new();
        }
        let fresh: BTreeSet<_> = self
            .growth
            .occurrence_peers
            .iter()
            .filter_map(|(site, peers)| peers.deferred.is_none().then_some(*site))
            .collect();
        for site in &fresh {
            self.ensure_deferred(span, *site);
        }
        fresh
    }

    pub(super) fn ensure_deferred(&mut self, span: &Span, site: RootId) {
        if self.growth.occurrence_peers[&site].deferred.is_none() {
            let deferred = Deferred::new(span, &mut self.growth, &mut self.storage);
            self.growth.occurrence_peers.get_mut(&site).unwrap().deferred = Some(deferred);
        }
    }

    pub(in crate::resource::memory::workers) fn wait_for_join_result(
        &mut self,
        span: &Span,
        consuming_peer: Option<&PeerResult>,
    ) -> WaitingJoin {
        let resumed_backing = consuming_peer.and_then(|peer| {
            self.ensure_deferred(span, peer.site);
            let deferred = self.growth.occurrence_peers[&peer.site].deferred.as_ref().unwrap();
            if !deferred.owned(&self.storage) {
                return None;
            }
            let allocation = deferred.allocation;
            let live_bytes = deferred.bytes(span);
            let waiting_bytes = self.metadata_local(span, "waiting_peer_bytes", live_bytes.clone());
            self.storage.set_allocation(allocation, MemoryKind::host_heap(), waiting_bytes);
            Some((allocation, live_bytes))
        });
        WaitingJoin { frame: self.storage.live_expression(span), resumed_backing }
    }
}

impl WaitingJoin {
    /// The delivered result coexists with the waiting charge. Only the resumed
    /// caller observes changes to the peer reservations made by this join.
    pub(in crate::resource::memory::workers) fn receive_result(
        self,
        span: &Span,
        storage: &mut Accounting,
        inline_bytes: u64,
    ) -> (Footprint, Footprint) {
        let ready = states::completed(span, storage.live_expression(span), inline_bytes);
        if let Some((allocation, live_bytes)) = self.resumed_backing {
            storage.set_allocation(allocation, MemoryKind::host_heap(), live_bytes);
        }
        (self.frame, ready)
    }
}
