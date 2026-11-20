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
    /// Each live deferred backing needs at least one outstanding reference.
    /// When installed, every deposit checks this immutable per-backing upper bound.
    per_backing: Option<(Expr, Expr)>,
    /// One host-heap charge covering the retained extents in the publishing scope.
    allocation: u64,
}

impl Deferred {
    pub(super) fn new(span: &Span, growth: &mut Growth, storage: &mut Accounting) -> Self {
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
        let deferred = Self { entries, empty, allocation, per_backing: None };
        storage.set_allocation(allocation, MemoryKind::host_heap(), deferred.bytes(span));
        deferred
    }

    pub(in crate::resource::memory) fn history_bytes(&self, span: &Span) -> Expr {
        expr::operation(
            span,
            "deferred_bytes",
            vec![self.entries.clone()],
            crate::ast_util::int_typ(),
        )
    }

    pub(in crate::resource::memory) fn bytes(&self, span: &Span) -> Expr {
        let history = self.history_bytes(span);
        match &self.per_backing {
            None => history,
            Some((extent, pending)) => contracts::minimum(
                span,
                history,
                contracts::multiply(span, extent.clone(), pending.clone()),
            ),
        }
    }

    /// The history and the population are independent upper bounds. Stale
    /// conservative history entries may outlive a visit, but a real retained
    /// allocation always needs an outstanding reservation for its own identity.
    pub(super) fn bound_by_reservations(
        &mut self,
        span: &Span,
        extent: Expr,
        pending: Expr,
        storage: &mut Accounting,
    ) {
        if self.per_backing.is_none() {
            self.per_backing = Some((extent, pending));
            storage.set_allocation(self.allocation, MemoryKind::host_heap(), self.bytes(span));
        }
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
        publication: bool,
        proofs: &mut Vec<Stmt>,
    ) {
        if let Some((extent, _)) = &self.per_backing {
            proofs.push(expr::check(
                span,
                crate::ast_util::mk_ineq(span, &bytes, extent, InequalityOp::Le),
                "cannot establish the byte bound for this retained allocation",
            ));
        }
        let laws = SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::Fuel(expr::function("group_deferred_backings"), 1, true),
        );
        proofs.push(crate::def::Spanned::new(span.clone(), StmtX::Expr(laws)));
        let args = vec![self.entries.clone(), visit, bytes, remaining, retired, pending.clone()];
        if publication {
            proofs.push(expr::lemma(span, "finish_peer_bound", args.clone()));
        }
        let next = expr::operation(span, "finish_peer_backing", args, self.entries.typ.clone());
        proofs.push(expr::assign(span, &self.entries, next));
    }
}

/// The caller's waiting frame and any peer backing held at its pre-join cost.
#[must_use = "receive the result before accounting for the resumed caller"]
pub(in crate::resource::memory::workers) struct WaitingJoin {
    /// All caller storage observed after evaluating the join operand.
    frame: Footprint,
    /// Allocation and live byte expression to restore after observing the result.
    resumed_backing: Vec<(u64, Expr)>,
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

    /// Receiving a fixed worker's exit state can run a nested payload's last
    /// destructor. Snapshot the ledgers this frame already owns, including
    /// backings reachable through another Arc. A ledger first created by the
    /// destructor contributes only to the resumed frame.
    pub(in crate::resource::memory::workers) fn wait_for_fixed_join(
        &mut self,
        span: &Span,
    ) -> WaitingJoin {
        let sites: Vec<_> = self
            .growth
            .occurrence_peers
            .iter()
            .filter_map(|(site, peers)| {
                peers.deferred.as_ref()?.owned(&self.storage).then_some(*site)
            })
            .collect();
        self.wait_for_join_result(span, sites)
    }

    pub(in crate::resource::memory::workers) fn wait_for_join_result(
        &mut self,
        span: &Span,
        sites: impl IntoIterator<Item = RootId>,
    ) -> WaitingJoin {
        let resumed_backing = sites
            .into_iter()
            .filter_map(|site| {
                self.ensure_deferred(span, site);
                let deferred = self.growth.occurrence_peers[&site].deferred.as_ref().unwrap();
                if !deferred.owned(&self.storage) {
                    return None;
                }
                let allocation = deferred.allocation;
                let live_bytes = deferred.bytes(span);
                let waiting_bytes =
                    self.metadata_local(span, "waiting_peer_bytes", live_bytes.clone());
                self.storage.set_allocation(allocation, MemoryKind::host_heap(), waiting_bytes);
                Some((allocation, live_bytes))
            })
            .collect();
        WaitingJoin {
            frame: self.storage.worker_frame(span, states::Phase::Waiting, |cost| cost),
            resumed_backing,
        }
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
        let ready = storage.worker_frame(span, states::Phase::Ready, |cost| {
            states::completed(span, cost, inline_bytes)
        });
        for (allocation, live_bytes) in self.resumed_backing {
            storage.set_allocation(allocation, MemoryKind::host_heap(), live_bytes);
        }
        (self.frame, ready)
    }
}
