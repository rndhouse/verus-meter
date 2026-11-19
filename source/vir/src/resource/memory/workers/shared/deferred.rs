//! Keep the original backing in the publisher while unjoined peers may retain
//! it. Retirement uses the selected allocation visit and the verified bound on
//! its remaining reservations, independently of where the handle is stored.
use super::*;
use crate::resource::memory::{footprint::MemoryKind, growth::Growth};

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
        let deferred = Self { entries, empty, allocation };
        deferred.resume(span, storage);
        deferred
    }

    pub(super) fn bytes(&self, span: &Span) -> Expr {
        expr::operation(
            span,
            "deferred_bytes",
            vec![self.entries.clone()],
            crate::ast_util::int_typ(),
        )
    }

    pub(in crate::resource::memory::workers) fn resume(
        &self,
        span: &Span,
        storage: &mut Accounting,
    ) {
        self.charge(storage, self.bytes(span));
    }

    pub(super) fn charge(&self, storage: &mut Accounting, bytes: Expr) {
        storage.set_allocation(self.allocation, MemoryKind::host_heap(), bytes);
    }

    /// Each accounting exit has proved that no bytes remain on this allocation.
    pub(super) fn release(&self, storage: &mut Accounting) {
        storage.release_dynamic(self.allocation);
    }

    pub(in crate::resource::memory) fn empty(&self, span: &Span) -> Expr {
        crate::ast_util::mk_eq(span, &self.entries, &self.empty)
    }

    pub(super) fn owned(&self, storage: &Accounting) -> bool {
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
