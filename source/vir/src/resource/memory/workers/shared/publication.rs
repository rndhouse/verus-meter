//! Reserve storage at the loop head for peers that can survive across visits.
//! Only executable publications and last-owner drops update the reserved sum.

use super::*;
use crate::resource::memory::footprint::MemoryKind;
use std::{collections::HashSet, sync::Arc};

/// The site is reserved before any body observation. A checked publication
/// binds it to a concrete root and chooses a bound in the loop entry's scope.
pub(in crate::resource::memory) struct PublicationSite {
    /// Empty backing sum present in every storage observation from loop entry.
    deferred: Deferred,
    /// Source loop whose visit ordinal can bound new allocations.
    region: u64,
    /// Stable scalar bindings in scope before the first visit.
    inputs: Arc<HashSet<VarIdent>>,
}

impl PublicationSite {
    pub(super) fn bind(self, extent: Expr, fallback: &Expr) -> (Deferred, (u64, Expr)) {
        let in_scope = crate::ast_visitor::expr_visitor_check(&extent, &mut |scope, value| {
            if let ExprX::Var(name) = &value.x
                && !scope.contains_key(name)
                && !self.inputs.contains(name)
            {
                return Err(());
            }
            Ok(())
        })
        .is_ok();
        (self.deferred, (self.region, if in_scope { extent } else { fallback.clone() }))
    }
}

impl Analysis<'_> {
    /// A constructor may first publish a peer halfway through a reusable
    /// visit. Reserve its initially empty charge before any source point can
    /// observe earlier visits. Only checked publication can populate it.
    pub(in crate::resource::memory) fn prepare_publication_ledgers(
        &mut self,
        region: &Span,
        body: &Expr,
    ) -> Vec<u64> {
        use crate::visitor::VisitorControlFlow::{Recurse, Return};
        if self.current_worker.is_some() {
            return Vec::new();
        }
        let mut sites = Vec::new();
        let mut spawns = false;
        let mut joins = false;
        crate::ast_visitor::expr_visitor_walk(body, &mut |value| {
            if matches!(value.x, ExprX::NonSpecClosure { .. } | ExprX::Loop { .. }) {
                return Return;
            }
            if let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. } = &value.x
                && let Some(ResourceIntrinsic::Concurrency(op)) = attrs.resource_intrinsic
            {
                spawns |= op.spawns();
                joins |= op.joins();
                if op == crate::resource::memory::concurrency::Operation::ArcNew {
                    sites.push(value.span.id);
                }
            }
            Recurse
        });
        if sites.is_empty() || !spawns || !joins {
            return Vec::new();
        }
        let inputs: Arc<HashSet<VarIdent>> = Arc::new(
            self.stable_scalars
                .iter()
                .filter(|name| self.slots.contains_key(*name))
                .cloned()
                .collect(),
        );
        for site in &sites {
            let deferred = Deferred::new(&body.span, &mut self.growth, &mut self.storage);
            self.growth.publication_ledgers.insert(
                *site,
                PublicationSite { deferred, region: region.id, inputs: inputs.clone() },
            );
        }
        sites
    }

    /// A constructor without a peer never acquired a charge.
    pub(in crate::resource::memory) fn finish_publication_ledgers(
        &mut self,
        region: &Span,
        sites: Vec<u64>,
    ) {
        for site in sites {
            if let Some(unused) = self.growth.publication_ledgers.remove(&site) {
                // Earlier snapshots include this provisional charge. An isolated
                // iteration must prove it stays zero when this site never hands
                // its backing to an independently retained peer.
                let bytes = unused.deferred.bytes(region);
                self.growth.loops.entry(region.id).or_default().push(expr::purpose(
                    crate::ast_util::mk_eq(region, &bytes, &expr::integer(region, 0)),
                    "unused peer publication charge",
                ));
                unused.deferred.release(&mut self.storage);
            }
        }
    }

    /// A local last owner can transfer only a full, publisher-paid heap extent.
    /// Missing or foreign charges fall back to the ordinary release obligation.
    pub(super) fn local_peer_bytes(&self, span: &Span, backing: &Owner) -> Option<Expr> {
        if Self::check_occurrence_payload(span, backing).is_err() {
            return None;
        }
        let mut owned = true;
        backing.visit(&mut |node| {
            owned &= node.dynamic.is_none_or(|id| self.storage.contains_allocation(id));
            if let Some(elements) = &node.elements {
                owned &= elements
                    .states
                    .values()
                    .all(|id| self.storage.contains_allocation(self.growth.elements[*id].id));
            }
        });
        let mut charges = self.owner_charges(span, backing);
        let bytes = charges.remove(&MemoryKind::host_heap())?;
        (owned && charges.values().all(|v| contracts::constant(v) == Some(0))).then_some(bytes)
    }
}
