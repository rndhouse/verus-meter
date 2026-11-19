//! Inductive byte bounds when a drain moves the last carrying handle's
//! allocation to the publisher on behalf of an independently retained peer.

use super::Loop;
use crate::ast::*;
use crate::ast_util::mk_ineq;
use crate::resource::memory::{
    analysis::Analysis,
    contracts,
    footprint::{MemoryKind, MemorySelection},
    metadata::expr,
    shared::RootId,
};
use std::collections::BTreeSet;

impl Analysis<'_> {
    /// Candidate bounds are checked on entry and on each executable back edge.
    pub(super) fn deferred_drain_bounds(
        &mut self,
        record: &Loop,
        fresh: &BTreeSet<RootId>,
        entry_heap: &Expr,
    ) -> Vec<Expr> {
        let span = &record.span;
        let mut facts = Vec::new();
        let mut sums = Vec::new();
        let mut peer_products = Vec::new();
        for (site, peers) in &self.growth.occurrence_peers {
            let publication = peers.publication.as_ref().filter(|(id, _)| *id == span.id);
            let empty = BTreeSet::new();
            let families = peers.joins.get(&span.id).unwrap_or(&empty);
            if families.is_empty() && publication.is_none() {
                continue;
            }
            let Some(ledger) = &peers.deferred else { continue };
            if !ledger.owned(&self.storage) {
                continue;
            }
            let carrier = |id| {
                self.growth.occurrence_roots.get(id) == Some(site)
                    && !peers.population.weights.contains_key(id)
            };
            let has_carrier = families.iter().any(carrier);
            let paired = fresh.contains(site)
                && has_carrier
                && peers.population.weights.keys().all(|id| families.contains(id));
            let mut sum =
                if publication.is_some() { ledger.history_bytes(span) } else { ledger.bytes(span) };
            let tag = verus_meter_model::completion_bytes(0).unwrap();
            let nested_only = peers
                .population
                .weights
                .keys()
                .all(|id| self.growth.nested_peers.get(id) == Some(site));
            let wrapper =
                verus_meter_model::arc_backing_bytes(verus_meter_model::reference_bytes(false))
                    .unwrap();
            let slot = if nested_only {
                verus_meter_model::completion_bytes(wrapper).unwrap()
            } else {
                tag
            };
            if nested_only && let Some((_, extent)) = &peers.publication {
                peer_products.push((extent.clone(), contracts::literal(span, slot)));
            }
            for charge in &record.charges {
                let Some((_, forest)) = record.reference_forests.get(&charge.location) else {
                    continue;
                };
                let ExprX::Var(name) = &forest.x else { continue };
                let Some(owners) = self.growth.forest_families.get(name) else { continue };
                let tags = contracts::multiply(
                    span,
                    contracts::literal(span, tag),
                    charge.length.0.clone(),
                );
                if !owners.is_empty()
                    && owners.iter().all(|id| {
                        peers.population.weights.contains_key(id)
                            && (nested_only || !self.growth.nested_peers.contains_key(id))
                    })
                {
                    // A nested peer also owns its wrapper; all other backing
                    // remains with the publisher. Prove the uniform slot cost.
                    let occupied = contracts::multiply(
                        span,
                        contracts::literal(span, slot),
                        charge.length.0.clone(),
                    );
                    facts.push(expr::purpose(
                        crate::ast_util::mk_eq(span, &charge.current, &occupied),
                        "occupied bytes in the peer handle collection",
                    ));
                } else if !paired
                    && has_carrier
                    && owners.iter().any(carrier)
                    && !record.grows_children(&charge.location)
                {
                    // A joined slot loses its completion tag. Its remaining
                    // charge can move to the deferred ledger without growing.
                    sum = contracts::add(
                        span,
                        sum,
                        contracts::subtract(span, charge.current.clone(), tags),
                    );
                }
            }
            if paired {
                // A paired drain may clear a fresh ledger on each back edge.
                // Actual allocation identities must establish this candidate.
                facts.push(expr::purpose(
                    ledger.empty(span),
                    "deferred peer backings at the loop head",
                ));
                continue;
            }
            if let Some((_, extent)) = publication {
                // Each construction in this body can contribute its extent once.
                // The actual updates must establish the bound at every back edge.
                let ordinal = self.growth.loop_occurrences[&span.id].clone();
                // Combine tags and backings in the same product as the
                // published per-visit storage. Both terms are source observations.
                let per_peer = contracts::literal(span, slot);
                let tags = contracts::multiply(
                    span,
                    per_peer.clone(),
                    contracts::literal(span, peers.population.weights.len() as u64),
                );
                let width = contracts::add(span, extent.clone(), tags);
                let upper = contracts::multiply(span, ordinal, width);
                sum = contracts::add(
                    span,
                    sum,
                    contracts::multiply(span, per_peer, peers.population.pending.clone()),
                );
                facts.push(expr::purpose(
                    mk_ineq(span, &sum, &upper, InequalityOp::Le),
                    "shared backings retained from completed publication visits",
                ));
            } else {
                sums.push(sum);
            }
        }
        for (extent, width) in peer_products {
            for schedule in [span, &record.body.span] {
                self.growth.before_loop_proof(
                    schedule,
                    expr::lemma(
                        schedule,
                        "peer_width_products",
                        vec![extent.clone(), width.clone()],
                    ),
                );
            }
        }
        if !sums.is_empty() {
            let law = SpannedTyped::new(
                span,
                &crate::ast_util::unit_typ(),
                ExprX::Fuel(expr::function("finish_peer_bound"), 1, true),
            );
            self.growth
                .before
                .entry(record.body.span.id)
                .or_default()
                .push(crate::def::Spanned::new(span.clone(), StmtX::Expr(law)));
            // Carry headroom for the observed inline temporaries into the
            // isolated loop proof. Each operation also checks its actual cost.
            let locals = MemorySelection::kind(MemoryKind::host_local());
            let peak = record
                .local_costs
                .iter()
                .filter_map(|(_, cost)| contracts::constant(&cost.select(span, &locals)))
                .max()
                .unwrap_or(0);
            let required = contracts::add(span, entry_heap.clone(), contracts::literal(span, peak));
            facts.push(expr::purpose(
                mk_ineq(span, &required, &self.bound, InequalityOp::Le),
                "available space for join temporaries",
            ));
        }
        for sum in sums {
            let initial = self.loop_snapshot(span, &sum);
            facts.push(expr::purpose(
                mk_ineq(span, &sum, &initial, InequalityOp::Le),
                "deferred and outstanding worker backing bytes",
            ));
        }
        facts
    }
}
