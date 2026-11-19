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
        for (site, peers) in &self.growth.occurrence_peers {
            let Some(families) = peers.joins.get(&span.id) else { continue };
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
            let mut sum = ledger.bytes(span);
            for charge in &record.charges {
                let Some((_, forest)) = record.reference_forests.get(&charge.location) else {
                    continue;
                };
                let ExprX::Var(name) = &forest.x else { continue };
                let Some(owners) = self.growth.forest_families.get(name) else { continue };
                let tag = contracts::literal(span, verus_meter_model::completion_bytes(0).unwrap());
                let tags = contracts::multiply(span, tag, charge.length.0.clone());
                if !owners.is_empty()
                    && owners.iter().all(|id| peers.population.weights.contains_key(id))
                {
                    // Only occupied peer slots carry completion tags. The
                    // vector's reserved inline handle slots are paid separately.
                    facts.push(expr::purpose(
                        crate::ast_util::mk_eq(span, &charge.current, &tags),
                        "completion tags in the peer handle collection",
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
            sums.push(sum);
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
