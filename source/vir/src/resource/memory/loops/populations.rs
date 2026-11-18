//! Checked loop-prefix obligations for collections of outstanding workers.

use crate::ast::*;
use crate::ast_util::{mk_eq, mk_ineq};
use crate::messages::Span;
use crate::resource::memory::{growth::Growth, metadata::expr, transfer};
use std::collections::HashMap;

/// Exact membership and its associated source observations. When the owner
/// crosses into a worker, the publishing trace specializes only the candidates.
/// The receiving loop must prove them against its real state at every boundary.
#[derive(Clone)]
pub(in super::super) struct PopulationPrefix {
    span: Span,
    body: Span,
    /// Actual records and the inferred records after the observed visit count.
    forest: (Expr, Expr),
    /// Actual and expected logical length in the receiving actor.
    length: Option<(Expr, Expr)>,
    /// Actual backing charge and its inferred upper bound.
    backing: Option<(Expr, Expr)>,
}

impl PopulationPrefix {
    pub(in super::super) fn new(
        record: &super::Loop,
        role: &super::LocalPath,
        forest: (Expr, Expr),
        length: Option<Expr>,
        backing: Option<Expr>,
    ) -> Self {
        let charge = record.charges.iter().find(|charge| &charge.location == role);
        Self {
            span: record.span.clone(),
            body: record.body.span.clone(),
            forest,
            length: length.and_then(|expected| Some((charge?.length.0.clone(), expected))),
            backing: backing.and_then(|upper| Some((charge?.backing.as_ref()?.0.clone(), upper))),
        }
    }

    pub(in super::super) fn emit(
        &self,
        growth: &mut Growth,
        captures: &HashMap<VarIdent, Expr>,
    ) -> Result<(), VirErr> {
        let span = &self.span;
        let specialize = |value: &Expr| {
            if captures.is_empty() {
                value.clone()
            } else {
                transfer::simplify::specialize(value, captures)
            }
        };
        let expected = specialize(&self.forest.1);
        let mut proofs = Vec::new();
        transfer::prove_loop_prefix(span, &expected, &mut proofs)?;
        let proof = crate::def::Spanned::new(
            span.clone(),
            StmtX::Expr(crate::ast_util::mk_block(span, proofs, None)),
        );
        growth.before_loop_proof(span, proof.clone());
        growth.before.entry(self.body.id).or_default().push(proof.clone());
        growth.after.entry(self.body.id).or_default().push(proof.clone());
        // Loop-body facts do not escape an isolated query. Instantiate the
        // same transport laws at exit before any subsequent join or drop.
        let mut exit_proofs = Vec::new();
        transfer::prove_prefix_exit(span, &expected, &mut exit_proofs)?;
        growth.after.entry(span.id).or_default().extend(exit_proofs);
        if let Some(last) = transfer::retained_last(span, &expected) {
            growth.after.entry(span.id).or_default().push(last);
        }
        let mut invariants = Vec::new();
        invariants.push(expr::purpose(
            mk_eq(span, &self.forest.0, &expected),
            "memory worker collection membership",
        ));
        if let Some((actual, length)) = &self.length {
            invariants.push(expr::purpose(
                mk_eq(span, actual, &specialize(length)),
                "captured worker collection length",
            ));
        }
        if let Some((actual, upper)) = &self.backing {
            invariants.push(expr::purpose(
                mk_ineq(span, actual, &specialize(upper), InequalityOp::Le),
                "memory collection backing-storage bound",
            ));
        }
        growth.loops.entry(span.id).or_default().extend(invariants);
        Ok(())
    }
}

impl crate::resource::memory::analysis::Analysis<'_> {
    /// A payload can outlive all named vector bindings. Carry an unchanged
    /// buffer's constructor size through isolated loop proofs while its charge
    /// is present, including when only outstanding workers retain the root.
    pub(super) fn shared_payload_invariants(&self, span: &Span) -> Vec<Expr> {
        let mut vectors = std::collections::BTreeSet::new();
        for backing in
            self.heap.shared.owned().chain(self.growth.indexed_shared.values().map(|c| &c.backing))
        {
            backing.visit(&mut |node| vectors.extend(node.vector));
        }
        vectors
            .into_iter()
            .filter_map(|id| {
                let backing = &self.growth.vectors[id].backing;
                if backing.changed || !self.storage.contains_allocation(backing.id) {
                    return None;
                }
                crate::ast_visitor::expr_visitor_check(&backing.initial_bytes, &mut |_, value| {
                    if let ExprX::Var(name) = &value.x
                        && !(self.stable_scalars.contains(name) && self.slots.contains_key(name))
                    {
                        return Err(());
                    }
                    Ok(())
                })
                .ok()?;
                Some(mk_eq(span, &backing.bytes, &backing.initial_bytes))
            })
            .collect()
    }

    /// Keep claims outside the loop's handle vectors as the entry offset.
    /// Verus checks this equality on the actual entry and back edges; lengths
    /// cannot stand in for membership when the possible worker weights differ.
    pub(super) fn loop_shared_claims(&mut self, record: &super::Loop) -> Vec<Expr> {
        use crate::resource::memory::contracts;
        if self.current_worker.is_some() {
            return Vec::new();
        }
        let span = &record.span;
        let mut offsets = Vec::new();
        let mut facts = Vec::new();
        let mut live_forests = std::collections::BTreeSet::new();
        let mut selected_handle = false;
        for owner in self.heap.owners.values().chain(self.heap.borrowed.values()) {
            owner.visit(&mut |node| {
                selected_handle |= node.selected_worker.is_some();
                if let Some(elements) = &node.elements
                    && let ExprX::Var(name) = &elements.records.x
                {
                    live_forests.insert(name.clone());
                }
            });
        }
        let mut needs_family_counts = false;
        for (root, claims, peers) in self
            .growth
            .indexed_shared
            .iter()
            .map(|(id, claims)| (id, &claims.population, None))
            .chain(
                self.growth
                    .occurrence_peers
                    .iter()
                    .map(|(id, peers)| (id, &peers.population, Some(&peers.destinations))),
            )
        {
            let mut current = expr::integer(span, 0);
            let mut related = false;
            let mut covered = std::collections::BTreeSet::new();
            for charge in &record.charges {
                let Some((typ, forest)) = record.reference_forests.get(&charge.location) else {
                    continue;
                };
                if let Some(destinations) = peers {
                    let ExprX::Var(name) = &forest.x else { continue };
                    if !destinations.contains(name) {
                        continue;
                    }
                    covered.insert(name.clone());
                }
                let TypX::Datatype(_, types, _) = &**typ else { continue };
                if !self.layouts.vector(typ) {
                    continue;
                }
                if types
                    .first()
                    .is_some_and(|typ| matches!(&**typ, TypX::Decorate(TypDecoration::Arc, _, _)))
                {
                    if peers.is_some() {
                        continue;
                    }
                    let key = expr::integer(span, root.serial());
                    let count = expr::operation(
                        span,
                        "shared_count",
                        vec![forest.clone(), key.clone()],
                        crate::ast_util::int_typ(),
                    );
                    // With one candidate root, every occupied result slot must
                    // retain exactly one reference to it. Prove that relationship
                    // on entry and after each push/pop before using the length.
                    let (name, path) = &charge.location;
                    let contribution = if self.growth.indexed_shared.len() == 1
                        && self
                            .heap
                            .root(name)
                            .and_then(|owner| owner.at(path))
                            .and_then(|node| node.elements.as_ref())
                            .is_some_and(|e| {
                                e.references == super::super::elements::References::IndexedAliases
                            }) {
                        facts.push(expr::purpose(
                            mk_eq(span, &count, &charge.length.0),
                            "references in the homogeneous Arc result collection",
                        ));
                        charge.length.0.clone()
                    } else {
                        count
                    };
                    current = contracts::add(span, current, contribution);
                    self.growth.before.entry(span.id).or_default().push(expr::lemma(
                        span,
                        "shared_count_empty",
                        vec![key],
                    ));
                    related = true;
                    continue;
                }
                let Some((payload, _)) =
                    types.first().and_then(|element| self.layouts.join_handle(element))
                else {
                    continue;
                };
                let families = self.retained_families(payload);
                if let Some((count, mixed)) =
                    claims.collection_count(span, families, forest, &charge.length.0)
                {
                    current = contracts::add(span, current, count);
                    related = true;
                    needs_family_counts |= mixed;
                }
            }
            // When all live destinations are in this loop, try the absolute
            // count. A worker or returned alias held outside the forests needs
            // the entry offset instead. Both candidates are checked by Verus.
            let closed = peers.is_some_and(|destinations| {
                destinations.intersection(&live_forests).all(|name| covered.contains(name))
            }) && !selected_handle
                && !self
                    .growth
                    .peer_results
                    .iter()
                    .any(|(id, role)| role.site == *root && self.heap.shared.has_strong(*id));
            if closed {
                facts.push(expr::purpose(
                    mk_eq(span, &claims.pending, &current),
                    "allocation peers in the live handle collections",
                ));
            }
            if related {
                offsets.push((claims.pending.clone(), current));
            }
        }
        if needs_family_counts {
            for law in
                ["worker_family_count_empty", "worker_family_count_push", "worker_family_count_pop"]
            {
                let activation = crate::def::Spanned::new(
                    span.clone(),
                    StmtX::Expr(SpannedTyped::new(
                        span,
                        &crate::ast_util::unit_typ(),
                        ExprX::Fuel(expr::function(law), 1, true),
                    )),
                );
                self.growth.before_loop_proof(span, activation.clone());
                self.growth.before.entry(record.body.span.id).or_default().push(activation);
            }
        }
        for (pending, current) in offsets {
            let entry = self.loop_snapshot(span, &current);
            let initial = self.loop_snapshot(span, &pending);
            // A slot count is an opaque integer. A clone stored during this
            // iteration can create and release a reservation before the next
            // back edge. Give both operations the checked lower bound.
            facts.push(expr::purpose(
                mk_ineq(span, &expr::integer(span, 0), &pending, InequalityOp::Le),
                "outstanding shared references are nonnegative",
            ));
            facts.push(expr::purpose(
                mk_ineq(span, &current, &pending, InequalityOp::Le),
                "worker collections cannot contain more claims than were published",
            ));
            facts.push(expr::purpose(
                mk_eq(
                    span,
                    &contracts::add(span, pending, entry),
                    &contracts::add(span, initial, current),
                ),
                "outstanding shared references in the loop's worker collections",
            ));
        }
        facts
    }
}
