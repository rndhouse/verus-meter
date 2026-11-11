//! Inductive memory proofs consume the shared loop record and checked transfers.

use super::{Charge, Loop, Transfer};
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, contracts};

impl Analysis<'_> {
    pub(in super::super) fn analyze_loop(&mut self, expr: &Expr) -> Result<(), VirErr> {
        let mut record = Loop::new(expr, self.layouts, self.summaries)?;
        let nested = self.growth.loop_depth > 0;
        self.prepare_element_loop(&record)?;
        let mut forest_bounds = self.element_loop_bounds(&record);
        forest_bounds.extend(self.loop_charge_candidates(&mut record));
        let loop_scalars = self.stable_scalars.clone();
        let entry = self.storage.live();
        let ids = self.heap.vectors();
        let metadata_facts = self.element_metadata_invariants(&expr.span);
        let precise_forests = !metadata_facts.is_empty();
        if precise_forests {
            self.enable_loop_metadata(&expr.span);
        }
        let vector_entry: Vec<_> = ids
            .iter()
            .filter(|_| precise_forests)
            .map(|id| {
                (
                    *id,
                    self.growth.vectors[*id].pushes,
                    self.growth.vectors[*id].backing.floor.clone(),
                )
            })
            .collect();
        let elements = self.heap.element_states();
        let mut entry_facts = Vec::new();
        if precise_forests {
            if !nested {
                entry_facts.extend(self.growth.invariants(
                    &expr.span,
                    &ids,
                    &loop_scalars,
                    &self.bound,
                ));
                entry_facts.extend(self.growth.element_invariants(
                    &expr.span,
                    &elements,
                    &loop_scalars,
                    &self.bound,
                ));
            }
            entry_facts.extend(metadata_facts);
            entry_facts.extend(self.element_reservation_invariants(&expr.span, &loop_scalars)?);
        }

        entry_facts.extend(
            record
                .invariants
                .iter()
                .filter(|inv| {
                    precise_forests
                        && matches!(
                            inv.kind,
                            LoopInvariantKind::InvariantAndEnsures
                                | LoopInvariantKind::InvariantExceptBreak
                        )
                })
                .map(|inv| inv.inv.clone()),
        );
        let entry_facts = self.freeze_loop_facts(&expr.span, entry_facts)?;
        let live = self.storage.live_expression(&expr.span).total();
        let loop_inputs = self.loop_inputs();
        let protection = self.heap.protect();
        self.heap.permit_loop_partitions(&protection.0, &protection.1);
        let first_checkpoint = self.checkpoints.len();
        self.storage.event(&expr.span, "analyze reusable while iteration".into());
        self.growth.loop_depth += 1;
        // Nested loops enter after any number of outer iterations. Their entry
        // candidates cannot reuse the first iteration's finite charge extent.
        self.growth.begin_element_iteration(&elements);
        self.discard(&record.condition)?;
        self.discard(&record.body)?;
        self.growth.loop_depth -= 1;
        assert_eq!(self.storage.live(), entry);
        // Every checkpoint may be reached after a previous complete
        // iteration. With reusable storage, one iteration's maximum is
        // the fixed point, including any nested loops or alternatives.
        let iteration_peak = self.storage.peak();
        for checkpoint in &mut self.checkpoints[first_checkpoint..] {
            checkpoint.peak.merge(&iteration_peak);
        }
        self.heap.unprotect(protection);
        record.regions = self.finish_loop_inputs(&expr.span, loop_inputs)?;
        let mut frame_invariants = Vec::new();
        for (id, pushes, floor) in vector_entry {
            let state = self.growth.vectors[id].clone();
            if state.pushes == pushes && std::sync::Arc::ptr_eq(&floor, &state.backing.floor) {
                // Observing an occupied length can improve our capacity lower
                // bound without changing physical backing or allocating bytes.
                let snapshot = self.loop_snapshot(&expr.span, &state.capacity);
                frame_invariants.push(crate::ast_util::mk_ineq(
                    &expr.span,
                    &snapshot,
                    &state.capacity,
                    InequalityOp::Le,
                ));
                let snapshot = self.loop_snapshot(&expr.span, &state.backing.bytes);
                frame_invariants.push(crate::ast_util::mk_eq(
                    &expr.span,
                    &state.backing.bytes,
                    &snapshot,
                ));
            }
        }
        let mut invariants = self.growth.invariants(&expr.span, &ids, &loop_scalars, &self.bound);
        invariants.extend(self.element_metadata_invariants(&expr.span));
        invariants.extend(self.element_reservation_invariants(&expr.span, &loop_scalars)?);
        invariants.extend(forest_bounds);
        invariants.extend(frame_invariants);
        invariants.extend(entry_facts);
        if nested {
            invariants.extend(self.growth.element_nonnegative(&expr.span, &elements));
        } else {
            invariants.extend(self.growth.element_invariants(
                &expr.span,
                &elements,
                &loop_scalars,
                &self.bound,
            ));
        }
        invariants.push(crate::ast_util::mk_ineq(&expr.span, &live, &self.bound, InequalityOp::Le));
        self.growth.loops.insert(expr.span.id, invariants);
        self.growth.repeat_elements(&elements);
        record.element_sources = self.growth.element_sources(&elements);
        record.element_ids = elements.clone();
        record.proof_scalars = loop_scalars;
        let mut children = Vec::new();
        crate::ast_visitor::expr_visitor_check(&record.body, &mut |_, value| {
            if matches!(value.x, ExprX::Loop { .. })
                && self.transitions.loops.contains_key(&value.span.id)
            {
                children.push(value.span.id);
            }
            Ok::<(), VirErr>(())
        })?;
        for id in children {
            let child = &self.transitions.loops[&id];
            let facts = self.growth.element_invariants_at(
                &child.span,
                &child.element_ids,
                &child.proof_scalars,
                &self.bound,
                Some(&child.element_sources),
            );
            self.transitions.loops.get_mut(&id).unwrap().element_facts = facts;
        }
        self.transitions.loops.insert(expr.span.id, record);
        Ok(())
    }

    /// Completed summary evidence becomes ordinary inductive proof candidates.
    /// Failed or partial inference cannot modify the body proof state.
    pub(in super::super) fn apply_loop_evidence(
        &mut self,
        loops: &std::collections::HashMap<u64, Vec<Transfer>>,
        growth: &std::collections::HashMap<u64, Vec<(super::super::paths::LocalPath, Expr)>>,
    ) -> Result<(), VirErr> {
        for (id, transfers) in loops {
            let record = &self.transitions.loops[id];
            self.growth.loops.entry(*id).or_default().extend(record.conservation(transfers));
        }
        for (id, bounds) in growth {
            let record = &self.transitions.loops[id];
            for (location, amount) in bounds {
                if let Some(charge) =
                    record.charges.iter().find(|charge| &charge.location == location)
                {
                    // Isolated loop queries do not retain the executable
                    // length's type bound for an erased integer snapshot.
                    self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                        &record.span,
                        &contracts::literal(&record.span, 0),
                        &charge.length.1,
                        InequalityOp::Le,
                    ));
                    // A positive prefix of a block costs at most the whole
                    // block. This pointwise envelope remains valid before an
                    // inner loop; exported forests retain the exact tiled cost.
                    let added = contracts::multiply(
                        &record.span,
                        amount.clone(),
                        contracts::subtract(
                            &record.span,
                            charge.length.0.clone(),
                            charge.length.1.clone(),
                        ),
                    );
                    let upper = contracts::add(&record.span, charge.entry.clone(), added);
                    self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                        &record.span,
                        &charge.current,
                        &upper,
                        InequalityOp::Le,
                    ));
                    if let (Some((bytes, entry)), Some((current_capacity, capacity, element))) =
                        (&charge.backing, &charge.reservation)
                    {
                        // An entry reservation stays available as backing grows.
                        // Without this frame fact, a loop query can pair an
                        // arbitrary entry capacity with a smaller current one.
                        self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                            &record.span,
                            capacity,
                            current_capacity,
                            InequalityOp::Le,
                        ));
                        let replacement = contracts::multiply(
                            &record.span,
                            contracts::literal(&record.span, *element),
                            crate::resource::memory::growth::grown_capacity(
                                &record.span,
                                charge.length.0.clone(),
                                *element,
                            ),
                        );
                        let upper = crate::resource::memory::growth::select(
                            &record.span,
                            crate::ast_util::mk_ineq(
                                &record.span,
                                &charge.length.0,
                                capacity,
                                InequalityOp::Le,
                            ),
                            entry.clone(),
                            contracts::maximum(&record.span, entry.clone(), replacement),
                        );
                        self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                            &record.span,
                            bytes,
                            &upper,
                            InequalityOp::Le,
                        ));
                    }
                }
            }
        }
        for (id, record) in &self.transitions.loops {
            self.growth.loops.entry(*id).or_default().extend(record.element_facts.iter().cloned());
        }
        self.inherit_loop_entries()
    }

    /// A nested query needs facts about its actual entry, not observations from
    /// the first syntactic visit to its parent's body. Freeze the parent's
    /// completed inductive facts at that entry after both summaries are known.
    /// These remain ordinary invariants checked before the nested loop.
    fn inherit_loop_entries(&mut self) -> Result<(), VirErr> {
        let records = self.transitions.loops.clone();
        let mut descendants = std::collections::HashMap::new();
        for (id, record) in &records {
            let mut children = std::collections::HashSet::new();
            crate::ast_visitor::expr_visitor_check(&record.body, &mut |_, value| {
                if matches!(value.x, ExprX::Loop { .. }) && records.contains_key(&value.span.id) {
                    children.insert(value.span.id);
                }
                Ok::<(), VirErr>(())
            })?;
            descendants.insert(*id, children);
        }
        let mut parents = Vec::new();
        for child in records.keys() {
            if let Some((parent, children)) = descendants
                .iter()
                .filter(|(_, children)| children.contains(child))
                .min_by_key(|(_, children)| children.len())
            {
                parents.push((children.len(), *parent, *child));
            }
        }
        parents.sort_by_key(|(size, _, _)| std::cmp::Reverse(*size));
        for (_, parent, child) in parents {
            let record = &records[&child];
            let mut immutable = self
                .growth
                .loop_entry
                .get(&parent)
                .map(|entries| entries.values().cloned().collect::<Vec<_>>())
                .unwrap_or_default();
            for charge in &records[&parent].charges {
                immutable.push(charge.entry.clone());
                immutable.push(charge.length.1.clone());
                if let Some((_, entry)) = &charge.backing {
                    immutable.push(entry.clone());
                }
            }
            for charge in &record.charges {
                immutable.push(charge.length.1.clone());
            }
            let mut preserved = std::collections::HashMap::new();
            for value in immutable {
                crate::ast_visitor::expr_visitor_check(&value, &mut |_, value| {
                    if let ExprX::Var(name) = &value.x {
                        preserved.insert(name.clone(), value.clone());
                    }
                    Ok::<(), VirErr>(())
                })?;
            }
            for (name, value) in preserved {
                if let Some(previous) =
                    self.growth.loop_entry.entry(child).or_default().insert(name, value.clone())
                {
                    self.growth.loops.entry(child).or_default().push(crate::ast_util::mk_eq(
                        &record.span,
                        &previous,
                        &value,
                    ));
                }
            }
            let facts = self.growth.loops[&parent].clone();
            let facts = self.freeze_loop_facts(&record.span, facts)?;
            self.growth.loops.entry(child).or_default().extend(facts);
            for charge in &record.charges {
                let fact = crate::ast_util::mk_eq(&record.span, &charge.length.0, &charge.length.1);
                let fact = self.freeze_loop_facts(&record.span, vec![fact])?;
                self.growth.loops.entry(child).or_default().extend(fact);
            }
        }
        Ok(())
    }

    /// Snapshot potential conservation groups before the body changes counters.
    /// The checked iteration graph chooses groups later; every candidate remains
    /// an ordinary invariant proved at loop entry and on all back edges.
    fn loop_charge_candidates(&mut self, record: &mut Loop) -> Vec<Expr> {
        let span = &record.span;
        let mut roles = Vec::new();
        for (name, owner) in self.heap.owners.iter().chain(self.heap.borrowed.iter()) {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                if let Some(elements) = &node.elements {
                    if elements.precise {
                        roles.push((
                            (name.clone(), path.clone()),
                            elements.states.values().copied().collect::<Vec<_>>(),
                            node.vector,
                            self.owner_length(span, node),
                        ));
                    }
                }
            });
        }
        let mut candidates = Vec::new();
        let mut charges = Vec::new();
        for (location, states, vector, length) in roles {
            let mut current = contracts::literal(span, 0);
            let mut entry = current.clone();
            for id in states {
                let bytes = self.growth.elements[id].bytes.clone();
                let snapshot = self.loop_snapshot(span, &bytes);
                if let Some(upper) = self.growth.elements[id].entry_upper() {
                    let mut stable = true;
                    let _ = crate::ast_visitor::expr_visitor_check(&upper, &mut |_, expr| {
                        if let crate::ast::ExprX::Var(name) = &expr.x {
                            stable &= self.stable_scalars.contains(name);
                        }
                        Ok::<(), VirErr>(())
                    });
                    if stable {
                        candidates.push(crate::ast_util::mk_ineq(
                            span,
                            &snapshot,
                            &upper,
                            crate::ast::InequalityOp::Le,
                        ));
                    }
                }
                current = contracts::add(span, current, bytes);
                entry = contracts::add(span, entry, snapshot);
            }
            let backing = vector.map(|id| {
                let bytes = self.growth.vectors[id].backing.bytes.clone();
                let snapshot = self.loop_snapshot(span, &bytes);
                (bytes, snapshot)
            });
            let length = SpannedTyped::new(span, &crate::ast_util::int_typ(), length.x.clone());
            let snapshot = self.loop_snapshot(span, &length);
            let reservation = vector.map(|id| {
                let state = self.growth.vectors[id].clone();
                (state.capacity.clone(), self.loop_snapshot(span, &state.capacity), state.element)
            });
            charges.push(Charge {
                location,
                current,
                entry,
                backing,
                length: (length, snapshot),
                reservation,
            });
        }
        record.charges = charges;
        candidates
    }
}

impl Loop {
    /// These are proof candidates, not assumptions or inferred byte allowances.
    fn conservation(&self, transfers: &[Transfer]) -> Vec<Expr> {
        transfers
            .iter()
            .flat_map(|transfer| {
                let a = &self.charges[transfer.source];
                let b = &self.charges[transfer.target];
                let mut candidates = vec![crate::ast_util::mk_ineq(
                    &self.span,
                    &contracts::add(&self.span, a.current.clone(), b.current.clone()),
                    &contracts::add(&self.span, a.entry.clone(), b.entry.clone()),
                    InequalityOp::Le,
                )];
                if transfer.source == transfer.target {
                    if let Some((bytes, entry)) = &a.backing {
                        candidates.push(crate::ast_util::mk_ineq(
                            &self.span,
                            bytes,
                            entry,
                            InequalityOp::Le,
                        ));
                    }
                }
                candidates
            })
            .collect()
    }
}
