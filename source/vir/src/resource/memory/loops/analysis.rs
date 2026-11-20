//! Inductive memory proofs consume the shared loop record and checked transfers.
//!
//! This module orchestrates entry snapshots, one reusable body visit, inductive
//! candidates, and exits. Charge construction, summary evidence, progress facts,
//! and nested entry propagation live in focused child modules.

mod charges;
mod evidence;
mod headroom;
mod nested;
mod visits;

use super::Loop;
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, contracts, metadata};

impl Analysis<'_> {
    /// Analyze one reusable visit, then attach its memory invariants and exit states.
    pub(in super::super) fn analyze_loop(&mut self, expr: &Expr) -> Result<(), VirErr> {
        let mut record = Loop::new(expr, self.layouts, self.summaries)?;
        let nested = self.growth.loop_depth > 0;
        record.nested = nested;
        self.prepare_element_loop(&record)?;
        let publication_sites = self.prepare_publication_ledgers(&record.span, &record.body);
        let fresh_ledgers = self.prepare_deferred_loop(&expr.span);
        for (name, owner) in &self.heap.owners {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                if let (Some(elements), Some((typ, _))) = (&node.elements, &node.source) {
                    // A helper input has only caller-charged children in this
                    // frame. Its exact membership is instantiated at the call;
                    // the helper checks the linear use of each removal.
                    let caller_owned = self
                        .transitions
                        .worker_parameter
                        .is_some_and(|(_, vector)| node.vector == Some(vector));
                    if !caller_owned && elements.precise && self.layouts.contains_references(typ) {
                        record.reference_forests.insert(
                            (name.clone(), path.clone()),
                            (typ.clone(), elements.records.clone()),
                        );
                    }
                }
            });
        }
        let mut forest_bounds = self.element_loop_bounds(&record);
        forest_bounds.extend(self.loop_charge_candidates(&mut record));
        let loop_scalars = self.stable_scalars.clone();
        record.proof_slices = self
            .growth
            .immutable_slices
            .iter()
            .filter(|name| self.slots.contains_key(*name))
            .cloned()
            .collect();
        let entry = self.storage.live();
        let ids = self.heap.vectors();
        let shared_payloads = self.shared_payload_invariants(&expr.span);
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
                    self.growth.vectors[*id].removals,
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
        let first_cost = self.storage.peak().costs.len();
        let entry_heap = self.storage.live_expression(&expr.span).select(
            &expr.span,
            &super::super::footprint::MemorySelection::kind(
                super::super::footprint::MemoryKind::host_heap(),
            ),
        );
        self.storage.event(&expr.span, "analyze reusable while iteration".into());
        self.growth.loop_depth += 1;
        self.growth.loop_regions.push(expr.span.id);
        let mut counters: std::collections::HashSet<_> = record
            .scalar_steps
            .keys()
            .filter(|name| self.slots.contains_key(*name))
            .cloned()
            .collect();
        if let Some(counter) = record.control.as_ref().and_then(|control| control.counter()) {
            counters.insert(counter.clone());
        }
        let inserted: Vec<_> = counters
            .into_iter()
            .filter(|name| self.growth.loop_counters.insert(name.clone()))
            .collect();
        // Nested loops enter after any number of outer iterations. Their entry
        // candidates cannot reuse the first iteration's finite charge extent.
        let zero = self.loop_zero_candidates(&record, &mut forest_bounds);
        self.growth.begin_element_iteration(&elements, &zero);
        let ordinal = self.loop_occurrence(&record);
        self.discard(&record.condition)?;
        record.completed = self.loop_progress(&mut record)?;
        let head = self.branch_state();
        let first_exit = self.flow.exits.len();
        if let Some(iterator) = &record.iterator {
            let (site, head) = iterator.observe_advance();
            self.growth.iterator_heads.insert(site, head);
            if let Some(name) = iterator.item_slot() {
                self.growth.iterator_item_slots.insert(name.clone());
            }
            self.growth
                .implicit_collection_loop_slots
                .extend(iterator.implicit_item_slots().cloned());
        }
        self.discard(&record.body)?;
        if let Some(iterator) = &record.iterator {
            self.growth.iterator_heads.remove(&iterator.observe_advance().0);
            if let Some(name) = iterator.item_slot() {
                self.growth.iterator_item_slots.remove(name);
            }
        }
        self.finish_publication_ledgers(&record.span, publication_sites);
        let mut breaks = Vec::new();
        let mut continues = Vec::new();
        for edge in self.flow.exits.split_off(first_exit) {
            use super::super::control::Target;
            match &edge.target {
                Target::Break(label) if label == &record.label => breaks.push(edge),
                Target::Continue(label) if label == &record.label => continues.push(edge),
                _ => self.flow.exits.push(edge),
            }
        }
        // Head breaks observe an unchanged loop-head state, so its checked
        // invariants also hold on those exits. A partial visit or an outer exit
        // must not export completed-visit relationships as exit facts.
        if breaks.iter().any(|edge| !record.head_breaks.contains(&edge.span.id))
            || self.flow.exits.len() > first_exit
        {
            self.growth.exiting_loops.insert(expr.span.id);
        }
        for edge in &continues {
            if self.flow.reachable {
                self.join_exit(&edge.span, &edge.state)?;
            } else {
                self.restore_branch(&edge.state);
            }
            self.growth.before.entry(edge.span.id).or_default().push(
                super::super::metadata::expr::assign(
                    &edge.span,
                    &ordinal,
                    contracts::add(&edge.span, ordinal.clone(), contracts::literal(&edge.span, 1)),
                ),
            );
        }
        record.single_visit = !self.flow.reachable;
        if record.single_visit {
            self.growth.single_visit_loops.insert(expr.span.id);
            self.restore_branch(&head);
        }
        if !nested {
            self.finish_element_reservations()?;
        }
        self.growth.loop_depth -= 1;
        self.growth.loop_regions.pop();
        for counter in inserted {
            self.growth.loop_counters.remove(&counter);
        }
        if record.single_visit {
            self.heap.unprotect(protection.clone());
            self.finish_loop_exits(expr, &record, &head, breaks, protection)?;
            self.transitions.loops.insert(expr.span.id, record);
            return Ok(());
        }
        self.growth.carried_scalars.extend(
            record.scalar_steps.keys().filter(|name| self.slots.contains_key(*name)).cloned(),
        );
        if !self.heap.shared.compatible_selections(&head.heap.shared) {
            return Err(super::super::model::unsupported(
                &expr.span,
                "selected Arc handles carried across a back edge without a checked identity relation",
            ));
        }
        if !self.heap.workers.compatible(&head.heap.workers) {
            return Err(super::super::model::unsupported(
                &expr.span,
                "retained worker populations without a checked back-edge ownership relation",
            ));
        }
        assert_eq!(self.storage.live(), entry);
        // Every checkpoint may be reached after a previous complete
        // iteration. With reusable storage, one iteration's maximum is
        // the fixed point, including any nested loops or alternatives.
        let iteration_peak = self.storage.peak();
        for edge in breaks.iter_mut().chain(self.flow.exits[first_exit..].iter_mut()) {
            let mut peak = edge.state.storage.peak();
            peak.merge(&iteration_peak);
            edge.state.storage.set_peak(peak);
        }
        if breaks.iter().any(|edge| edge.owner.is_some() || edge.value.bytes != 0) {
            return Err(super::super::model::unsupported(
                &expr.span,
                "value-producing breaks in reusable loops without a checked result transformation",
            ));
        }
        if !super::super::control::compatible_heap(&self.heap, &head.heap)
            && (breaks.iter().any(|edge| !record.head_breaks.contains(&edge.span.id))
                || self.flow.exits.len() > first_exit)
        {
            return Err(super::super::model::unsupported(
                &expr.span,
                "partial loop exits after changing fixed ownership roles or original input regions",
            ));
        }
        let costs = &iteration_peak.costs[first_cost..];
        record.local_costs = costs.to_vec();
        if let Some(iterator) = &record.iterator
            && head.heap.owners.contains_key(&iterator.receiver)
            && let Some(last) = costs.iter().rposition(|(site, _)| iterator.dispatch_site(site.id))
        {
            // Exhaustion still invokes next with the backing allocation live.
            // No item staging or work from the successful path is reachable.
            let span = &record.span;
            let local = super::super::footprint::MemorySelection::kind(
                super::super::footprint::MemoryKind::host_local(),
            );
            if let Some(bytes) = costs[..=last]
                .iter()
                .filter_map(|(_, cost)| contracts::constant(&cost.select(span, &local)))
                .max()
            {
                let cost =
                    contracts::add(span, entry_heap.clone(), contracts::literal(span, bytes));
                let bound = crate::ast_util::mk_ineq(span, &cost, &self.bound, InequalityOp::Le);
                let empty =
                    crate::ast_util::mk_eq(span, &iterator.length, &contracts::literal(span, 0));
                self.growth.loops.entry(span.id).or_default().push(metadata::expr::purpose(
                    crate::ast_util::mk_implies(span, &empty, &bound),
                    "memory budget exceeded when checking an empty consuming iterator",
                ));
            }
        }
        // An inline-element iterator keeps one immutable allocation charge.
        // Carry the visit's fixed headroom into an isolated loop proof.
        if let Some(iterator) = &record.iterator
            && let Some(owner) = head.heap.owners.get(&iterator.receiver)
            && owner.source.is_none()
            && owner.elements.is_none()
            && let Some(extent) = &owner.extent
            && let ExprX::Var(backing) = &extent.x
        {
            let span = &record.span;
            // A consuming iterator keeps its entire backing, even after yielding
            // an element. Carry its original length-to-bytes bound through the
            // isolated proof alongside any other vectors growing in this loop.
            if let Some(allocation) = owner.dynamic
                && let Some(state) = self.growth.vectors.iter().find(|v| v.backing.id == allocation)
                && state.append_only
                && state.pushes > 0
                && [&state.minimum, &state.backing.initial_bytes, &state.backing.floor]
                    .into_iter()
                    .all(|term| contracts::constant(term).is_some())
            {
                let upper =
                    state.appended_bytes(span, &iterator.length, state.backing.floor.clone());
                self.growth.loops.entry(span.id).or_default().push(crate::ast_util::mk_ineq(
                    span,
                    extent,
                    &upper,
                    InequalityOp::Le,
                ));
            }
            let facts =
                record.iterator_headroom(iterator, &loop_scalars, extent, &self.bound, |point| {
                    match &point.total().x {
                        ExprX::Var(name) if name == backing => Some(0),
                        ExprX::Binary(BinaryOp::Arith(ArithOp::Add(_)), left, right) => {
                            match (&left.x, &right.x) {
                                (ExprX::Var(name), _) if name == backing => {
                                    contracts::constant(right)
                                }
                                (_, ExprX::Var(name)) if name == backing => {
                                    contracts::constant(left)
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                });
            self.growth.loops.entry(span.id).or_default().extend(facts.into_iter().map(|fact| {
                metadata::expr::purpose(
                    fact,
                    "memory budget exceeded for the consuming iterator and its loop body",
                )
            }));
        }
        if let Some(iterator) = &record.iterator
            && let Some(item) = iterator.consumed_item_type()
            && self.layouts.owner(item)
        {
            // A successful advance transfers existing payloads. The source
            // binding adds only its inline slot to the loop-head footprint.
            let span = &record.span;
            let bytes = contracts::literal(span, self.layouts.size(item, span)?);
            let cost = contracts::add(span, live.clone(), bytes);
            let fits = crate::ast_util::mk_ineq(span, &cost, &self.bound, InequalityOp::Le);
            let has_item = crate::ast_util::mk_ineq(
                span,
                &iterator.position,
                &iterator.length,
                InequalityOp::Lt,
            );
            self.growth.loops.entry(span.id).or_default().push(metadata::expr::purpose(
                crate::ast_util::mk_implies(span, &has_item, &fits),
                "memory budget exceeded for the consuming loop item binding",
            ));
        }
        let candidate =
            crate::ast_util::mk_ineq(&expr.span, &entry_heap, &self.bound, InequalityOp::Le);
        record.entry_headroom = vec![candidate];
        for checkpoint in &mut self.checkpoints[first_checkpoint..] {
            checkpoint.peak.merge(&iteration_peak);
        }
        self.heap.unprotect(protection.clone());
        record.regions = self.finish_loop_inputs(&expr.span, loop_inputs)?;
        let mut frame_invariants = Vec::new();
        for (id, pushes, removals, floor) in vector_entry {
            let state = self.growth.vectors[id].clone();
            if state.pushes == pushes && std::sync::Arc::ptr_eq(&floor, &state.backing.floor) {
                let snapshot = self.loop_snapshot(&expr.span, &state.capacity);
                frame_invariants.push(crate::ast_util::mk_eq(
                    &expr.span,
                    &snapshot,
                    &state.capacity,
                ));
                let snapshot = self.loop_snapshot(&expr.span, &state.backing.bytes);
                let frame = if state.removals == removals {
                    crate::ast_util::mk_eq(&expr.span, &state.backing.bytes, &snapshot)
                } else {
                    crate::ast_util::mk_ineq(
                        &expr.span,
                        &state.backing.bytes,
                        &snapshot,
                        InequalityOp::Le,
                    )
                };
                frame_invariants.push(frame);
            }
        }
        let mut invariants = self.growth.invariants(&expr.span, &ids, &loop_scalars, &self.bound);
        invariants.extend(shared_payloads);
        invariants.extend(
            self.element_metadata_invariants(&expr.span)
                .into_iter()
                .map(|fact| metadata::expr::purpose(fact, "memory allocation descriptor validity")),
        );
        invariants.extend(self.element_reservation_invariants(&expr.span, &loop_scalars)?);
        if self.growth.exiting_loops.contains(&expr.span.id) {
            // These describe current allocations, not completed visits. Prove
            // them separately on every normal exit and break so later code can
            // still account for storage retained by a partial final visit.
            // Progress, conservation, and frozen head facts remain head-only.
            let mut exits = invariants.clone();
            exits.extend(frame_invariants.iter().cloned());
            exits.extend(self.growth.element_invariants(
                &expr.span,
                &elements,
                &loop_scalars,
                &self.bound,
            ));
            self.growth.loop_ensures.entry(expr.span.id).or_default().extend(exits);
        }
        invariants.extend(self.loop_shared_claims(&record));
        invariants.extend(self.deferred_drain_bounds(&record, &fresh_ledgers, &entry_heap));
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
        invariants.push(metadata::expr::purpose(
            crate::ast_util::mk_ineq(&expr.span, &live, &self.bound, InequalityOp::Le),
            "memory byte bound at loop head",
        ));
        self.growth.loops.entry(expr.span.id).or_default().extend(invariants);
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
        // A head guard can fire after any number of complete visits. Reuse the
        // completed head's role identities, including its loop-exit input
        // regions, rather than the representative first visit's old regions.
        let completed_head = self.branch_state();
        for edge in &mut breaks {
            if record.head_breaks.contains(&edge.span.id) {
                let peak = edge.state.storage.peak();
                edge.state = completed_head.clone();
                edge.state.storage.set_peak(peak);
            }
        }
        self.finish_loop_exits(expr, &record, &head, breaks, protection)?;
        self.transitions.loops.insert(expr.span.id, record);
        Ok(())
    }

    /// A false head condition and explicit breaks are distinct normal exits.
    /// Returns and exits targeting an enclosing label continue unwinding.
    fn finish_loop_exits(
        &mut self,
        expr: &Expr,
        record: &Loop,
        head: &super::super::lifetime::BranchState,
        breaks: Vec<super::super::control::Edge>,
        protection: (std::collections::HashSet<VarIdent>, std::collections::HashSet<VarIdent>),
    ) -> Result<(), VirErr> {
        let mut result = if record.conditional {
            if record.single_visit {
                self.restore_branch(head);
            }
            Some(super::super::lifetime::Value::unit())
        } else {
            None
        };
        let mut owner = None;
        self.flow.reachable = result.is_some();
        for mut edge in breaks {
            edge.state.heap.unprotect(protection.clone());
            if let Some(result) = &mut result {
                edge.align_result_role(owner.as_ref())?;
                self.join_exit(&edge.span, &edge.state)?;
                result.merge(&edge.value);
                owner = super::super::control::merge_result(&expr.span, owner, edge.owner)?;
            } else {
                self.restore_branch(&edge.state);
                result = Some(edge.value);
                owner = edge.owner;
            }
        }
        self.heap.unprotect(protection);
        self.produced = result;
        self.result_owner = owner;
        Ok(())
    }
}
