//! Inductive memory proofs consume the shared loop record and checked transfers.
//!
//! This module orchestrates entry snapshots, one reusable body visit, inductive
//! candidates, and exits. Charge construction, summary evidence, progress facts,
//! and nested entry propagation live in focused child modules.

mod charges;
mod evidence;
mod nested;
mod visits;

use super::Loop;
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, contracts};

impl Analysis<'_> {
    /// Analyze one reusable visit, then attach its memory invariants and exit states.
    pub(in super::super) fn analyze_loop(&mut self, expr: &Expr) -> Result<(), VirErr> {
        let mut record = Loop::new(expr, self.layouts, self.summaries)?;
        let nested = self.growth.loop_depth > 0;
        record.nested = nested;
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
        let first_cost = self.storage.peak().costs.len();
        let entry_heap = self.storage.live_expression(&expr.span).select(
            &expr.span,
            &super::super::footprint::MemorySelection::kind(
                super::super::footprint::MemoryKind::host_heap(),
            ),
        );
        self.storage.event(&expr.span, "analyze reusable while iteration".into());
        self.growth.loop_depth += 1;
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
        self.discard(&record.condition)?;
        record.completed = self.loop_progress(&mut record)?;
        let head = self.branch_state();
        let first_exit = self.flow.exits.len();
        self.discard(&record.body)?;
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
            if let Some((ordinal, _)) = &record.completed {
                self.growth.before.entry(edge.span.id).or_default().push(
                    super::super::metadata::expr::assign(
                        &edge.span,
                        ordinal,
                        contracts::add(
                            &edge.span,
                            ordinal.clone(),
                            contracts::literal(&edge.span, 1),
                        ),
                    ),
                );
            }
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
        record.local_costs =
            iteration_peak.costs[first_cost..].iter().map(|(_, cost)| cost.clone()).collect();
        let candidate =
            crate::ast_util::mk_ineq(&expr.span, &entry_heap, &self.bound, InequalityOp::Le);
        record.entry_headroom = vec![candidate];
        for checkpoint in &mut self.checkpoints[first_checkpoint..] {
            checkpoint.peak.merge(&iteration_peak);
        }
        self.heap.unprotect(protection.clone());
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
