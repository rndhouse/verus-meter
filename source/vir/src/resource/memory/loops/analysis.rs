//! Inductive memory proofs consume the shared loop record and checked transfers.

use super::{Charge, Loop, Transfer};
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, contracts};

impl Analysis<'_> {
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

    /// Preserve zero charge only with an explicit, checked loop invariant.
    /// Potential backing writes also invalidate first-visit zero shortcuts.
    fn loop_zero_candidates(
        &mut self,
        record: &Loop,
        facts: &mut Vec<Expr>,
    ) -> std::collections::HashSet<usize> {
        let mut zero = std::collections::HashSet::new();
        for (name, owner) in self.heap.owners.iter().chain(self.heap.borrowed.iter()) {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                let location = (name.clone(), path.clone());
                if let Some(id) = node.vector {
                    self.growth.vectors[id].loop_backing |= record.grows_backing(&location);
                }
                if !record.grows_children(&location) {
                    if let Some(elements) = &node.elements {
                        for id in elements.states.values() {
                            if self.growth.elements[*id].unchanged_zero() {
                                zero.insert(*id);
                                facts.push(crate::ast_util::mk_eq(
                                    &record.span,
                                    &self.growth.elements[*id].bytes,
                                    &contracts::literal(&record.span, 0),
                                ));
                            }
                        }
                    }
                }
            });
        }
        zero
    }

    /// Completed summary evidence becomes ordinary inductive proof candidates.
    /// Failed or partial inference cannot modify the body proof state.
    pub(in super::super) fn apply_loop_evidence(
        &mut self,
        loops: &std::collections::HashMap<u64, Vec<Transfer>>,
        growth: &std::collections::HashMap<u64, Vec<(super::super::paths::LocalPath, Expr)>>,
        scratch: &std::collections::HashMap<u64, Expr>,
        repetitions: &std::collections::HashMap<u64, Expr>,
    ) -> Result<(), VirErr> {
        for (id, transfers) in loops {
            let record = self.transitions.loops[id].clone();
            self.growth.loops.entry(*id).or_default().extend(record.conservation(transfers));
            if transfers.iter().any(|transfer| transfer.additional.is_some()) {
                let mut additions = std::collections::BTreeMap::new();
                for transfer in transfers {
                    if let Some(amount) = &transfer.additional {
                        additions
                            .entry(transfer.target)
                            .and_modify(|old: &mut Expr| {
                                *old =
                                    contracts::maximum(&record.span, old.clone(), amount.clone());
                            })
                            .or_insert_with(|| amount.clone());
                    }
                }
                let amount = additions
                    .into_values()
                    .fold(contracts::literal(&record.span, 0), |sum, amount| {
                        contracts::add(&record.span, sum, amount)
                    });
                self.reserve_loop_headroom(&record, amount, scratch.get(id))?;
            }
        }
        for (id, allowance) in repetitions {
            let record = self.transitions.loops[id].clone();
            let sum = |entry: bool| {
                record.charges.iter().fold(contracts::literal(&record.span, 0), |sum, charge| {
                    let mut amount =
                        if entry { charge.entry.clone() } else { charge.current.clone() };
                    if let Some((current, initial)) = &charge.backing {
                        amount = contracts::add(
                            &record.span,
                            amount,
                            if entry { initial.clone() } else { current.clone() },
                        );
                    }
                    contracts::add(&record.span, sum, amount)
                })
            };
            let mut upper = sum(true);
            if contracts::constant(allowance) != Some(0) {
                let (completed, entry) = record.completed.clone().ok_or_else(|| {
                    super::super::model::unsupported(
                        &record.span,
                        "allocation growth without a checked iteration progress observation",
                    )
                })?;
                self.growth.loops.entry(*id).or_default().extend([
                    crate::ast_util::mk_ineq(
                        &record.span,
                        &contracts::literal(&record.span, 0),
                        &entry,
                        InequalityOp::Le,
                    ),
                    crate::ast_util::mk_ineq(
                        &record.span,
                        &contracts::literal(&record.span, 0),
                        &completed,
                        InequalityOp::Le,
                    ),
                ]);
                upper = contracts::add(
                    &record.span,
                    upper,
                    contracts::multiply(&record.span, allowance.clone(), completed),
                );
                self.reserve_loop_headroom(&record, allowance.clone(), scratch.get(id))?;
            }
            self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                &record.span,
                &sum(false),
                &upper,
                InequalityOp::Le,
            ));
        }
        for (id, bounds) in growth {
            let record = &self.transitions.loops[id];
            let mut envelopes = std::collections::BTreeMap::<_, Expr>::new();
            for (location, amount) in bounds {
                envelopes
                    .entry(location)
                    .and_modify(|old| {
                        *old = contracts::maximum(&record.span, old.clone(), amount.clone());
                    })
                    .or_insert_with(|| amount.clone());
            }
            for (location, amount) in envelopes {
                // These append envelopes describe owning children. Scalar
                // vector backing follows its existing growth policy; its new
                // snapshot is needed only by the ordered recurrence's sum.
                if let Some(charge) = record.charges.iter().find(|charge| {
                    &charge.location == location && contracts::constant(&charge.current) != Some(0)
                }) {
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
                    self.growth
                        .loops
                        .entry(*id)
                        .or_default()
                        .extend(charge.append_backing(&record.span));
                }
            }
        }
        for (id, record) in &self.transitions.loops {
            self.growth.loops.entry(*id).or_default().extend(record.element_facts.iter().cloned());
        }
        self.inherit_loop_entries()
    }

    /// Reserve temporary and retained headroom using ordinary entry checks and
    /// inductive invariants, shared by disjoint and evolving loop summaries.
    fn reserve_loop_headroom(
        &mut self,
        record: &Loop,
        amount: Expr,
        scratch: Option<&Expr>,
    ) -> Result<(), VirErr> {
        let visits = record
            .visits_bound
            .clone()
            .unwrap_or_else(|| contracts::literal(&record.span, record.size_ceiling.unwrap_or(0)));
        if contracts::constant(&amount).is_none() {
            // Ordinary queries treat general multiplication as uninterpreted.
            // Supply pointwise order and successor facts for this envelope.
            self.growth.before.entry(record.span.id).or_default().push(
                super::super::metadata::expr::lemma(
                    &record.span,
                    "product_bounds",
                    vec![amount.clone(), contracts::literal(&record.span, 0), visits.clone()],
                ),
            );
            if let Some(observation) = &record.progress {
                self.growth.before.entry(record.body.span.id).or_default().push(
                    super::super::metadata::expr::lemma(
                        &record.body.span,
                        "product_bounds",
                        vec![amount.clone(), observation.ordinal.clone(), visits.clone()],
                    ),
                );
            }
        }
        let reserve = contracts::multiply(&record.span, amount, visits);
        let call_ceiling = scratch.cloned().unwrap_or_else(|| contracts::literal(&record.span, 0));
        let mut local_peak = contracts::literal(&record.span, 0);
        for cost in &record.local_costs {
            // Body-local scalar aliases do not exist at the loop head.
            // Their helper allowances use checked iteration ceilings;
            // explicit layout charges and stable bounds stay unchanged.
            let cost = cost.map(&record.span, &|amount| {
                        let stable = crate::ast_visitor::expr_visitor_check(amount, &mut |scope, value| {
                            if matches!(&value.x, ExprX::Var(name) if !scope.contains_key(name) && !record.proof_scalars.contains(name)) { Err(()) } else { Ok(()) }
                        }).is_ok();
                        Ok(if stable { amount.clone() } else { call_ceiling.clone() })
                    })?;
            let selected = cost.select(
                &record.span,
                &super::super::footprint::MemorySelection::kind(
                    super::super::footprint::MemoryKind::host_local(),
                ),
            );
            local_peak = contracts::maximum(&record.span, local_peak, selected);
        }
        let reserve = contracts::add(&record.span, reserve, local_peak);
        let candidates = record
            .entry_headroom
            .iter()
            .map(|candidate| {
                let ExprX::Binary(BinaryOp::Inequality(InequalityOp::Le), live, bound) =
                    &candidate.x
                else {
                    unreachable!()
                };
                crate::ast_util::mk_ineq(
                    &record.span,
                    &contracts::add(&record.span, live.clone(), reserve.clone()),
                    bound,
                    InequalityOp::Le,
                )
            })
            .collect();
        let facts = self.freeze_loop_facts(&record.span, candidates)?;
        for fact in &facts {
            let check = SpannedTyped::new(
                &record.span,
                &crate::ast_util::unit_typ(),
                ExprX::AssertAssume {
                    is_assume: false,
                    expr: fact.clone(),
                    msg: Some(crate::messages::error(
                        &record.span,
                        "memory budget exceeded: cannot reserve heap headroom for loop allocations",
                    )),
                },
            );
            self.growth
                .before
                .entry(record.span.id)
                .or_default()
                .push(crate::def::Spanned::new(record.span.clone(), StmtX::Expr(check)));
        }
        self.growth.loops.entry(record.span.id).or_default().extend(facts);
        Ok(())
    }

    /// Count actual back edges independently of the source counter's stride.
    /// These erased updates cannot alter executable storage or overflow behavior.
    fn loop_progress(&mut self, record: &mut Loop) -> Result<Option<(Expr, Expr)>, VirErr> {
        let Some(control) = &record.control else { return Ok(None) };
        let observe = |value: &Expr| {
            if let Some(super::super::transfer::checked::Operation::Length { receiver }) =
                self.transitions.operation_at(&value.span)
            {
                let value = super::super::projections::spec_value(&receiver.source).ok()?;
                Some(self.owner_length(
                    &record.span,
                    &super::super::heap::Owner {
                        source: Some((receiver.typ.clone(), value)),
                        ..Default::default()
                    },
                ))
            } else {
                super::super::projections::spec_value(value).ok()
            }
        };
        let observations = if record.iterator.is_some() {
            (Some(control.start.clone()), Some(control.end.clone()))
        } else {
            (observe(&control.start), observe(&control.end))
        };
        let (Some(left), Some(right)) = observations else {
            return Ok(None);
        };
        let left = SpannedTyped::new(&record.span, &crate::ast_util::int_typ(), left.x.clone());
        let right = SpannedTyped::new(&record.span, &crate::ast_util::int_typ(), right.x.clone());
        // A logical role and the progress condition observe the same entry
        // length. Reuse its snapshot so isolated queries retain that identity.
        let mut snapshot = |source: &Expr, value: &Expr| {
            if let Some(super::super::transfer::checked::Operation::Length { receiver }) =
                self.transitions.operation_at(&source.span)
            {
                if let Some(entry) = record.entry_length(&receiver.location) {
                    return entry;
                }
            }
            if let Some(name) = super::local(source) {
                let current =
                    SpannedTyped::new(&record.span, &crate::ast_util::int_typ(), ExprX::Var(name));
                return self.loop_snapshot(&record.span, &current);
            }
            self.loop_snapshot(&record.span, value)
        };
        let bounds = (snapshot(&control.start, &left), snapshot(&control.end, &right));
        let mut scalars = std::collections::HashMap::new();
        for name in record
            .scalar_steps
            .keys()
            .filter(|name| self.slots.contains_key(*name))
            .cloned()
            .collect::<Vec<_>>()
        {
            let current = SpannedTyped::new(
                &record.span,
                &crate::ast_util::int_typ(),
                ExprX::Var(name.clone()),
            );
            let initial = self.loop_snapshot(&record.span, &current);
            scalars.insert(name, (current, initial));
        }
        let zero = contracts::literal(&record.span, 0);
        let (ordinal, declaration) = super::super::metadata::expr::local(
            &record.span,
            "loop_visits",
            crate::ast_util::int_typ(),
            zero.clone(),
            Mode::Spec,
        );
        self.growth.before.entry(record.span.id).or_default().push(declaration);
        self.growth.after.entry(record.body.span.id).or_default().push(
            super::super::metadata::expr::assign(
                &record.body.span,
                &ordinal,
                contracts::add(
                    &record.body.span,
                    ordinal.clone(),
                    contracts::literal(&record.body.span, 1),
                ),
            ),
        );
        record.progress =
            Some(super::progress::Observation { ordinal: ordinal.clone(), bounds, scalars });
        Ok(Some((ordinal, zero)))
    }

    /// Publish only validated translations and length changes as ordinary loop
    /// invariants. Each relationship is proved at entry and on every back edge.
    pub(in super::super) fn apply_progress_evidence(
        &mut self,
        evidence: &std::collections::HashMap<u64, super::progress::Evidence>,
    ) {
        for (id, evidence) in evidence {
            let record = self.transitions.loops.get_mut(id).unwrap();
            let Some(observation) = &record.progress else { continue };
            let span = &record.span;
            let ordinal = &observation.ordinal;
            let gap = record.control.as_ref().unwrap().gap(
                evidence.bounds.0.clone().unwrap_or_else(|| observation.bounds.0.clone()),
                evidence.bounds.1.clone().unwrap_or_else(|| observation.bounds.1.clone()),
            );
            let bound = super::progress::count(span, gap, evidence.stride);
            record.visits_bound = Some(bound.clone());
            if !record.head_breaks.is_empty() {
                // Verus cannot assume the negated while condition after a
                // break. Check the completed count on all real exits instead.
                self.growth
                    .loop_ensures
                    .entry(*id)
                    .or_default()
                    .push(crate::ast_util::mk_eq(span, ordinal, &bound));
            }
            let mut facts = vec![
                crate::ast_util::mk_ineq(
                    span,
                    &contracts::literal(span, 0),
                    ordinal,
                    InequalityOp::Le,
                ),
                crate::ast_util::mk_ineq(span, ordinal, &bound, InequalityOp::Le),
            ];
            for (source, snapshot) in [
                (&record.control.as_ref().unwrap().start, &observation.bounds.0),
                (&record.control.as_ref().unwrap().end, &observation.bounds.1),
            ] {
                if let Some(name) = super::local(source) {
                    if !record.effects.writes.contains(&name) {
                        let current =
                            SpannedTyped::new(span, &crate::ast_util::int_typ(), ExprX::Var(name));
                        facts.push(crate::ast_util::mk_eq(span, snapshot, &current));
                    }
                }
            }
            for (snapshot, initial) in [
                (&observation.bounds.0, &evidence.bounds.0),
                (&observation.bounds.1, &evidence.bounds.1),
            ] {
                if let Some(initial) = initial {
                    facts.push(crate::ast_util::mk_eq(span, snapshot, initial));
                }
            }
            for (name, initial) in &evidence.scalars {
                if let Some((_, snapshot)) = observation.scalars.get(name) {
                    facts.push(crate::ast_util::mk_eq(span, snapshot, initial));
                }
            }
            for (name, definition) in &evidence.definitions {
                let current = SpannedTyped::new(span, &definition.typ, ExprX::Var(name.clone()));
                facts.push(crate::ast_util::mk_eq(span, &current, definition));
            }
            for (location, initial) in &evidence.entry_lengths {
                if let Some(charge) =
                    record.charges.iter().find(|charge| &charge.location == location)
                {
                    facts.push(crate::ast_util::mk_eq(span, &charge.length.1, initial));
                }
            }
            let translated = |initial: &Expr, step: i128| {
                if step >= 0 {
                    contracts::add(
                        span,
                        initial.clone(),
                        contracts::multiply(
                            span,
                            super::super::metadata::expr::integer(span, step),
                            ordinal.clone(),
                        ),
                    )
                } else {
                    contracts::subtract(
                        span,
                        initial.clone(),
                        contracts::multiply(
                            span,
                            super::super::metadata::expr::integer(span, -step),
                            ordinal.clone(),
                        ),
                    )
                }
            };
            if let Some(iterator) = &record.iterator {
                facts.push(crate::ast_util::mk_eq(
                    span,
                    &iterator.position,
                    &translated(&observation.bounds.0, 1),
                ));
                facts.push(crate::ast_util::mk_eq(span, &iterator.length, &observation.bounds.1));
            }
            for (name, (current, initial)) in &observation.scalars {
                let (_, step) = &record.scalar_steps[name];
                facts.push(crate::ast_util::mk_eq(span, current, &translated(initial, *step)));
            }
            for (location, step) in &evidence.lengths {
                if let Some(charge) =
                    record.charges.iter().find(|charge| &charge.location == location)
                {
                    let expected = translated(&charge.length.1, *step);
                    let expected = if *step < 0 {
                        contracts::maximum(span, contracts::literal(span, 0), expected)
                    } else {
                        expected
                    };
                    facts.push(crate::ast_util::mk_eq(span, &charge.length.0, &expected));
                }
            }
            for (location, expected) in &evidence.prefixes {
                if let Some(charge) =
                    record.charges.iter().find(|charge| &charge.location == location)
                {
                    facts.push(crate::ast_util::mk_eq(span, &charge.length.0, expected));
                }
            }
            self.growth.loops.entry(*id).or_default().extend(facts);
        }
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
            if record.single_visit {
                continue;
            }
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
            let facts = self.growth.loops.get(&parent).cloned().unwrap_or_default();
            let facts = if let Some(iterator) = &records[&parent].iterator {
                facts.iter().map(|fact| iterator.body_fact(fact)).collect::<Result<_, _>>()?
            } else {
                facts
            };
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
                if node.vector.is_some()
                    || node.elements.as_ref().is_some_and(|elements| elements.precise)
                {
                    roles.push((
                        (name.clone(), path.clone()),
                        node.elements
                            .as_ref()
                            .filter(|elements| elements.precise)
                            .map(|elements| elements.states.values().copied().collect::<Vec<_>>())
                            .unwrap_or_default(),
                        node.vector,
                        self.owner_length(span, node),
                    ));
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
        // Alternative destinations belong to one connected conservation group.
        // Pairwise bounds would incorrectly require each destination to contain
        // everything removed from the source on every branch.
        let mut groups: Vec<std::collections::BTreeSet<usize>> = Vec::new();
        for transfer in transfers {
            let mut group = std::collections::BTreeSet::from([transfer.source, transfer.target]);
            let mut index = 0;
            while index < groups.len() {
                if !groups[index].is_disjoint(&group) {
                    group.extend(groups.remove(index));
                    index = 0;
                } else {
                    index += 1;
                }
            }
            groups.push(group);
        }
        groups.sort();
        let mut candidates = Vec::new();
        for group in groups {
            let sum = |entry: bool| {
                group.iter().fold(contracts::literal(&self.span, 0), |sum, index| {
                    let charge = &self.charges[*index];
                    contracts::add(
                        &self.span,
                        sum,
                        if entry { charge.entry.clone() } else { charge.current.clone() },
                    )
                })
            };
            let mut upper = sum(true);
            let mut additions = std::collections::BTreeMap::new();
            for transfer in transfers.iter().filter(|transfer| group.contains(&transfer.source)) {
                if let Some(additional) = &transfer.additional {
                    additions
                        .entry(transfer.target)
                        .and_modify(|old: &mut Expr| {
                            *old = contracts::maximum(&self.span, old.clone(), additional.clone());
                        })
                        .or_insert_with(|| additional.clone());
                }
            }
            for (target, amount) in additions {
                let charge = &self.charges[target];
                let completed = contracts::subtract(
                    &self.span,
                    charge.length.0.clone(),
                    charge.length.1.clone(),
                );
                upper = contracts::add(
                    &self.span,
                    upper,
                    contracts::multiply(&self.span, amount, completed),
                );
            }
            candidates.push(crate::ast_util::mk_ineq(
                &self.span,
                &sum(false),
                &upper,
                InequalityOp::Le,
            ));
            if group.len() == 1 {
                let role = *group.first().unwrap();
                if transfers
                    .iter()
                    .any(|transfer| transfer.source == role && transfer.target == role)
                {
                    if let Some((bytes, entry)) = &self.charges[role].backing {
                        candidates.push(crate::ast_util::mk_ineq(
                            &self.span,
                            bytes,
                            entry,
                            InequalityOp::Le,
                        ));
                    }
                }
            }
        }
        let targets: std::collections::BTreeSet<_> = transfers
            .iter()
            .filter(|transfer| transfer.additional.is_some() && transfer.source != transfer.target)
            .map(|transfer| transfer.target)
            .collect();
        for target in targets {
            let charge = &self.charges[target];
            candidates.push(crate::ast_util::mk_ineq(
                &self.span,
                &contracts::literal(&self.span, 0),
                &charge.length.1,
                InequalityOp::Le,
            ));
            candidates.extend(charge.append_backing(&self.span));
        }
        candidates
    }
}

impl Charge {
    /// Entry reservation remains available while append-only backing can grow.
    /// Retained root bytes are separate from the appended children's charges.
    fn append_backing(&self, span: &crate::messages::Span) -> Vec<Expr> {
        let (Some((bytes, entry)), Some((capacity, initial, element))) =
            (&self.backing, &self.reservation)
        else {
            return Vec::new();
        };
        let replacement = contracts::multiply(
            span,
            contracts::literal(span, *element),
            crate::resource::memory::growth::grown_capacity(span, self.length.0.clone(), *element),
        );
        let upper = crate::resource::memory::growth::select(
            span,
            crate::ast_util::mk_ineq(span, &self.length.0, initial, InequalityOp::Le),
            entry.clone(),
            contracts::maximum(span, entry.clone(), replacement),
        );
        vec![
            crate::ast_util::mk_ineq(span, initial, capacity, InequalityOp::Le),
            crate::ast_util::mk_ineq(span, bytes, &upper, InequalityOp::Le),
        ]
    }
}
