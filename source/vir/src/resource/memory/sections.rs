//! Independently checked section contracts, composed like function contracts.

use super::accounting::{Accounting, CheckKind, Obligation};
use super::analysis::Analysis;
use super::budget::{BudgetExpr, evaluate_envelope};
use super::contracts;
use crate::ast::*;
use crate::messages::Span;

impl Analysis<'_> {
    /// A replacement belongs to every active section around its owner. Capture
    /// the possible new buffer before the operation mutates the vector length.
    pub(super) fn record_section_replacement(
        &mut self,
        span: &Span,
        id: usize,
        replacement: &Expr,
    ) {
        if let Some(scopes) = self.growth.section_backings.get(&id) {
            for local in scopes {
                let retained =
                    super::allocations::retained_bytes(span, local.clone(), replacement.clone());
                self.growth
                    .updates
                    .entry(span.id)
                    .or_default()
                    .push(super::symbolic::assign(span, local, retained));
            }
        }
    }

    pub(super) fn section(
        &mut self,
        expr: &Expr,
        contract_span: &Span,
        budget: &BudgetExpr,
        stmts: &[Stmt],
        tail: &Option<Expr>,
    ) -> Result<(), VirErr> {
        let envelope = evaluate_envelope(budget, self.budgets, self.functions, self.layouts)?;
        let allowed = self
            .var_modes
            .iter()
            .filter(|(_, mode)| **mode == Mode::Exec)
            .map(|(name, _)| name.clone())
            .collect();
        let formula =
            contracts::lower(budget, &allowed, self.budgets, self.functions, self.layouts)?;
        let bound = if contracts::constant(&formula).is_some() {
            formula
        } else {
            // Re-entering this section takes a fresh snapshot. Its body, its
            // loops, and its parent must all use the same entry allowance.
            super::symbolic::range_checks(
                &formula,
                &crate::ast_util::mk_bool(contract_span, true),
                self.growth.before.entry(contract_span.id).or_default(),
            );
            self.allocation_snapshot(contract_span, formula)
        };
        // Enclosing storage and earlier peaks belong to the parent. Keep the
        // mode environment and call graph shared, since this is still its code.
        let parent = std::mem::replace(&mut self.storage, Accounting::new(contract_span, envelope));
        // An enclosing loop must not add its previous iteration's peak to a
        // child checkpoint: the child starts fresh each time it is entered.
        let parent_slots = self.slots.clone();
        let parent_checkpoints = std::mem::take(&mut self.checkpoints);
        let protection = self.heap.protect();
        let mut vectors = self.heap.vectors();
        vectors.sort_unstable();
        vectors.dedup();
        for &id in &vectors {
            let zero = super::contracts::literal(contract_span, 0);
            let local = self.allocation_snapshot(contract_span, zero);
            self.growth.section_backings.entry(id).or_default().push(local.clone());
            let backing = &self.growth.vectors[id].backing;
            // Both the section's replacement bound and the owner's full backing
            // bound apply. The latter also carries the owner's loop invariants.
            let bytes = super::contracts::minimum(contract_span, local, backing.bytes.clone());
            self.storage.set_allocation(backing.id, backing.kind.clone(), bytes);
        }
        let protected_elements = self.growth.protected_elements.clone();
        let section_shared = self.growth.section_shared.clone();
        self.growth.section_shared.extend(self.heap.shared.allocation_ids());
        let section_owners = self.growth.section_owners.clone();
        self.growth
            .section_owners
            .extend(self.heap.owners.keys().chain(self.heap.borrowed.keys()).cloned());
        self.growth.protected_elements.extend(self.heap.element_states());
        let outer_bound = std::mem::replace(&mut self.bound, bound.clone());
        let first_exit = self.flow.exits.len();
        self.block_contents(expr, stmts, tail)?;
        self.heap.unprotect(protection.clone());
        self.bound = outer_bound;
        // The parent already tracks this owner through the same proof state.
        // Remove the section's relative charge on every exit before composing.
        for id in vectors {
            let scopes = self.growth.section_backings.get_mut(&id).unwrap();
            scopes.pop();
            if scopes.is_empty() {
                self.growth.section_backings.remove(&id);
            }
            let allocation = self.growth.vectors[id].backing.id;
            self.storage.release_dynamic(allocation);
            for edge in &mut self.flow.exits[first_exit..] {
                edge.state.storage.release_dynamic(allocation);
            }
        }
        self.growth.protected_elements = protected_elements;
        self.growth.section_owners = section_owners;
        self.growth.section_shared = section_shared;
        self.check_checkpoints()?;
        let section = std::mem::replace(&mut self.storage, parent);
        self.checkpoints = parent_checkpoints;
        let retained = section.live_storage();
        let report = section.finish_section(contract_span);
        self.obligations.extend(report.cost_points.iter().map(|(span, cost)| Obligation {
            span: span.clone(),
            cost: cost.clone(),
            bound: super::footprint::MemoryBudget::total(bound.clone()),
            kind: CheckKind::Section,
        }));
        let allowance = contracts::constant(&bound)
            .map_or_else(|| "entry-dependent".into(), |n| format!("{n} bytes"));
        self.storage.event(
            contract_span,
            format!(
                "checked section: local fixed-cost peak {} bytes, declared bound {allowance}",
                report.peak,
            ),
        );
        // The parent relies on the declared contract, including slack, rather
        // than the implementation's measured peak. Siblings reuse this allowance.
        self.storage.section_allowance(contract_span, bound)?;
        for edge in &mut self.flow.exits[first_exit..] {
            let local = std::mem::replace(&mut edge.state.storage, self.storage.clone());
            edge.state.storage.retain_section_storage(&local.into_live_storage(), &edge.span)?;
            for (name, value) in &parent_slots {
                if !edge.state.slots.contains_key(name)
                    && edge.value.origins.is_disjoint(&value.ids)
                {
                    edge.state.storage.release_values(&value.ids);
                }
            }
            if let Some(id) = edge.state.storage.resume_value(
                &edge.span,
                &edge.value.ids,
                &edge.value.origins,
                edge.value.bytes,
            )? {
                edge.value.ids.insert(id);
                edge.value.origins.insert(id);
            }
            edge.state.heap.unprotect(protection.clone());
        }
        // A value originating outside the section belongs to the outer budget.
        // If the section consumed it, it must not remain live afterward.
        for (name, value) in parent_slots {
            if !self.slots.contains_key(&name) {
                self.storage.release_values(&value.ids);
            }
        }
        // A borrowed receiver's compiler scope can end outside this block.
        // Adopt its live values/backing after checking the declared allowance.
        // Exit edges above use their own retained charges, not this normal
        // path's temporaries.
        if self.flow.reachable {
            self.storage.retain_section_storage(&retained, contract_span)?;
        }
        Ok(())
    }
}
