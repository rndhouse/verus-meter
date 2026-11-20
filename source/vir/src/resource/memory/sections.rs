//! Independently checked section contracts, composed like function contracts.

use super::accounting::{Accounting, CheckKind, Obligation};
use super::analysis::Analysis;
use super::budget::{BudgetExpr, evaluate_envelope};
use super::contracts;
use crate::ast::*;
use crate::messages::Span;

impl Analysis<'_> {
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
            let immutable = |name: &VarIdent| {
                self.stable_scalars.contains(name) || self.growth.immutable_slices.contains(name)
            };
            let mut stable = true;
            crate::ast_visitor::expr_visitor_check(&formula, &mut |_, term| {
                // Lowering a collection length keeps its receiver as a read
                // of the Rust place. A mutable vector must retain its snapshot.
                stable &= match &term.x {
                    ExprX::Var(name) => immutable(name),
                    ExprX::ReadPlace(place, _) => {
                        matches!(&place.x, PlaceX::Local(name) if immutable(name))
                    }
                    _ => true,
                };
                Ok::<(), VirErr>(())
            })?;
            if stable { formula } else { self.allocation_snapshot(contract_span, formula) }
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
            let backing = self.growth.vectors[id].backing.clone();
            let entry = self.allocation_snapshot(contract_span, backing.bytes.clone());
            self.growth.section_backings.entry(id).or_default().push(entry.clone());
            let bytes = super::growth::section_bytes(contract_span, backing.bytes, entry);
            self.storage.set_allocation(backing.id, backing.kind, bytes);
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
        self.obligations.extend(report.points.iter().map(|point| Obligation {
            span: point.span.clone(),
            cost: point.cost.clone(),
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
