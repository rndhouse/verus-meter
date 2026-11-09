//! Independently checked section contracts, composed like function contracts.

use super::accounting::{Accounting, CheckKind, Obligation};
use super::analysis::Analysis;
use super::budget::{BudgetExpr, evaluate_body_budget};
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
        let budget = evaluate_body_budget(budget, self.budgets, self.functions, self.layouts)?;
        // Enclosing storage and earlier peaks belong to the parent. Keep the
        // mode environment and call graph shared, since this is still its code.
        let parent = std::mem::replace(&mut self.storage, Accounting::new(contract_span, budget));
        // An enclosing loop must not add its previous iteration's peak to a
        // child checkpoint: the child starts fresh each time it is entered.
        let parent_slots = self.slots.clone();
        let parent_checkpoints = std::mem::take(&mut self.checkpoints);
        let protection = self.heap.protect();
        let protected = self.growth.section_protected.clone();
        let protected_elements = self.growth.protected_elements.clone();
        self.growth.protected_elements.extend(self.heap.element_states());
        self.growth.section_protected.extend(self.heap.vectors());
        let outer_bound =
            std::mem::replace(&mut self.bound, super::contracts::literal(contract_span, budget));
        self.block_contents(expr, stmts, tail)?;
        self.heap.unprotect(protection);
        self.bound = outer_bound;
        self.growth.section_protected = protected;
        self.growth.protected_elements = protected_elements;
        self.check_checkpoints()?;
        let section = std::mem::replace(&mut self.storage, parent);
        self.checkpoints = parent_checkpoints;
        let report = section.finish_section(contract_span);
        let bound = super::contracts::literal(contract_span, budget);
        self.obligations.extend(report.cost_points.iter().map(|(span, cost)| Obligation {
            span: span.clone(),
            cost: cost.clone(),
            bound: super::footprint::MemoryBudget::total(bound.clone()),
            kind: CheckKind::Section,
        }));
        self.storage.event(
            contract_span,
            format!(
                "checked section: local peak {} bytes, declared bound {} bytes",
                report.peak, budget,
            ),
        );
        // The parent relies on the declared contract, including slack, rather
        // than the implementation's measured peak. Siblings reuse this allowance.
        self.storage.section_allowance(contract_span, budget)?;
        // A value originating outside the section belongs to the outer budget.
        // If the section consumed it, it must not remain live afterward.
        for (name, value) in parent_slots {
            if !self.slots.contains_key(&name) {
                self.storage.release_values(&value.ids);
            }
        }
        Ok(())
    }
}
