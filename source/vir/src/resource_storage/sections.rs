//! Independently checked section contracts, composed like function contracts.

use super::accounting::Accounting;
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
        let parent_checkpoints = std::mem::take(&mut self.checkpoints);
        self.block_contents(expr, stmts, tail)?;
        self.check_checkpoints()?;
        let section = std::mem::replace(&mut self.storage, parent);
        self.checkpoints = parent_checkpoints;
        let report = section.finish_section(contract_span)?;
        self.storage.event(
            contract_span,
            format!(
                "checked section: local peak {} bytes, declared bound {} bytes",
                report.peak, budget,
            ),
        );
        // The parent relies on the declared contract, including slack, rather
        // than the implementation's measured peak. Siblings reuse this allowance.
        self.storage.reserve(contract_span, budget, "section declared bound")?;
        self.storage.release(contract_span, budget, "section exit");
        Ok(())
    }
}
