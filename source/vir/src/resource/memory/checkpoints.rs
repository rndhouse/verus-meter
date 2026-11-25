//! Keep each scoped obligation with the reaching ownership state until worker composition.
//! Peak history follows normal control-flow merges, including previous loop iterations.
use super::{
    accounting::{CheckKind, Obligation, Peak, Point},
    analysis::Analysis,
    budget::BudgetExpr,
    contracts,
    footprint::{Footprint, MemoryBudget},
    growth::Growth,
    model::unsupported,
};
use crate::{
    ast::*,
    messages::{AstId, Span},
};

/// A cumulative bound and the history visible where it is asserted.
pub(super) struct Checkpoint {
    // The assertion location used for diagnostics.
    span: Span,
    // Maximum permitted cumulative model bytes at this assertion.
    budget: u64,
    /// Historical cost points that can precede this assertion.
    pub(super) peak: Peak,
}

/// Evaluate the bound at the source observation, in the nearest budgeted scope.
pub(super) struct ScopedCheck {
    /// Reaching local charges, tags and guards at the original executable site.
    pub(super) point: Point,
    pub(super) bound: Expr,
    /// A population contributes only when this scope covers its publication.
    pub(super) section: Option<AstId>,
    pub(super) kind: CheckKind,
}

impl ScopedCheck {
    pub(super) fn obligation(&self, concurrent: Option<Footprint>, growth: &Growth) -> Obligation {
        Obligation {
            contributor: concurrent.as_ref().and_then(|_| growth.point_contributor(&self.point)),
            span: self.point.span.clone(),
            cost: concurrent.unwrap_or_else(|| self.point.cost.clone()),
            bound: MemoryBudget::total(self.bound.clone()),
            kind: self.kind,
        }
    }
}

impl Analysis<'_> {
    pub(super) fn checkpoint(&mut self, expr: &Expr, budget: &BudgetExpr) -> Result<(), VirErr> {
        let budget =
            super::budget::checkpoint_budget(budget, self.budgets, self.functions, self.layouts)?;
        if matches!(expr.x, ExprX::ResourceAssert(_)) {
            if self.current_worker.is_some() && self.section_scopes.is_empty() {
                self.growth.ancestor_query.get_or_insert_with(|| expr.span.clone());
            }
            self.checkpoints.push(Checkpoint {
                span: expr.span.clone(),
                budget,
                peak: self.storage.peak(),
            });
            return Ok(());
        }
        let cost = self.storage.live_expression(&expr.span);
        self.observe_shared_checkpoint(&expr.span, &cost, budget)?;
        let bound = contracts::literal(&expr.span, budget);
        if self.concurrency.closures.is_empty() {
            self.obligations.push(Obligation {
                contributor: None,
                span: expr.span.clone(),
                cost,
                bound: MemoryBudget::total(bound),
                kind: CheckKind::CurrentCheckpoint,
            });
        } else {
            for point in self.storage.current_points(&expr.span) {
                self.defer_scoped(point, &bound, CheckKind::CurrentCheckpoint);
            }
        }
        Ok(())
    }

    /// Preserve the original local checks when there is no composed worker domain.
    pub(super) fn local_scoped_checks(&mut self) {
        for query in self.growth.scoped_checks.values().flatten() {
            self.obligations.push(query.obligation(None, &self.growth));
        }
    }

    pub(super) fn defer_scoped(&mut self, point: Point, bound: &Expr, kind: CheckKind) {
        self.growth.scoped_checks.entry(self.current_worker).or_default().push(ScopedCheck {
            point,
            bound: bound.clone(),
            section: self.section_scopes.last().copied(),
            kind,
        });
    }

    pub(super) fn check_checkpoints(&mut self) -> Result<(), VirErr> {
        let mut historical = std::collections::HashMap::<_, Vec<_>>::new();
        if !self.concurrency.closures.is_empty() && !self.checkpoints.is_empty() {
            for point in self.storage.points() {
                historical.entry((point.span.id, point.cost.identity())).or_default().push(point);
            }
        }
        for checkpoint in &self.checkpoints {
            for (span, cost) in &checkpoint.peak.costs {
                if !self.concurrency.closures.is_empty() {
                    let points = historical.get(&(span.id, cost.identity())).ok_or_else(|| {
                        unsupported(
                            span,
                            "a peak checkpoint without its reaching ownership observation",
                        )
                    })?;
                    for &point in points {
                        self.growth.scoped_checks.entry(self.current_worker).or_default().push(
                            ScopedCheck {
                                point: point.clone(),
                                bound: contracts::literal(&checkpoint.span, checkpoint.budget),
                                section: self.section_scopes.last().copied(),
                                kind: CheckKind::Checkpoint,
                            },
                        );
                    }
                    continue;
                }
                self.obligations.push(Obligation {
                    contributor: None,
                    span: span.clone(),
                    cost: cost.clone(),
                    bound: MemoryBudget::total(contracts::literal(
                        &checkpoint.span,
                        checkpoint.budget,
                    )),
                    kind: CheckKind::Checkpoint,
                });
            }
        }
        Ok(())
    }
}
