//! A section has a relative byte contract but executes on the caller's thread.
//! Its synchronization state crosses the boundary on each normal and early exit.

use super::{Accounting, Live, MemoryReport, Point};
use crate::{ast::Expr, messages::Span};
use std::sync::Arc;

impl Accounting {
    /// Start one relative ledger per entry guard condition. The outer frame
    /// remains live even while an inner acquire is blocked.
    pub(in super::super) fn enter_section(&mut self, parent: &Self) {
        let conditions: std::collections::BTreeSet<_> =
            parent.paths.iter().map(|path| path.held.clone()).collect();
        self.paths = conditions
            .into_iter()
            .map(|held| Live {
                section_entry: Some(held.iter().copied().collect()),
                held,
                ..Default::default()
            })
            .collect();
    }

    pub(in super::super) fn holding_any(&self) -> bool {
        self.paths.iter().any(|path| !path.held.is_empty())
    }

    /// Freeze symbolic outer charges at entry. Child bookkeeping may subsequently
    /// mutate a vector's byte variable. Outer values and input identities survive
    /// conservatively through the independently contracted section.
    pub(in super::super) fn section_prefixes(
        &self,
        span: &Span,
        mut freeze: impl FnMut(Expr) -> Expr,
    ) -> Vec<Point> {
        self.paths
            .iter()
            .map(|path| {
                let mut path = path.clone();
                for charge in path.dynamic.values_mut() {
                    charge.amount = freeze(charge.amount.clone());
                }
                Point {
                    span: span.clone(),
                    cost: Self::path_expression(&path, span),
                    fixed_origins: path.fixed_origins(),
                    allocations: path.dynamic.keys().copied().collect(),
                    inputs: path.inputs,
                    values: path.values.into_keys().collect(),
                    condition: super::super::synchronization::local::Condition {
                        held: path.held.into_iter().collect(),
                        ..Default::default()
                    },
                    section_entry: path.section_entry,
                }
            })
            .collect()
    }

    /// The parent's declared allowance already bounds inner checkpoints. Preserve
    /// the more precise observations for worker composition and the condition on
    /// that allowance only where the guard persists throughout the section.
    pub(in super::super) fn compose_section_phases(
        &mut self,
        prefixes: &[Point],
        report: &MemoryReport,
        allowance_start: usize,
    ) {
        if prefixes.is_empty() {
            return;
        }
        let points = Arc::make_mut(&mut self.report.points);
        for allowance in &mut points[allowance_start..] {
            let entry = allowance.condition.held.clone();
            allowance.condition.held.retain(|interval| {
                report
                    .points
                    .iter()
                    .filter(|point| point.section_entry.as_deref() == Some(entry.as_slice()))
                    .all(|point| point.condition.held.contains(interval))
            });
        }
        for point in report.points.iter() {
            for prefix in prefixes {
                if point.section_entry.as_deref() != Some(prefix.condition.held.as_slice()) {
                    continue;
                }
                let mut phase = point.clone();
                phase.section_entry.clone_from(&prefix.section_entry);
                phase.cost = prefix.cost.add(&point.span, point.cost.clone());
                phase.fixed_origins.extend(&prefix.fixed_origins);
                phase.allocations.extend(prefix.allocations.iter().copied());
                phase.inputs.extend(prefix.inputs.iter().copied());
                phase.values.extend(prefix.values.iter().copied());
                points.push(phase);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{VarIdent, VarIdentDisambiguate},
        resource::memory::{
            contracts,
            footprint::MemoryKind,
            synchronization::{Effects, Operation, Outcome, local::Interval},
        },
    };

    #[test]
    fn a_section_preserves_the_relation_between_an_outer_buffer_and_its_guard() {
        let span = Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "section entry".into(),
        };
        let mut effects = Effects::default();
        let name = |id| VarIdent(Arc::new("binding".into()), VarIdentDisambiguate::VirTemp(id));
        let mutex = name(0);
        let instance = effects.construct(mutex.clone()).unwrap();
        let acquisition = effects
            .acquire(&mutex, name(1), Operation::MutexLock, Outcome::Acquired)
            .unwrap()
            .unwrap();
        let interval = Interval { instance, acquisition };

        let mut outer = Accounting::new(&span, 1024);
        let plain = outer.clone();
        outer
            .acquire_interval(&span, interval, Operation::MutexLock.acquisition_contract().unwrap())
            .unwrap();
        outer.reserve_owned(&span, MemoryKind::host_heap(), 64, "conditional buffer").unwrap();
        outer.join_live(&plain).unwrap();

        let mut inner = Accounting::new(&span, 1024);
        inner.enter_section(&outer);
        inner.record_live(&span).unwrap();
        let prefixes = outer.section_prefixes(&span, |amount| amount);
        let report = inner.finish_section(&span);
        let before = outer.points().len();
        outer.compose_section_phases(&prefixes, &report, before);
        let phases = &outer.points()[before..];
        assert_eq!(phases.len(), 2);
        for phase in phases {
            let held = phase.condition.held.contains(&interval);
            assert_eq!(contracts::constant(&phase.cost.total()), Some(if held { 64 } else { 0 }));
            assert_eq!(phase.fixed_origins.len(), usize::from(held));
        }
    }
}
