//! Checked live/peak accounting and source-located diagnostics.

use super::contracts;
use super::footprint::{Charge, Footprint, MemoryBudget, MemoryKind, MemorySelection};
use super::model::{MODEL_NAME, unsupported};
use crate::ast::{Expr, VirErr, VirErrAs};
use crate::messages::{Span, note};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Clone, Copy)]
pub(super) enum CheckKind {
    Function,
    Section,
    Checkpoint,
}

pub(super) struct Obligation {
    pub(super) span: Span,
    pub(super) cost: Footprint,
    pub(super) bound: MemoryBudget,
    pub(super) kind: CheckKind,
}

#[derive(Clone)]
pub struct MemoryEvent {
    pub span: Span,
    pub description: String,
    pub live: u64,
    pub footprint: Footprint,
}

#[derive(Clone)]
pub struct MemoryReport {
    // A conservative call envelope can exceed u64 even when its selected cost
    // fits. Actual reservations and declared budgets still use the u64 model.
    pub peak: u128,
    pub budget: u64,
    pub events: Vec<MemoryEvent>,
    pub(super) conditional: bool,
    pub(super) cost_points: Vec<(Span, Footprint)>,
}

impl MemoryReport {
    /// Project each simultaneous footprint before taking its peak. This also
    /// retains aggregate contract slack across calls and sections.
    pub fn selected_peak(&self, span: &Span, selection: &MemorySelection) -> Expr {
        self.cost_points
            .iter()
            .map(|(_, cost)| cost.select(span, selection))
            .reduce(|a, b| contracts::maximum(span, a, b))
            .unwrap_or_else(|| contracts::literal(span, 0))
    }

    pub fn diagnostics(&self, span: &Span) -> Vec<VirErrAs> {
        let mut result = vec![VirErrAs::Note(note(
            span,
            if self.conditional {
                format!(
                    "resource model {MODEL_NAME}: fixed-cost peak {} bytes, budget envelope {} bytes; symbolic storage obligations require Verus proofs",
                    self.peak, self.budget
                )
            } else {
                format!(
                    "resource model {MODEL_NAME}: peak {} bytes, budget {} bytes",
                    self.peak, self.budget
                )
            },
        ))];
        result.extend(self.events.iter().map(|event| {
            VirErrAs::Note(note(
                &event.span,
                format!("storage: {}; live {} bytes", event.description, event.live),
            ))
        }));
        result
    }
}

/// A path's high-water mark, including the source that established it.
#[derive(Clone)]
pub(super) struct Peak {
    pub(super) bytes: u128,
    pub(super) span: Span,
    pub(super) costs: Vec<(Span, Footprint)>,
}

impl Peak {
    pub(super) fn merge(&mut self, other: &Self) {
        if other.bytes > self.bytes {
            self.bytes = other.bytes;
            self.span = other.span.clone();
        }
        // Cloned peaks share the same obligation expressions. Keep their common
        // history once when joining branches or adding a loop's iteration peak
        // to a checkpoint. A span can have multiple distinct charges, so span
        // identity alone is not enough to identify a shared obligation.
        let mut seen: HashSet<_> =
            self.costs.iter().map(|(span, cost)| (span.id, cost.identity())).collect();
        self.costs.extend(
            other
                .costs
                .iter()
                .filter(|(span, cost)| seen.insert((span.id, cost.identity())))
                .cloned(),
        );
    }
}

static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

#[derive(Clone, Default)]
pub(super) struct Live {
    fixed: std::collections::BTreeMap<MemoryKind, u64>,
    dynamic: HashMap<u64, Charge<Expr>>,
    values: HashMap<u64, Charge<u64>>,
    pub(super) inputs: HashSet<usize>,
}

#[derive(Clone)]
pub(super) struct Point {
    pub(super) cost: Footprint,
    pub(super) values: HashSet<u64>,
    pub(super) inputs: HashSet<usize>,
}

#[derive(Clone)]
pub(super) struct Accounting {
    paths: Vec<Live>,
    points: Vec<Point>,
    peak_costs: Vec<(Span, Footprint)>,
    peak_span: Span,
    report: MemoryReport,
}

impl Accounting {
    pub(super) fn new(span: &Span, budget: u64) -> Self {
        Self {
            paths: vec![Live::default()],
            points: Vec::new(),
            peak_costs: Vec::new(),
            peak_span: span.clone(),
            report: MemoryReport {
                peak: 0,
                budget,
                events: Vec::new(),
                conditional: false,
                cost_points: Vec::new(),
            },
        }
    }

    pub(super) fn points(&self) -> &[Point] {
        &self.points
    }
    pub(super) fn restore_live(&mut self, other: &Self) {
        self.paths = other.paths.clone();
    }
    pub(super) fn join_live(&mut self, other: &Self) -> Result<(), VirErr> {
        for path in &other.paths {
            if !self.paths.iter().any(|p| {
                p.fixed == path.fixed
                    && p.values == path.values
                    && p.inputs == path.inputs
                    && p.dynamic.len() == path.dynamic.len()
                    && p.dynamic.iter().all(|(id, e)| {
                        path.dynamic
                            .get(id)
                            .is_some_and(|v| e.kind == v.kind && Arc::ptr_eq(&e.amount, &v.amount))
                    })
            }) {
                if self.paths.len() >= 1024 {
                    return Err(unsupported(
                        &self.peak_span,
                        "more than 1024 distinct live ownership alternatives; divide the function into checked helpers",
                    ));
                }
                self.paths.push(path.clone());
            }
        }
        Ok(())
    }
    pub(super) fn add_input(&mut self, input: usize) {
        for path in &mut self.paths {
            path.inputs.insert(input);
        }
    }
    pub(super) fn release_input(&mut self, input: usize) {
        for path in &mut self.paths {
            path.inputs.remove(&input);
        }
    }
    pub(super) fn reserve_value(
        &mut self,
        span: &Span,
        kind: MemoryKind,
        bytes: u64,
    ) -> Result<u64, VirErr> {
        let id = self.reserve_value_unchecked(kind, bytes);
        self.record_live(span)?;
        Ok(id)
    }
    pub(super) fn reserve_value_unchecked(&mut self, kind: MemoryKind, bytes: u64) -> u64 {
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        for path in &mut self.paths {
            path.values.insert(id, Charge { kind: kind.clone(), amount: bytes });
        }
        id
    }
    pub(super) fn transfer_values(&mut self, ids: &HashSet<u64>, bytes: u64) -> u64 {
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        for path in &mut self.paths {
            let charge = ids.iter().find_map(|id| path.values.get(id)).cloned();
            for id in ids {
                path.values.remove(id);
            }
            if let Some(charge) = charge {
                assert_eq!(charge.amount, bytes, "moves preserve size");
                path.values.insert(id, charge);
            }
        }
        id
    }
    pub(super) fn release_values(&mut self, ids: &HashSet<u64>) {
        for path in &mut self.paths {
            for id in ids {
                path.values.remove(id);
            }
        }
    }
    pub(super) fn live(&self) -> u64 {
        self.paths
            .iter()
            .map(|p| {
                p.fixed.values().sum::<u64>() + p.values.values().map(|c| c.amount).sum::<u64>()
            })
            .max()
            .unwrap_or(0)
    }

    pub(super) fn peak(&self) -> Peak {
        Peak {
            bytes: self.report.peak,
            span: self.peak_span.clone(),
            costs: self.peak_costs.clone(),
        }
    }

    pub(super) fn set_peak(&mut self, peak: Peak) {
        self.peak_costs = peak.costs;
        self.report.peak = peak.bytes;
        self.peak_span = peak.span;
    }

    pub(super) fn record_live(&mut self, span: &Span) -> Result<(), VirErr> {
        for path in &self.paths {
            path.values
                .values()
                .map(|c| c.amount)
                .chain(path.fixed.values().copied())
                .try_fold(0u64, |a, b| a.checked_add(b))
                .ok_or_else(|| unsupported(span, "storage totals exceeding u64"))?;
        }
        let live = self.live();
        if u128::from(live) > self.report.peak {
            self.report.peak = live.into();
            self.peak_span = span.clone();
        }
        let paths = self.paths.clone();
        for path in paths {
            let cost = Self::path_expression(&path, span);
            self.record_point(span, cost, &path);
        }
        Ok(())
    }
    pub(super) fn reserve(
        &mut self,
        span: &Span,
        kind: MemoryKind,
        bytes: u64,
        reason: &str,
    ) -> Result<(), VirErr> {
        if bytes == 0 {
            return Ok(());
        }
        for path in &mut self.paths {
            let amount = path.fixed.entry(kind.clone()).or_default();
            *amount = amount
                .checked_add(bytes)
                .ok_or_else(|| unsupported(span, "storage totals exceeding u64"))?;
        }
        self.record_live(span)?;
        self.event(span, format!("reserve {bytes} bytes for {reason}"));
        Ok(())
    }
    fn path_expression(path: &Live, span: &Span) -> Footprint {
        let mut cost = Footprint::zero(span);
        let mut values = std::collections::BTreeMap::<MemoryKind, u64>::new();
        for charge in path.values.values() {
            *values.entry(charge.kind.clone()).or_default() += charge.amount;
        }
        for (kind, amount) in values {
            cost = cost.add(span, Footprint::charge(kind, contracts::literal(span, amount)));
        }
        for (kind, amount) in &path.fixed {
            cost =
                cost.add(span, Footprint::charge(kind.clone(), contracts::literal(span, *amount)));
        }
        for charge in path.dynamic.values() {
            cost = cost.add(span, Footprint::charge(charge.kind.clone(), charge.amount.clone()));
        }
        cost
    }
    pub(super) fn live_expression(&self, span: &Span) -> Footprint {
        self.paths
            .iter()
            .map(|p| Self::path_expression(p, span))
            .reduce(|a, b| a.maximum(span, b))
            .unwrap_or_else(|| Footprint::zero(span))
    }
    pub(super) fn reserve_dynamic(&mut self, span: &Span, kind: MemoryKind, cost: Expr) {
        for path in &mut self.paths {
            path.dynamic.insert(span.id, Charge { kind: kind.clone(), amount: cost.clone() });
        }
        self.record_live(span).expect("dynamic reservation preserves fixed storage");
    }
    pub(super) fn dynamic_cost(&self, span: &Span, id: u64) -> Expr {
        self.paths
            .iter()
            .filter_map(|p| p.dynamic.get(&id).map(|c| c.amount.clone()))
            .reduce(|a, b| contracts::maximum(span, a, b))
            .unwrap_or_else(|| contracts::literal(span, 0))
    }
    pub(super) fn release_dynamic(&mut self, id: u64) {
        for path in &mut self.paths {
            path.dynamic.remove(&id);
        }
    }
    fn record_point(&mut self, span: &Span, cost: Footprint, path: &Live) {
        self.report.cost_points.push((span.clone(), cost.clone()));
        self.peak_costs.push((span.clone(), cost.clone()));
        self.points.push(Point {
            cost,
            values: path.values.keys().copied().collect(),
            inputs: path.inputs.clone(),
        });
        self.report.conditional = true;
    }
    #[cfg(test)]
    pub(super) fn symbolic_cost(&mut self, span: &Span, cost: Expr) {
        for path in self.paths.clone() {
            self.record_point(span, Footprint::allowance(cost.clone()), &path);
        }
    }
    pub(super) fn call_cost(
        &mut self,
        span: &Span,
        cost: Footprint,
        excluded_inputs: &HashSet<usize>,
        result_ids: &HashSet<u64>,
        result_live: bool,
    ) {
        for mut path in self.paths.clone() {
            for input in excluded_inputs {
                path.inputs.remove(input);
            }
            if !result_live {
                for id in result_ids {
                    path.values.remove(id);
                }
            }
            self.record_point(span, cost.clone(), &path);
        }
    }
    /// Compose a section's unrestricted total allowance without assigning it
    /// a fictitious allocation kind or retaining it after the section exits.
    pub(super) fn section_allowance(&mut self, span: &Span, bytes: u64) -> Result<(), VirErr> {
        let live = self
            .live()
            .checked_add(bytes)
            .ok_or_else(|| unsupported(span, "storage totals exceeding u64"))?;
        if u128::from(live) > self.report.peak {
            self.report.peak = live.into();
            self.peak_span = span.clone();
        }
        for path in self.paths.clone() {
            let cost = Self::path_expression(&path, span)
                .add(span, Footprint::allowance(contracts::literal(span, bytes)));
            self.record_point(span, cost, &path);
        }
        Ok(())
    }
    pub(super) fn release(&mut self, span: &Span, kind: MemoryKind, bytes: u64, reason: &str) {
        if bytes == 0 {
            return;
        }
        for path in &mut self.paths {
            let amount = path.fixed.get_mut(&kind).expect("matching memory kind");
            *amount = amount.checked_sub(bytes).expect("balanced resource events");
            if *amount == 0 {
                path.fixed.remove(&kind);
            }
        }
        self.event(span, format!("release {bytes} bytes for {reason}"));
    }
    pub(super) fn event(&mut self, span: &Span, description: String) {
        self.report.events.push(MemoryEvent {
            span: span.clone(),
            description,
            live: self.live(),
            footprint: self.live_expression(span),
        });
    }

    pub(super) fn finish(self, function_span: &Span) -> MemoryReport {
        self.finish_scope(function_span, "function exit")
    }

    pub(super) fn finish_conditional(mut self) -> MemoryReport {
        self.paths.clear();
        self.report.conditional = true;
        self.report
    }

    pub(super) fn finish_section(self, section_span: &Span) -> MemoryReport {
        self.finish_scope(section_span, "section exit")
    }

    fn finish_scope(mut self, scope_span: &Span, exit: &str) -> MemoryReport {
        self.paths.clear();
        self.event(scope_span, exit.into());
        self.report
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> Span {
        Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "peak merge test".into(),
        }
    }

    #[test]
    fn repeated_branch_joins_keep_shared_cost_once() {
        let span = span();
        let mut storage = Accounting::new(&span, 100);
        storage.symbolic_cost(&span, super::super::contracts::literal(&span, 8));
        let mut peak = storage.peak();
        for _ in 0..64 {
            let sibling = peak.clone();
            peak.merge(&sibling);
            assert_eq!(peak.costs.len(), 1);
        }
    }

    #[test]
    fn overlapping_peaks_preserve_distinct_charges_at_the_same_span() {
        let span = span();
        let cost =
            |n| (span.clone(), Footprint::allowance(super::super::contracts::literal(&span, n)));
        let shared = cost(8);
        let left = cost(16);
        let right = cost(32);
        let mut peak =
            Peak { bytes: 16, span: span.clone(), costs: vec![shared.clone(), left.clone()] };
        let other =
            Peak { bytes: 32, span: span.clone(), costs: vec![shared.clone(), right.clone()] };
        peak.merge(&other);
        peak.merge(&other);
        assert_eq!(peak.bytes, 32);
        assert_eq!(peak.costs.len(), 3);
        for (actual, expected) in peak.costs.iter().zip([shared, left, right]) {
            assert_eq!(actual.0.id, expected.0.id);
            assert_eq!(actual.1.identity(), expected.1.identity());
        }
    }
    #[test]
    fn repeated_empty_branches_keep_one_live_state() {
        let span = span();
        let mut storage = Accounting::new(&span, 100);
        storage.reserve_value(&span, MemoryKind::host_local(), 24).unwrap();
        storage.reserve_dynamic(
            &span,
            MemoryKind::host_heap(),
            super::super::contracts::literal(&span, 16),
        );
        for _ in 0..64 {
            let sibling = storage.clone();
            storage.join_live(&sibling).unwrap();
            assert_eq!(storage.paths.len(), 1);
        }
    }

    #[test]
    fn joining_distinct_moves_preserves_each_remaining_value() {
        let span = span();
        let mut storage = Accounting::new(&span, 100);
        let a = storage.reserve_value(&span, MemoryKind::host_local(), 16).unwrap();
        let b = storage.reserve_value(&span, MemoryKind::host_local(), 16).unwrap();
        let mut sibling = storage.clone();
        storage.release_values(&[a].into_iter().collect());
        sibling.release_values(&[b].into_iter().collect());
        storage.join_live(&sibling).unwrap();
        assert_eq!(storage.paths.len(), 2);
        assert_eq!(storage.live(), 16);
        storage.release_values(&[a, b].into_iter().collect());
        assert_eq!(storage.live(), 0);
    }
    #[test]
    fn excessive_distinct_states_produce_a_diagnostic() {
        let span = span();
        let mut storage = Accounting::new(&span, 100);
        for _ in 1..1024 {
            let mut alternative = Accounting::new(&span, 100);
            alternative.reserve_value_unchecked(MemoryKind::host_local(), 1);
            storage.join_live(&alternative).unwrap();
        }
        let mut extra = Accounting::new(&span, 100);
        extra.reserve_value_unchecked(MemoryKind::host_local(), 1);
        assert!(storage.join_live(&extra).is_err());
        assert_eq!(storage.paths.len(), 1024);
    }
    fn selected(storage: &Accounting, selection: MemorySelection) -> u64 {
        contracts::constant(&storage.report.selected_peak(&span(), &selection)).unwrap()
    }

    #[test]
    fn sequential_kinds_reuse_total_budget() {
        let s = span();
        let mut storage = Accounting::new(&s, 100);
        storage.reserve(&s, MemoryKind::host_local(), 100, "local").unwrap();
        storage.release(&s, MemoryKind::host_local(), 100, "local");
        storage.reserve(&s, MemoryKind::host_heap(), 100, "heap").unwrap();
        assert_eq!(selected(&storage, MemorySelection::All), 100);
        assert_eq!(selected(&storage, MemorySelection::kind(MemoryKind::host_local())), 100);
        assert_eq!(selected(&storage, MemorySelection::kind(MemoryKind::host_heap())), 100);
    }

    #[test]
    fn equal_totals_in_different_kinds_remain_distinct_at_join() {
        let s = span();
        let gpu = MemoryKind::new("device.0.vram");
        let mut local = Accounting::new(&s, 100);
        local.reserve(&s, MemoryKind::host_local(), 64, "local").unwrap();
        let mut device = Accounting::new(&s, 100);
        device.reserve(&s, gpu.clone(), 64, "device").unwrap();
        local.join_live(&device).unwrap();
        assert_eq!(local.paths.len(), 2);
        let cost = local.live_expression(&s);
        assert_eq!(contracts::constant(&cost.total()), Some(64));
        assert_eq!(contracts::constant(&cost.select(&s, &MemorySelection::kind(gpu))), Some(64));
    }

    #[test]
    fn dynamic_device_charge_survives_value_move_and_releases_independently() {
        let s = span();
        let gpu = MemoryKind::new("device.1.vram");
        let mut storage = Accounting::new(&s, 100);
        let handle = storage.reserve_value(&s, MemoryKind::host_local(), 8).unwrap();
        storage.reserve_dynamic(&s, gpu.clone(), contracts::literal(&s, 64));
        let moved = storage.transfer_values(&[handle].into(), 8);
        storage.release_values(&[moved].into());
        let cost = storage.live_expression(&s);
        assert_eq!(contracts::constant(&cost.total()), Some(64));
        assert_eq!(contracts::constant(&cost.select(&s, &MemorySelection::kind(gpu))), Some(64));
        storage.release_dynamic(s.id);
        assert_eq!(contracts::constant(&storage.live_expression(&s).total()), Some(0));
    }

    #[test]
    fn section_allowance_is_unrestricted_and_does_not_remain_live() {
        let s = span();
        let mut storage = Accounting::new(&s, 100);
        storage.reserve_value(&s, MemoryKind::host_local(), 8).unwrap();
        storage.section_allowance(&s, 80).unwrap();
        assert_eq!(selected(&storage, MemorySelection::All), 88);
        assert_eq!(selected(&storage, MemorySelection::kind(MemoryKind::new("device.0.vram"))), 80);
        assert_eq!(storage.live(), 8);
    }
    #[test]
    fn moving_a_value_preserves_an_extension_kind() {
        let s = span();
        let gpu_stack = MemoryKind::new("device.0.local");
        let mut storage = Accounting::new(&s, 100);
        let value = storage.reserve_value(&s, gpu_stack.clone(), 16).unwrap();
        let moved = storage.transfer_values(&[value].into(), 16);
        let cost = storage.live_expression(&s);
        assert_eq!(
            contracts::constant(&cost.select(&s, &MemorySelection::kind(gpu_stack))),
            Some(16)
        );
        assert_eq!(
            contracts::constant(&cost.select(&s, &MemorySelection::kind(MemoryKind::host_local()))),
            Some(0)
        );
        storage.release_values(&[moved].into());
        assert_eq!(storage.live(), 0);
    }
}
