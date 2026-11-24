//! Checked live/peak accounting and source-located diagnostics.

use super::contracts;
use super::footprint::{Charge, Footprint, MemoryBudget, MemoryKind, MemorySelection};
use super::model::{MODEL_NAME, unsupported};
use super::synchronization::local::{Boundary, Condition};
use crate::ast::{Expr, VirErr, VirErrAs};
use crate::messages::{Span, note};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

mod calls;
mod holders;
mod intervals;
mod origins;
pub(super) use origins::ReturnedStorage;
mod sections;
mod transport;
pub(super) use transport::SharedBackingCharges;

#[derive(Clone, Copy)]
pub(super) enum CheckKind {
    Function,
    Section,
    Checkpoint,
    CurrentCheckpoint,
    WorkerState(&'static str),
}

#[derive(Clone)]
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
    /// This operation relies on verified worker bodies and their simultaneous byte bounds.
    pub covers_workers: bool,
    pub events: Vec<MemoryEvent>,
    pub(super) conditional: bool,
    /// Source observations shared by byte obligations, lifetime profiles and checked body effects.
    pub(super) points: Arc<Vec<Point>>,
    /// Separate actor ledgers with verified protocol witnesses. Reuse the
    /// checked effects when a developer requests a synchronization trace.
    pub(super) holder_effects: Vec<Arc<super::summary::BodyEffects>>,
}

impl MemoryReport {
    /// Project each simultaneous footprint before taking its peak. This also
    /// retains aggregate contract slack across calls and sections.
    pub fn selected_peak(&self, span: &Span, selection: &MemorySelection) -> Expr {
        self.points
            .iter()
            .map(|point| point.cost.select(span, selection))
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
        result.extend(self.synchronization_diagnostics());
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

/// A deferred allocation still has its original size on this accounting path.
/// Only the charge visible at a memory observation depends on outstanding aliases.
#[derive(Clone)]
struct DynamicCharge {
    kind: MemoryKind,
    amount: Expr,
    original: Option<Expr>,
    /// Source identities retained inside a conditionally charged shared backing.
    owned: origins::FixedOrigins,
}

impl DynamicCharge {
    fn new(kind: MemoryKind, amount: Expr) -> Self {
        Self { kind, amount, original: None, owned: Default::default() }
    }

    /// A branch join must preserve what a later collection can restore, even
    /// when two paths currently expose the same symbolic cost.
    fn same_state(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.owned == other.owned
            && Arc::ptr_eq(&self.amount, &other.amount)
            && self.original.as_ref().map(Arc::as_ptr) == other.original.as_ref().map(Arc::as_ptr)
    }

    fn defer(&mut self, span: &Span, empty: &Expr) {
        let conditional = super::growth::select(
            span,
            empty.clone(),
            contracts::literal(span, 0),
            self.amount.clone(),
        );
        self.original = Some(std::mem::replace(&mut self.amount, conditional));
    }
}

#[derive(Clone, Default)]
pub(super) struct Live {
    /// Entry acquisitions of the immediately enclosing independently contracted section.
    section_entry: Option<Arc<[super::synchronization::local::Interval]>>,
    owned: origins::FixedOrigins,
    fixed: std::collections::BTreeMap<MemoryKind, u64>,
    /// Allocation identity fixes symbolic addition order across verifier runs.
    /// Hash iteration changes SMT term shape and can amplify metadata matching.
    dynamic: std::collections::BTreeMap<u64, DynamicCharge>,
    values: HashMap<u64, Charge<u64>>,
    pub(super) inputs: HashSet<usize>,
    /// Acquisitions held by this actor on this particular execution path.
    held: std::collections::BTreeSet<super::synchronization::local::Interval>,
}

impl Live {
    /// Equal live ledgers preserve future destruction, inputs and held guards.
    /// Numeric equality alone cannot identify transported storage.
    fn same_state(&self, other: &Self) -> bool {
        self.section_entry == other.section_entry
            && self.fixed == other.fixed
            && self.owned == other.owned
            && self.values == other.values
            && self.inputs == other.inputs
            && self.held == other.held
            && self.dynamic.len() == other.dynamic.len()
            && self
                .dynamic
                .iter()
                .all(|(id, e)| other.dynamic.get(id).is_some_and(|v| e.same_state(v)))
    }

    /// Sections freeze dynamic byte terms at entry. Fixed charges and their
    /// symbolic addition order follow the ordinary path expression.
    fn footprint_with(
        &self,
        span: &Span,
        mut dynamic_amount: impl FnMut(&Expr) -> Expr,
    ) -> Footprint {
        let mut cost = Footprint::zero(span);
        let mut values = std::collections::BTreeMap::<MemoryKind, u64>::new();
        for charge in self.values.values() {
            *values.entry(charge.kind.clone()).or_default() += charge.amount;
        }
        for (kind, amount) in values {
            cost = cost.add(span, Footprint::charge(kind, contracts::literal(span, amount)));
        }
        for (kind, amount) in &self.fixed {
            cost =
                cost.add(span, Footprint::charge(kind.clone(), contracts::literal(span, *amount)));
        }
        for charge in self.dynamic.values() {
            cost = cost
                .add(span, Footprint::charge(charge.kind.clone(), dynamic_amount(&charge.amount)));
        }
        cost
    }

    fn add_fixed(&mut self, span: &Span, kind: &MemoryKind, bytes: u64) -> Result<(), VirErr> {
        let amount = self.fixed.entry(kind.clone()).or_default();
        *amount = amount
            .checked_add(bytes)
            .ok_or_else(|| unsupported(span, "storage totals exceeding u64"))?;
        Ok(())
    }

    fn remove_fixed(&mut self, kind: &MemoryKind, bytes: u64) {
        let amount = self.fixed.get_mut(kind).expect("matching memory kind");
        *amount = amount.checked_sub(bytes).expect("balanced resource events");
        if *amount == 0 {
            self.fixed.remove(kind);
        }
    }
}

#[derive(Clone)]
pub(super) struct Point {
    /// Call site and callee profile behind this composed observation. The callee
    /// keeps its own constructors, branches and loop binders in the checked graph.
    pub(super) call_point: Option<usize>,
    section_entry: Option<Arc<[super::synchronization::local::Interval]>>,
    pub(super) span: Span,
    pub(super) condition: Condition,
    pub(super) cost: Footprint,
    /// Owned witnesses still intact at this point in this actor.
    pub(super) holders: Vec<super::synchronization::holders::Witness>,
    /// Fixed heap constructors individually charged on this reaching path.
    pub(super) fixed_origins: std::collections::BTreeSet<origins::FixedOrigin>,
    /// Identified dynamic backing and aggregate-forest charges on this path.
    pub(super) allocations: std::collections::BTreeSet<u64>,
    pub(super) values: HashSet<u64>,
    pub(super) inputs: HashSet<usize>,
}

impl Point {
    /// Pair an observation's byte expression with the ownership and acquisitions
    /// of the same reaching path, including its enclosing section's entry state.
    fn from_live(span: &Span, cost: Footprint, path: &Live, boundary: Boundary) -> Self {
        Self {
            span: span.clone(),
            call_point: None,
            cost,
            condition: Condition { held: path.held.iter().copied().collect(), boundary },
            section_entry: path.section_entry.clone(),
            holders: Vec::new(),
            fixed_origins: path.fixed_origins(),
            allocations: path.dynamic.keys().copied().collect(),
            values: path.values.keys().copied().collect(),
            inputs: path.inputs.clone(),
        }
    }
}

#[derive(Clone)]
pub(super) struct Accounting {
    /// Whole-scope high water is independent of the history on continuing paths.
    /// Restoring a branch must not erase peaks on an edge that already exited.
    observed_peak: u128,
    paths: Vec<Live>,
    peak_costs: Vec<(Span, Footprint)>,
    peak_span: Span,
    report: MemoryReport,
}

impl Accounting {
    /// Snapshot surviving charges without copying a section's peak/proof history.
    pub(super) fn live_storage(&self) -> Vec<Live> {
        self.paths.clone()
    }

    /// Retire a ledger after its history has been composed separately.
    pub(super) fn into_live_storage(self) -> Vec<Live> {
        self.paths
    }

    pub(super) fn new(span: &Span, budget: u64) -> Self {
        Self {
            observed_peak: 0,
            paths: vec![Live::default()],
            peak_costs: Vec::new(),
            peak_span: span.clone(),
            report: MemoryReport {
                peak: 0,
                budget,
                covers_workers: false,
                events: Vec::new(),
                conditional: false,
                points: Arc::default(),
                holder_effects: Vec::new(),
            },
        }
    }

    /// Include all compatible worker phases in the originating caller observation.
    /// The coordinator still owns the completion tags and the canonical shared backing.
    pub(super) fn include_worker_costs(&mut self, additions: Vec<Option<Expr>>) {
        self.report.covers_workers = true;
        assert_eq!(self.report.points.len(), additions.len());
        for (point, extra) in Arc::make_mut(&mut self.report.points).iter_mut().zip(additions) {
            if let Some(extra) = extra {
                point.cost = point.cost.add(&point.span, Footprint::allowance(extra));
                if let Some(bytes) = contracts::constant(&point.cost.total()) {
                    self.report.peak = self.report.peak.max(u128::from(bytes));
                }
            }
        }
    }

    pub(super) fn points(&self) -> &[Point] {
        &self.report.points
    }
    pub(super) fn restore_live(&mut self, other: &Self) {
        self.paths = other.paths.clone();
    }
    /// A section may retain a result or compiler-scoped temporary beyond its boundary.
    /// Compose only live charges here; the section's history is represented in
    /// the parent by its declared allowance, just as on normal completion.
    pub(super) fn retain_section_storage(
        &mut self,
        other: &[Live],
        span: &Span,
    ) -> Result<(), VirErr> {
        let mut paths = Vec::new();
        for parent in &self.paths {
            for local in other {
                if local.section_entry.as_deref().is_some_and(|held| !parent.held.iter().eq(held)) {
                    continue;
                }
                let mut path = parent.clone();
                for (kind, amount) in &local.fixed {
                    let sum = path.fixed.entry(kind.clone()).or_default();
                    *sum = sum
                        .checked_add(*amount)
                        .ok_or_else(|| unsupported(span, "storage totals exceeding u64"))?;
                }
                path.owned.extend(&local.owned);
                path.held.clone_from(&local.held);
                path.dynamic.extend(local.dynamic.clone());
                path.values.extend(local.values.clone());
                path.inputs.extend(local.inputs.iter().copied());
                if paths.len() >= 1024 {
                    return Err(unsupported(
                        span,
                        "more than 1024 section-exit ownership alternatives",
                    ));
                }
                paths.push(path);
            }
        }
        self.paths = paths;
        Ok(())
    }

    /// A move from an enclosing region cannot transfer its inline charge until
    /// that region's ledger is restored. Reconnect missing result identities
    /// per path; locally charged alternatives already have their own identities.
    pub(super) fn resume_value(
        &mut self,
        span: &Span,
        ids: &HashSet<u64>,
        origins: &HashSet<u64>,
        bytes: u64,
    ) -> Result<Option<u64>, VirErr> {
        if bytes == 0 {
            return Ok(None);
        }
        let mut restored = None;
        for path in &mut self.paths {
            if ids.iter().any(|id| path.values.contains_key(id)) {
                continue;
            }
            let source =
                origins.iter().find(|id| path.values.contains_key(id)).copied().ok_or_else(
                    || unsupported(span, "a section exit value without a charged source lifetime"),
                )?;
            let charge = path.values.remove(&source).unwrap();
            assert_eq!(charge.amount, bytes, "moves preserve size");
            let id = *restored
                .get_or_insert_with(|| NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
            path.values.insert(id, charge);
        }
        Ok(restored)
    }
    pub(super) fn join_live(&mut self, other: &Self) -> Result<(), VirErr> {
        for path in &other.paths {
            if !self.paths.iter().any(|other| other.same_state(path)) {
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

    /// Pack disjoint field lifetimes into one aggregate without creating another
    /// inline charge. Alternatives within a field are distinct from simultaneous
    /// fields: each reachable path contributes that field's storage exactly once.
    pub(super) fn pack_values(&mut self, fields: &[(&HashSet<u64>, u64)], bytes: u64) -> u64 {
        let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        for path in &mut self.paths {
            let mut amount = 0u64;
            let mut seen = HashSet::new();
            for (ids, expected) in fields {
                let live: Vec<_> =
                    ids.iter().filter_map(|id| path.values.get(id).map(|c| (*id, c))).collect();
                assert!(
                    live.len() == 1 || (*expected == 0 && live.is_empty()),
                    "one inline lifetime per captured field and path"
                );
                for (source, charge) in live {
                    assert!(seen.insert(source), "capture fields are disjoint");
                    assert_eq!(charge.kind, MemoryKind::host_local());
                    assert_eq!(charge.amount, *expected);
                    amount = amount.checked_add(charge.amount).expect("validated capture layout");
                }
            }
            assert_eq!(amount, bytes, "capture packing preserves storage");
            for source in seen {
                path.values.remove(&source);
            }
            path.values.insert(id, Charge { kind: MemoryKind::host_local(), amount });
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
        self.observed_peak = self.observed_peak.max(u128::from(live));
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
            path.add_fixed(span, &kind, bytes)?;
        }
        self.record_live(span)?;
        self.event(span, format!("reserve {bytes} bytes for {reason}"));
        Ok(())
    }
    fn path_expression(path: &Live, span: &Span) -> Footprint {
        path.footprint_with(span, Clone::clone)
    }
    pub(super) fn live_expression(&self, span: &Span) -> Footprint {
        self.paths
            .iter()
            .map(|p| Self::path_expression(p, span))
            .reduce(|a, b| a.maximum(span, b))
            .unwrap_or_else(|| Footprint::zero(span))
    }
    /// Allocation identities use a separate range from source AST span IDs.
    pub(super) fn fresh_allocation() -> u64 {
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed) | (1u64 << 63)
    }
    /// Install a symbolic live charge without creating a new peak observation.
    pub(super) fn set_allocation(&mut self, id: u64, kind: MemoryKind, cost: Expr) {
        for path in &mut self.paths {
            path.dynamic.insert(id, DynamicCharge::new(kind.clone(), cost.clone()));
        }
    }
    pub(super) fn reserve_dynamic(&mut self, span: &Span, kind: MemoryKind, cost: Expr) {
        for path in &mut self.paths {
            path.dynamic.insert(span.id, DynamicCharge::new(kind.clone(), cost.clone()));
        }
        self.record_live(span).expect("dynamic reservation preserves fixed storage");
    }
    pub(super) fn contains_allocation(&self, id: u64) -> bool {
        self.paths.iter().all(|path| path.dynamic.contains_key(&id))
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
        self.record_phase(span, cost, path, Boundary::Live);
    }

    fn record_phase(&mut self, span: &Span, cost: Footprint, path: &Live, boundary: Boundary) {
        self.peak_costs.push((span.clone(), cost.clone()));
        Arc::make_mut(&mut self.report.points).push(Point::from_live(span, cost, path, boundary));
        self.report.conditional = true;
    }
    #[cfg(test)]
    pub(super) fn symbolic_cost(&mut self, span: &Span, cost: Expr) {
        for path in self.paths.clone() {
            self.record_point(span, Footprint::allowance(cost.clone()), &path);
        }
    }
    /// Evaluate the committed descriptor updates on each reaching path, keeping
    /// its byte expression paired with the acquisitions held on that path.
    pub(super) fn record_call_exit(&mut self, span: &Span, growth: &super::growth::Growth) {
        for path in self.paths.clone() {
            let cost = path.footprint_with(span, |amount| growth.after_value(span, amount));
            self.record_point(span, cost, &path);
        }
    }
    /// Compose a section's unrestricted total allowance without assigning it
    /// a fictitious allocation kind or retaining it after the section exits.
    pub(super) fn section_allowance(&mut self, span: &Span, allowance: Expr) -> Result<(), VirErr> {
        if let Some(bytes) = contracts::constant(&allowance) {
            let live = self
                .live()
                .checked_add(bytes)
                .ok_or_else(|| unsupported(span, "storage totals exceeding u64"))?;
            if u128::from(live) > self.report.peak {
                self.report.peak = live.into();
                self.peak_span = span.clone();
            }
        }
        for path in self.paths.clone() {
            let cost = Self::path_expression(&path, span)
                .add(span, Footprint::allowance(allowance.clone()));
            self.record_point(span, cost, &path);
        }
        Ok(())
    }
    pub(super) fn release(&mut self, span: &Span, kind: MemoryKind, bytes: u64, reason: &str) {
        if bytes == 0 {
            return;
        }
        for path in &mut self.paths {
            path.remove_fixed(&kind, bytes);
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
        self.report.peak = self.report.peak.max(self.observed_peak);
        self.paths.clear();
        self.report.conditional = true;
        self.report
    }

    pub(super) fn finish_section(self, section_span: &Span) -> MemoryReport {
        self.finish_scope(section_span, "section exit")
    }

    fn finish_scope(mut self, scope_span: &Span, exit: &str) -> MemoryReport {
        self.report.peak = self.report.peak.max(self.observed_peak);
        self.paths.clear();
        self.event(scope_span, exit.into());
        self.report
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ExprX, VarIdent, VarIdentDisambiguate};

    fn span() -> Span {
        Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "peak merge test".into(),
        }
    }

    #[test]
    fn symbolic_totals_are_stable_across_allocation_insertion_orders() {
        let span = span();
        let total = |offset: u64| {
            let mut live = Live::default();
            for step in 0..8 {
                let id = (step + offset) % 8;
                let name = VarIdent(
                    Arc::new(format!("allocation_{id}")),
                    VarIdentDisambiguate::VirTemp(id),
                );
                let (amount, _) = super::super::symbolic::integer_local(&span, name);
                live.dynamic.insert(id, DynamicCharge::new(MemoryKind::host_heap(), amount));
            }
            Accounting::path_expression(&live, &span).total()
        };
        let expected = total(0);
        for offset in 1..8 {
            assert!(super::super::transfer::simplify::inspect::same_expression(
                &expected,
                &total(offset),
            ));
        }
        let mut allocations = 0;
        crate::ast_visitor::expr_visitor_check(&expected, &mut |_, value| {
            allocations += usize::from(matches!(&value.x, ExprX::Var(_)));
            Ok::<(), VirErr>(())
        })
        .unwrap();
        assert_eq!(allocations, 8);
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
            assert_eq!(contracts::constant(&storage.live_expression(&span).total()), Some(40));
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
    fn packing_fields_preserves_simultaneous_storage_and_branch_alternatives() {
        let span = span();
        let mut storage = Accounting::new(&span, 20);
        let first = storage.reserve_value(&span, MemoryKind::host_local(), 8).unwrap();
        let second = storage.reserve_value(&span, MemoryKind::host_local(), 12).unwrap();
        let mut sibling = storage.clone();
        sibling.release_values(&[first].into());
        let alternative = sibling.reserve_value(&span, MemoryKind::host_local(), 8).unwrap();
        storage.join_live(&sibling).unwrap();
        let packed =
            storage.pack_values(&[(&[first, alternative].into(), 8), (&[second].into(), 12)], 20);
        assert_eq!(storage.live(), 20);
        assert_eq!(selected(&storage, MemorySelection::All), 20);
        // The old field identities no longer own inline storage on either path.
        storage.release_values(&[first, alternative, second].into());
        assert_eq!(storage.live(), 20);
        storage.release_values(&[packed].into());
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
        let error = storage.join_live(&extra).unwrap_err();
        assert!(error.note.contains("more than 1024 distinct live ownership alternatives"));
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
        storage.section_allowance(&s, contracts::literal(&s, 80)).unwrap();
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
