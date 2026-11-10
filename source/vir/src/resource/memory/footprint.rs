//! Memory kinds are model identities, independent of byte sizes and ownership.
//! Projections are evaluated at each accounting point before taking a peak.

use super::contracts;
use crate::ast::{Expr, VirErr};
use crate::messages::Span;
use std::collections::BTreeSet;
use std::sync::Arc;

/// Extensible, namespaced identity. Creating an identity does not authorize an
/// allocator: allocation semantics still have to be supplied by the model.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryKind(Arc<str>);

impl MemoryKind {
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self(name.into())
    }
    pub fn host_local() -> Self {
        Self::new("host.local")
    }
    pub fn host_heap() -> Self {
        Self::new("host.heap")
    }
    pub fn name(&self) -> &str {
        &self.0
    }
}

/// A set avoids counting a kind twice when selecting a group of resources.
#[derive(Clone, Debug)]
pub enum MemorySelection {
    All,
    Kinds(BTreeSet<MemoryKind>),
}

impl MemorySelection {
    pub fn kind(kind: MemoryKind) -> Self {
        Self::Kinds([kind].into())
    }
    fn contains(&self, kind: &MemoryKind) -> bool {
        match self {
            Self::All => true,
            Self::Kinds(kinds) => kinds.contains(kind),
        }
    }
    fn is_empty(&self) -> bool {
        matches!(self, Self::Kinds(kinds) if kinds.is_empty())
    }
}

/// A limit selects resources explicitly; its amount remains a scalar byte formula.
#[derive(Clone)]
pub struct MemoryBudget {
    pub selection: MemorySelection,
    pub amount: Expr,
}

impl MemoryBudget {
    pub fn total(amount: Expr) -> Self {
        Self { selection: MemorySelection::All, amount }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub(super) struct Charge<T> {
    pub kind: MemoryKind,
    pub amount: T,
}

/// Shared expression tree preserves correlations between kinds and branches.
/// `total` caches the existing scalar formula for ordinary memory contracts.
#[derive(Clone)]
pub struct Footprint {
    total: Expr,
    node: Arc<Node>,
}

#[derive(Clone)]
enum Node {
    Charge(MemoryKind, Expr),
    Allowance(Expr),
    Add(Footprint, Footprint),
    Remove(Footprint, MemoryKind, Expr),
    Maximum(Footprint, Footprint),
    Limit(Footprint, Expr),
}

impl Footprint {
    pub fn total(&self) -> Expr {
        self.total.clone()
    }
    pub(super) fn identity(&self) -> *const () {
        Arc::as_ptr(&self.node).cast()
    }
    pub(super) fn charge(kind: MemoryKind, amount: Expr) -> Self {
        Self { total: amount.clone(), node: Arc::new(Node::Charge(kind, amount)) }
    }
    /// An aggregate contract can spend its entire allowance in any kind. It
    /// must not be attributed to whichever kinds its current body happens to use.
    pub(super) fn allowance(amount: Expr) -> Self {
        Self { total: amount.clone(), node: Arc::new(Node::Allowance(amount)) }
    }
    pub(super) fn zero(span: &Span) -> Self {
        Self::charge(MemoryKind::host_local(), contracts::literal(span, 0))
    }
    pub(super) fn add(&self, span: &Span, other: Self) -> Self {
        Self {
            total: contracts::add(span, self.total(), other.total()),
            node: Arc::new(Node::Add(self.clone(), other)),
        }
    }
    /// Remove an exact, live charge, never an independently computed peak.
    pub(super) fn remove(&self, span: &Span, kind: MemoryKind, amount: Expr) -> Self {
        Self {
            total: contracts::subtract(span, self.total(), amount.clone()),
            node: Arc::new(Node::Remove(self.clone(), kind, amount)),
        }
    }
    pub(super) fn maximum(&self, span: &Span, other: Self) -> Self {
        Self {
            total: contracts::maximum(span, self.total(), other.total()),
            node: Arc::new(Node::Maximum(self.clone(), other)),
        }
    }
    pub(super) fn limit(&self, span: &Span, bound: Expr) -> Self {
        Self {
            total: contracts::minimum(span, self.total(), bound.clone()),
            node: Arc::new(Node::Limit(self.clone(), bound)),
        }
    }
    /// Upper bound on selected usage. Aggregate allowances are conservatively
    /// available to every nonempty selection; different projections need not add.
    pub fn select(&self, span: &Span, selection: &MemorySelection) -> Expr {
        if matches!(selection, MemorySelection::All) {
            return self.total();
        }
        if selection.is_empty() {
            return contracts::literal(span, 0);
        }
        match &*self.node {
            Node::Charge(kind, amount) => {
                if selection.contains(kind) {
                    amount.clone()
                } else {
                    contracts::literal(span, 0)
                }
            }
            Node::Allowance(amount) => amount.clone(),
            Node::Add(a, b) => {
                contracts::add(span, a.select(span, selection), b.select(span, selection))
            }
            Node::Remove(a, kind, amount) => {
                let cost = a.select(span, selection);
                if selection.contains(kind) {
                    contracts::subtract(span, cost, amount.clone())
                } else {
                    cost
                }
            }
            Node::Maximum(a, b) => {
                contracts::maximum(span, a.select(span, selection), b.select(span, selection))
            }
            Node::Limit(a, bound) => {
                contracts::minimum(span, a.select(span, selection), bound.clone())
            }
        }
    }
    pub(super) fn map(
        &self,
        span: &Span,
        f: &impl Fn(&Expr) -> Result<Expr, VirErr>,
    ) -> Result<Self, VirErr> {
        Ok(match &*self.node {
            Node::Charge(kind, amount) => Self::charge(kind.clone(), f(amount)?),
            Node::Allowance(amount) => Self::allowance(f(amount)?),
            Node::Add(a, b) => a.map(span, f)?.add(span, b.map(span, f)?),
            Node::Remove(a, kind, amount) => a.map(span, f)?.remove(span, kind.clone(), f(amount)?),
            Node::Maximum(a, b) => a.map(span, f)?.maximum(span, b.map(span, f)?),
            Node::Limit(a, bound) => a.map(span, f)?.limit(span, f(bound)?),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> Span {
        Span { raw_span: Arc::new(()), id: 1, data: Arc::new([]), as_string: "footprint".into() }
    }
    fn amount(cost: &Footprint, kind: MemorySelection) -> u64 {
        contracts::constant(&cost.select(&span(), &kind)).unwrap()
    }
    fn charge(kind: MemoryKind, n: u64) -> Footprint {
        Footprint::charge(kind, contracts::literal(&span(), n))
    }

    #[test]
    fn group_peak_preserves_correlation_and_deduplicates_kinds() {
        let s = span();
        let local = MemoryKind::host_local();
        let heap = MemoryKind::host_heap();
        let peak = charge(local.clone(), 100).maximum(&s, charge(heap.clone(), 100));
        assert_eq!(amount(&peak, MemorySelection::kind(local.clone())), 100);
        assert_eq!(amount(&peak, MemorySelection::kind(heap.clone())), 100);
        assert_eq!(amount(&peak, MemorySelection::Kinds([local.clone(), heap, local].into())), 100);
        assert_eq!(amount(&peak, MemorySelection::All), 100);
    }

    #[test]
    fn arbitrary_device_kinds_and_host_copy_overlap() {
        let s = span();
        let gpu0 = MemoryKind::new("device.0.vram");
        let gpu1 = MemoryKind::new("device.1.vram");
        let cost = charge(MemoryKind::host_heap(), 64).add(&s, charge(gpu0.clone(), 64));
        assert_eq!(amount(&cost, MemorySelection::All), 128);
        assert_eq!(amount(&cost, MemorySelection::kind(gpu0)), 64);
        assert_eq!(amount(&cost, MemorySelection::kind(gpu1)), 0);
    }

    #[test]
    fn total_allowance_cannot_be_assigned_to_current_implementation_kind() {
        let s = span();
        let allowance = Footprint::allowance(contracts::literal(&s, 100));
        let with_destination = charge(MemoryKind::host_local(), 8)
            .add(&s, allowance.remove(&s, MemoryKind::host_local(), contracts::literal(&s, 8)));
        assert_eq!(amount(&with_destination, MemorySelection::All), 100);
        assert_eq!(amount(&with_destination, MemorySelection::kind(MemoryKind::host_heap())), 100);
        assert_eq!(amount(&with_destination, MemorySelection::kind(MemoryKind::host_local())), 100);
        assert_eq!(amount(&with_destination, MemorySelection::Kinds(BTreeSet::new())), 0);
    }

    #[test]
    fn profile_mapping_and_bound_preserve_kind() {
        let s = span();
        let gpu = MemoryKind::new("device.0.vram");
        let cost = charge(gpu.clone(), 48).limit(&s, contracts::literal(&s, 32));
        let mapped = cost.map(&s, &|e| Ok(e.clone())).unwrap();
        assert_eq!(amount(&mapped, MemorySelection::kind(gpu)), 32);
        assert_eq!(amount(&mapped, MemorySelection::kind(MemoryKind::host_heap())), 0);
    }
}
