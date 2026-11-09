//! Container-independent allocation sizes, transfers, and retained effects.
//!
//! Sizes are byte expressions tagged with their memory kind. Container adapters
//! supply these expressions; call composition never reconstructs them from a
//! return type or treats a reservation in elements as a byte count.

use super::accounting::Accounting;
use super::contracts;
use super::footprint::{Charge, MemoryKind};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

/// The ownership tree surviving in a result. Input indices identify
/// provenance, so forwarding retains the caller's allocation identity.
#[derive(Clone)]
pub(super) enum ReturnedOwner {
    /// Transfer an input subtree, applying replacements at relative child paths.
    Input {
        /// Parameter whose entire subtree survives in the result.
        index: usize,
        /// Possible replacement sizes; original allocations may remain larger.
        replacements: std::collections::BTreeMap<super::heap::OwnerPath, Charge<Expr>>,
    },
    /// Compose newly owned storage and child owners. Struct nodes have no allocation.
    Node {
        /// Only this node's allocation; excludes allocations owned by children.
        allocation: Option<Charge<Expr>>,
        /// Fixed child owners, each accounting for its own allocations.
        children: std::collections::BTreeMap<super::heap::OwnerSlot, ReturnedOwner>,
    },
    /// A fresh allocation whose growth requires a conservative byte bound.
    Replaced { allocation: Charge<Expr> },
}

/// Allocation effects established by a checked function body. Temporary peaks
/// remain in its lifetime profiles; these describe only storage surviving a call.
#[derive(Clone)]
pub(super) struct AllocationSummary {
    /// Ownership and byte-size effects of the returned value.
    pub(super) returned: Option<ReturnedOwner>,
    /// Replacement bounds retained through borrowed inputs, keyed by parameter and child path.
    pub(super) retained: HashMap<super::paths::InputPath, Charge<Expr>>,
}

/// Erased byte state for an allocation whose size may change. Container-specific
/// facts such as element capacity do not belong to this state.
#[derive(Clone)]
pub(super) struct RetainedAllocation {
    /// Stable charge identity across moves and branches.
    pub(super) id: u64,
    /// Address space of both the retained allocation and its replacements.
    pub(super) kind: MemoryKind,
    /// Constructor charge, or zero for a caller-supplied allocation.
    pub(super) initial_bytes: Expr,
    /// Proof local bounding the bytes currently retained in this function.
    pub(super) bytes: Expr,
    /// Snapshot committed only after the executable operation.
    pub(super) next_bytes: Expr,
    /// Inline parameter storage that stays live while this incoming allocation
    /// can grow. None marks a locally created allocation. This is a layout size,
    /// not the size of the original backing allocation retained by the caller.
    pub(super) input_bytes: Option<u64>,
    /// Whether the body can replace this allocation.
    pub(super) changed: bool,
    /// Helper-provided byte bounds used in checked loop invariants.
    pub(super) floor: Expr,
}

impl RetainedAllocation {
    /// Schedule a possible replacement's retained effect. The operation's peak
    /// was accounted separately; committing these statements must follow it.
    pub(super) fn retain(
        &mut self,
        span: &Span,
        replacement: &Charge<Expr>,
    ) -> Result<Option<(Stmt, Stmt)>, VirErr> {
        if self.kind != replacement.kind {
            return Err(super::model::unsupported(span, "changing an allocation's memory kind"));
        }
        if contracts::constant(&replacement.amount) == Some(0) {
            return Ok(None);
        }
        let upper = retained_bytes(span, self.bytes.clone(), replacement.amount.clone());
        let snapshot = super::symbolic::assign(span, &self.next_bytes, upper);
        let commit = super::symbolic::assign(span, &self.bytes, self.next_bytes.clone());
        self.floor = contracts::maximum(span, self.floor.clone(), replacement.amount.clone());
        self.changed = true;
        Ok(Some((snapshot, commit)))
    }
}

/// Specialize a byte expression without changing its memory kind.
pub(super) fn instantiate(
    allocation: &Charge<Expr>,
    function: &Function,
    args: &Exprs,
    allowed: &HashSet<VarIdent>,
) -> Result<Charge<Expr>, VirErr> {
    Ok(Charge {
        kind: allocation.kind.clone(),
        amount: contracts::substitute(&allocation.amount, function, args, allowed)?,
    })
}

/// After a possible replacement, either the old allocation or the new one
/// survives. Their sum belongs only to the temporary overlap at the operation.
pub(super) fn retained_bytes(span: &Span, previous: Expr, replacement: Expr) -> Expr {
    contracts::maximum(span, previous, replacement)
}

impl Accounting {
    /// Observe replacement storage while the old allocation is still live,
    /// then remove only the temporary charge. Retained state commits separately.
    pub(super) fn replacement_peak(
        &mut self,
        span: &Span,
        replacement: &Charge<Expr>,
    ) -> Result<(), VirErr> {
        let temporary = Self::fresh_allocation();
        self.set_allocation(temporary, replacement.kind.clone(), replacement.amount.clone());
        let result = self.record_live(span);
        self.release_dynamic(temporary);
        result
    }
}

impl super::analysis::Analysis<'_> {
    /// Freeze a runtime byte extent before its source value is consumed. Later
    /// accounting refers to the snapshot, never to a moved or mutated receiver.
    pub(super) fn allocation_snapshot(&mut self, span: &Span, amount: Expr) -> Expr {
        let name = VarIdent(
            std::sync::Arc::new("$memory_extent".into()),
            VarIdentDisambiguate::VirTemp(Accounting::fresh_allocation()),
        );
        let (value, declaration) = super::symbolic::integer_local(span, name);
        self.growth.declarations.push(declaration);
        self.growth
            .before
            .entry(span.id)
            .or_default()
            .push(super::symbolic::assign(span, &value, amount));
        value
    }
}

#[cfg(test)]
mod tests {
    use super::super::footprint::MemorySelection;
    use super::*;
    use std::sync::Arc;

    fn span() -> Span {
        Span { raw_span: Arc::new(()), id: 1, data: Arc::new([]), as_string: "allocations".into() }
    }

    #[test]
    fn replacement_overlap_preserves_kind_and_releases_only_temporary_storage() {
        let s = span();
        let device = MemoryKind::new("device.0.vram");
        let mut storage = Accounting::new(&s, 100);
        storage.reserve(&s, MemoryKind::host_local(), 8, "handle").unwrap();
        let old = Accounting::fresh_allocation();
        storage.set_allocation(old, device.clone(), contracts::literal(&s, 16));
        storage
            .replacement_peak(
                &s,
                &Charge { kind: device.clone(), amount: contracts::literal(&s, 32) },
            )
            .unwrap();
        let overlap = &storage.points().last().unwrap().cost;
        assert_eq!(contracts::constant(&overlap.total()), Some(56));
        assert_eq!(
            contracts::constant(&overlap.select(&s, &MemorySelection::kind(device.clone()))),
            Some(48)
        );
        assert_eq!(
            contracts::constant(
                &overlap.select(&s, &MemorySelection::kind(MemoryKind::host_heap()))
            ),
            Some(0)
        );
        assert_eq!(contracts::constant(&storage.live_expression(&s).total()), Some(24));
        storage.set_allocation(
            old,
            device,
            retained_bytes(&s, contracts::literal(&s, 16), contracts::literal(&s, 32)),
        );
        assert_eq!(contracts::constant(&storage.live_expression(&s).total()), Some(40));
        storage.release_dynamic(old);
        assert_eq!(contracts::constant(&storage.live_expression(&s).total()), Some(8));
    }

    #[test]
    fn smaller_replacement_bound_cannot_erase_the_original_charge() {
        let s = span();
        assert_eq!(
            contracts::constant(&retained_bytes(
                &s,
                contracts::literal(&s, 64),
                contracts::literal(&s, 16)
            )),
            Some(64)
        );
        assert_eq!(
            contracts::constant(&retained_bytes(
                &s,
                contracts::literal(&s, 64),
                contracts::literal(&s, 0)
            )),
            Some(64)
        );
    }

    #[test]
    fn retained_effect_cannot_silently_reclassify_memory() {
        let s = span();
        let zero = contracts::literal(&s, 0);
        let mut allocation = RetainedAllocation {
            id: 7,
            kind: MemoryKind::new("device.0.vram"),
            initial_bytes: zero.clone(),
            bytes: zero.clone(),
            next_bytes: zero.clone(),
            input_bytes: Some(8),
            changed: false,
            floor: zero,
        };
        let replacement =
            Charge { kind: MemoryKind::host_heap(), amount: contracts::literal(&s, 32) };
        assert!(allocation.retain(&s, &replacement).is_err());
        assert!(!allocation.changed);
        assert_eq!(contracts::constant(&allocation.floor), Some(0));
    }
}
