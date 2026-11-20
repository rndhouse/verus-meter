//! Move charged storage between actors without executing a destructor or adding
//! their histories together. Publication and collection use the same operation.

use super::{Accounting, Charge, DynamicCharge, Live, MemoryKind, contracts};
use crate::resource::memory::{
    elements::{ElementState, References},
    growth::Growth,
    heap::Owner,
    lifetime::Storage,
    model::unsupported,
};
use crate::{
    ast::{Expr, VirErr},
    messages::Span,
};
use std::collections::{BTreeMap, BTreeSet};

/// The charged allocations reached by following uniquely owned children.
#[derive(Default)]
pub(super) struct Allocations {
    pub(super) roles: BTreeMap<MemoryKind, BTreeSet<u64>>,
    pub(super) fixed: BTreeMap<MemoryKind, u64>,
    pub(super) dynamic: BTreeSet<u64>,
}

impl Allocations {
    pub(super) fn owned(
        owner: Option<&Owner>,
        element_states: &[ElementState],
        span: &Span,
    ) -> Result<Self, VirErr> {
        let mut allocations = Self::default();
        let mut duplicate = false;
        if let Some(owner) = owner {
            owner.visit(&mut |node| {
                if let Some(role) = node.fixed_role {
                    duplicate |=
                        !allocations.roles.entry(node.kind.clone()).or_default().insert(role);
                }
                if node.bytes != 0 {
                    let bytes = allocations.fixed.entry(node.kind.clone()).or_default();
                    *bytes = bytes.checked_add(node.bytes).expect("live storage fits the model");
                }
                if let Some(id) = node.dynamic {
                    duplicate |= !allocations.dynamic.insert(id);
                }
                if let Some(elements) = &node.elements {
                    for state in elements.states.values() {
                        duplicate |= !allocations.dynamic.insert(element_states[*state].id);
                    }
                }
            });
        }
        if duplicate {
            return Err(unsupported(span, "duplicate allocation identities in owned storage"));
        }
        Ok(allocations)
    }
}

/// Byte-only immutable backing for a canonical shared root. Fixed totals need
/// identities while conditional. Symbolic allocations keep their original IDs.
pub(in super::super) struct SharedBackingCharges {
    roles: BTreeMap<MemoryKind, BTreeSet<u64>>,
    fixed: Vec<(u64, Charge<u64>)>,
    dynamic: BTreeSet<u64>,
}

impl SharedBackingCharges {
    /// Only a complete tree of local byte charges can substitute for a payload.
    /// Incoming regions and strong or worker links need the original destructor.
    pub(in super::super) fn for_payload(
        owner: &Owner,
        element_states: &[ElementState],
        span: &Span,
    ) -> Result<Option<Self>, VirErr> {
        if !owner.complete() || !owner.inputs().is_empty() || owner.references() != References::None
        {
            return Ok(None);
        }
        let Allocations { fixed, dynamic, roles } =
            Allocations::owned(Some(owner), element_states, span)?;
        let fixed = fixed
            .into_iter()
            .map(|(kind, amount)| (Accounting::fresh_allocation(), Charge { kind, amount }))
            .collect();
        Ok(Some(Self { fixed, dynamic, roles }))
    }

    /// A path can only defer an allocation it currently owns. Check every
    /// component before changing the ledger, including on section boundaries.
    pub(in super::super) fn defer(
        &self,
        storage: &mut Accounting,
        empty: Expr,
        span: &Span,
    ) -> bool {
        for path in &storage.paths {
            if self.roles.values().flatten().any(|role| !path.owned.contains_key(role))
                || self.fixed.iter().any(|(id, c)| {
                    path.dynamic.contains_key(id)
                        || path.fixed.get(&c.kind).copied().unwrap_or(0) < c.amount
                })
                || self
                    .dynamic
                    .iter()
                    .any(|id| path.dynamic.get(id).is_none_or(|c| c.original.is_some()))
            {
                return false;
            }
        }
        for path in &mut storage.paths {
            for (id, c) in &self.fixed {
                path.remove_fixed(&c.kind, c.amount);
                let mut charge =
                    DynamicCharge::new(c.kind.clone(), contracts::literal(span, c.amount));
                for role in self.roles.get(&c.kind).into_iter().flatten() {
                    charge
                        .owned
                        .insert(*role, path.owned.remove(role).expect("validated backing role"));
                }
                charge.defer(span, &empty);
                path.dynamic.insert(*id, charge);
            }
            for id in &self.dynamic {
                path.dynamic.get_mut(id).unwrap().defer(span, &empty);
            }
        }
        true
    }

    pub(in super::super) fn receive(
        &self,
        storage: &mut Accounting,
        span: &Span,
    ) -> Result<(), VirErr> {
        for path in &mut storage.paths {
            let missing =
                || unsupported(span, "an indexed Arc result without its retained backing charge");
            for (id, c) in &self.fixed {
                let saved = path.dynamic.remove(id).ok_or_else(missing)?;
                saved.original.ok_or_else(missing)?;
                path.owned.extend(saved.owned);
                path.add_fixed(span, &c.kind, c.amount)?;
            }
            for id in &self.dynamic {
                let charge = path.dynamic.get_mut(id).ok_or_else(missing)?;
                charge.amount = charge.original.take().ok_or_else(missing)?;
            }
        }
        storage.record_live(span)
    }
}

impl Accounting {
    /// A completed body must have transferred or released every charge. A
    /// missing descriptor cannot silently turn live storage into zero bytes.
    pub(in super::super) fn check_transferred(&self, span: &Span) -> Result<(), VirErr> {
        if !self.only_frame_storage(&Default::default(), &Default::default()) {
            return Err(unsupported(
                span,
                "worker completion with storage absent from its result descriptor",
            ));
        }
        Ok(())
    }

    /// At a closed consumer's exit only scalar frame slots and input regions
    /// conservatively kept with their caller may remain.
    pub(in super::super) fn only_frame_storage(
        &self,
        slots: &std::collections::HashSet<u64>,
        inputs: &std::collections::HashSet<usize>,
    ) -> bool {
        self.paths.iter().all(|path| {
            path.fixed.values().all(|bytes| *bytes == 0)
                && path.owned.is_empty()
                && path.dynamic.is_empty()
                && path.held.is_empty()
                && path.values.iter().all(|(id, charge)| charge.amount == 0 || slots.contains(id))
                && path.inputs.is_subset(inputs)
        })
    }

    /// Detach precisely the supplied value and its uniquely owned descendants.
    /// Canonical shared backing stays in its enclosing domain; a handle carries
    /// only its identity. The source keeps its earlier peak observations.
    pub(in super::super) fn take_storage(
        &mut self,
        storage: &Storage,
        growth: &Growth,
        span: &Span,
    ) -> Result<Self, VirErr> {
        let Allocations { fixed, dynamic, roles } =
            Allocations::owned(storage.owner.as_ref(), &growth.elements, span)?;
        let inputs = storage.owner.as_ref().map(Owner::inputs).unwrap_or_default();
        let mut remaining = self.paths.clone();
        let mut transferred = Vec::new();
        for path in &mut remaining {
            let mut selected = Live::default();
            for role in roles.values().flatten() {
                let origin = path.owned.remove(role).ok_or_else(|| {
                    unsupported(span, "actor transport without its fixed allocation origin")
                })?;
                selected.owned.insert(*role, origin);
            }
            for (kind, bytes) in &fixed {
                let total = path.fixed.entry(kind.clone()).or_default();
                *total = total.checked_sub(*bytes).ok_or_else(|| {
                    unsupported(span, "actor transport without its charged allocation")
                })?;
                selected.fixed.insert(kind.clone(), *bytes);
            }
            for id in &dynamic {
                let charge = path.dynamic.remove(id).ok_or_else(|| {
                    unsupported(span, "actor transport without its symbolic allocation")
                })?;
                if charge.original.is_some() {
                    return Err(unsupported(
                        span,
                        "actor transport of backing reserved by outstanding shared aliases",
                    ));
                }
                selected.dynamic.insert(*id, charge);
            }
            for id in &storage.value.ids {
                if let Some(charge) = path.values.remove(id) {
                    selected.values.insert(*id, charge);
                }
            }
            let bytes: u64 = selected.values.values().map(|charge| charge.amount).sum();
            if bytes != storage.value.bytes || selected.values.len() > 1 {
                return Err(unsupported(
                    span,
                    "actor transport without one complete value lifetime",
                ));
            }
            for id in &inputs {
                if path.inputs.remove(id) {
                    selected.inputs.insert(*id);
                }
            }
            transferred.push(selected);
        }
        let mut target = Self::new(span, self.report.budget);
        target.paths = transferred;
        target.record_live(span)?;
        self.paths = remaining;
        Ok(target)
    }

    /// Receive live storage only. Another actor's ordered execution and peaks
    /// remain in its summary, never spliced into this actor's execution history.
    pub(in super::super) fn receive_storage(
        &mut self,
        source: Self,
        span: &Span,
    ) -> Result<(), VirErr> {
        if self.paths.len().saturating_mul(source.paths.len()) > 1024 {
            return Err(unsupported(span, "more than 1024 actor storage alternatives"));
        }
        let mut paths = Vec::new();
        for current in &self.paths {
            for incoming in &source.paths {
                if incoming.owned.keys().any(|role| current.owned.contains_key(role))
                    || incoming.values.keys().any(|id| current.values.contains_key(id))
                    || incoming.dynamic.keys().any(|id| current.dynamic.contains_key(id))
                    || !incoming.inputs.is_disjoint(&current.inputs)
                {
                    return Err(unsupported(span, "duplicate ownership at actor collection"));
                }
                let mut path = current.clone();
                for (kind, bytes) in &incoming.fixed {
                    let total = path.fixed.entry(kind.clone()).or_default();
                    *total = total.checked_add(*bytes).ok_or_else(|| {
                        unsupported(span, "collected storage exceeding the model range")
                    })?;
                }
                path.owned.extend(&incoming.owned);
                path.dynamic.extend(incoming.dynamic.clone());
                path.values.extend(incoming.values.clone());
                path.inputs.extend(&incoming.inputs);
                paths.push(path);
            }
        }
        self.paths = paths;
        self.record_live(span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resource::memory::{contracts, footprint::MemoryKind, heap::Owner, lifetime::Value};

    fn span(id: u64) -> Span {
        Span {
            raw_span: std::sync::Arc::new(()),
            id,
            data: std::sync::Arc::new([]),
            as_string: "actor transport".into(),
        }
    }

    fn live(storage: &Accounting) -> u64 {
        contracts::constant(&storage.live_expression(&span(0)).total()).unwrap()
    }

    fn peak(storage: &Accounting) -> u64 {
        storage
            .peak()
            .costs
            .iter()
            .map(|(_, cost)| contracts::constant(&cost.total()).unwrap())
            .max()
            .unwrap_or(0)
    }

    #[test]
    fn transfer_preserves_charges_and_keeps_actor_histories_separate() {
        let site = span(1);
        let mut caller = Accounting::new(&site, 1024);
        let inline = caller.reserve_value(&site, MemoryKind::host_local(), 8).unwrap();
        let fixed_role =
            caller.reserve_owned(&site, MemoryKind::host_heap(), 32, "owned buffer").unwrap();
        let allocation = Accounting::fresh_allocation();
        caller.set_allocation(allocation, MemoryKind::host_heap(), contracts::literal(&site, 16));
        caller.record_live(&site).unwrap();
        let storage = Storage {
            typ: crate::ast_util::unit_typ(),
            value: Value {
                bytes: 8,
                ids: [inline].into(),
                origins: [inline].into(),
                ..Value::unit()
            },
            owner: Some(Owner {
                bytes: 32,
                fixed_role,
                dynamic: Some(allocation),
                ..Default::default()
            }),
        };
        let mut worker = caller.take_storage(&storage, &Growth::default(), &span(2)).unwrap();
        assert_eq!(live(&caller), 0);
        assert_eq!(live(&worker), 56);
        let origin = *worker.paths[0].owned.values().next().unwrap();
        assert_eq!(origin.identity, fixed_role.unwrap());
        assert_eq!(origin.site, site.id);
        assert!(caller.paths[0].owned.is_empty());
        worker.reserve(&span(3), MemoryKind::host_heap(), 80, "worker scratch").unwrap();
        worker.release(&span(4), MemoryKind::host_heap(), 80, "worker scratch");
        assert_eq!(peak(&caller), 56);
        assert_eq!(peak(&worker), 136);
        let outgoing = worker.take_storage(&storage, &Growth::default(), &span(5)).unwrap();
        worker.check_transferred(&span(5)).unwrap();
        caller.receive_storage(outgoing.clone(), &span(6)).unwrap();
        assert_eq!(live(&caller), 56);
        assert_eq!(peak(&caller), 56);
        assert_eq!(caller.paths[0].owned[&fixed_role.unwrap()].identity, origin.identity);
        assert!(caller.receive_storage(outgoing, &span(7)).is_err());
        assert_eq!(live(&caller), 56);
    }

    #[test]
    fn a_returned_alias_restores_each_paths_own_payload_charges() {
        use crate::resource::memory::heap::OwnerSlot;
        let site = span(1);
        let allocation = Accounting::fresh_allocation();
        let payload_kind = MemoryKind::new("device.buffer");
        let mut storage = Accounting::new(&site, 256);
        let role =
            storage.reserve_owned(&site, MemoryKind::host_heap(), 40, "shared backing").unwrap();
        let owner = Owner {
            bytes: 40,
            fixed_role: role,
            children: [(
                OwnerSlot::Contents,
                Owner {
                    kind: payload_kind.clone(),
                    dynamic: Some(allocation),
                    ..Default::default()
                },
            )]
            .into(),
            ..Default::default()
        };
        let charges = SharedBackingCharges::for_payload(&owner, &[], &site).unwrap().unwrap();
        let mut alternative = storage.clone();
        storage.set_allocation(allocation, payload_kind.clone(), contracts::literal(&site, 7));
        alternative.set_allocation(allocation, payload_kind.clone(), contracts::literal(&site, 19));
        storage.join_live(&alternative).unwrap();
        assert!(charges.defer(&mut storage, crate::ast_util::mk_bool(&site, false), &site));
        assert!(storage.paths.iter().all(|p| p.owned.is_empty()));
        charges.receive(&mut storage, &site).unwrap();
        let restored: Vec<_> = storage
            .paths
            .iter()
            .map(|path| {
                let charge = &path.dynamic[&allocation];
                assert_eq!(charge.kind, payload_kind);
                assert_eq!(path.fixed[&MemoryKind::host_heap()], 40);
                assert_eq!(path.owned[&role.unwrap()].identity, role.unwrap());
                contracts::constant(&charge.amount).unwrap()
            })
            .collect();
        assert_eq!(restored, [7, 19]);
    }

    #[test]
    fn missing_result_storage_cannot_be_discarded_at_completion() {
        let site = span(1);
        let mut worker = Accounting::new(&site, 1024);
        worker.reserve(&site, MemoryKind::host_heap(), 32, "lost allocation").unwrap();
        assert!(worker.check_transferred(&site).is_err());
        let fabricated = Storage {
            typ: crate::ast_util::unit_typ(),
            value: Value::unit(),
            owner: Some(Owner { bytes: 64, ..Default::default() }),
        };
        assert!(worker.take_storage(&fabricated, &Growth::default(), &site).is_err());
        assert_eq!(live(&worker), 32);
    }
}
