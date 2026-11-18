//! Move charged storage between actors without executing a destructor or adding
//! their histories together. Publication and collection use the same operation.

use super::{Accounting, Charge, Live};
use crate::resource::memory::{growth::Growth, heap::Owner, lifetime::Storage, model::unsupported};
use crate::{
    ast::{Expr, VirErr},
    messages::Span,
};
use std::collections::{BTreeMap, HashSet};

impl Accounting {
    /// Transfer the existing flat backing charge when the last finite handle
    /// goes away. Its conditional replacement describes the same allocation.
    pub(in super::super) fn defer_shared_backing(&mut self, id: u64, owner: &Owner, cost: Expr) {
        for path in &mut self.paths {
            path.remove_fixed(&owner.kind, owner.bytes);
            path.dynamic.insert(id, Charge { kind: owner.kind.clone(), amount: cost.clone() });
        }
    }

    /// A checked result has brought a strong handle back into the fixed tree.
    /// Require its existing conditional charge on every incoming path.
    pub(in super::super) fn receive_shared_backing(
        &mut self,
        span: &Span,
        id: u64,
        owner: &Owner,
    ) -> Result<(), VirErr> {
        for path in &mut self.paths {
            if path.dynamic.remove(&id).is_none() {
                return Err(unsupported(
                    span,
                    "an indexed Arc result without its retained backing charge",
                ));
            }
            path.add_fixed(span, &owner.kind, owner.bytes)?;
        }
        self.record_live(span)
    }

    /// A completed body must have transferred or released every charge. A
    /// missing descriptor cannot silently turn live storage into zero bytes.
    pub(in super::super) fn check_transferred(&self, span: &Span) -> Result<(), VirErr> {
        if self.paths.iter().any(|path| {
            path.fixed.values().any(|bytes| *bytes != 0)
                || !path.dynamic.is_empty()
                || path.values.values().any(|charge| charge.amount != 0)
                || !path.inputs.is_empty()
        }) {
            return Err(unsupported(
                span,
                "worker completion with storage absent from its result descriptor",
            ));
        }
        Ok(())
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
        let mut fixed = BTreeMap::<_, u64>::new();
        let mut dynamic = HashSet::new();
        let mut inputs = HashSet::new();
        let mut duplicate = false;
        if let Some(owner) = &storage.owner {
            inputs.extend(owner.inputs());
            owner.visit(&mut |node| {
                let bytes = fixed.entry(node.kind.clone()).or_default();
                *bytes = bytes.checked_add(node.bytes).expect("live storage fits the model");
                if let Some(id) = node.dynamic {
                    duplicate |= !dynamic.insert(id);
                }
                if let Some(elements) = &node.elements {
                    for state in elements.states.values() {
                        duplicate |= !dynamic.insert(growth.elements[*state].id);
                    }
                }
            });
        }
        if duplicate {
            return Err(unsupported(span, "duplicate allocation identities in actor transport"));
        }
        let mut remaining = self.paths.clone();
        let mut transferred = Vec::new();
        for path in &mut remaining {
            let mut selected = Live::default();
            for (kind, bytes) in &fixed {
                if *bytes == 0 {
                    continue;
                }
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
                if incoming.values.keys().any(|id| current.values.contains_key(id))
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
        caller.reserve(&site, MemoryKind::host_heap(), 32, "owned buffer").unwrap();
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
            owner: Some(Owner { bytes: 32, dynamic: Some(allocation), ..Default::default() }),
        };
        let mut worker = caller.take_storage(&storage, &Growth::default(), &span(2)).unwrap();
        assert_eq!(live(&caller), 0);
        assert_eq!(live(&worker), 56);
        worker.reserve(&span(3), MemoryKind::host_heap(), 80, "worker scratch").unwrap();
        worker.release(&span(4), MemoryKind::host_heap(), 80, "worker scratch");
        assert_eq!(peak(&caller), 56);
        assert_eq!(peak(&worker), 136);
        let outgoing = worker.take_storage(&storage, &Growth::default(), &span(5)).unwrap();
        worker.check_transferred(&span(5)).unwrap();
        caller.receive_storage(outgoing.clone(), &span(6)).unwrap();
        assert_eq!(live(&caller), 56);
        assert_eq!(peak(&caller), 56);
        assert!(caller.receive_storage(outgoing, &span(7)).is_err());
        assert_eq!(live(&caller), 56);
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
