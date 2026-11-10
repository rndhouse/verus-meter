//! The same finite structural traversal serializes and restores every supported
//! ownership shape. Runtime repetition stays in the allocation forest.

use super::super::{
    analysis::Analysis,
    contracts,
    footprint::Charge,
    heap::{Owner, OwnerSlot},
};
use super::expr;
use crate::ast::*;
use crate::messages::Span;

impl Analysis<'_> {
    pub(in super::super) fn owner_metadata(
        &mut self,
        span: &Span,
        owner: &Owner,
        proofs: &mut Vec<Stmt>,
    ) -> Expr {
        let bytes = owner.dynamic.map_or_else(
            || contracts::literal(span, owner.bytes),
            |id| {
                contracts::add(
                    span,
                    contracts::literal(span, owner.bytes),
                    self.storage.dynamic_cost(span, id),
                )
            },
        );
        let capacity = owner
            .vector
            .map(|id| self.growth.vectors[id].capacity.clone())
            .or_else(|| owner.capacity.clone())
            .unwrap_or_else(|| expr::integer(span, 0));
        let record = expr::operation(
            span,
            "allocated",
            vec![expr::path(span, []), expr::integer(span, 0), bytes, capacity],
            expr::record_type(),
        );
        let empty = expr::empty(span, expr::record_type());
        let mut memory = expr::push(span, empty.clone(), record.clone());
        proofs.push(expr::lemma(span, "well_formed_record", vec![record.clone()]));
        proofs.push(expr::lemma(
            span,
            "cost_push",
            vec![empty.clone(), record.clone(), expr::integer(span, 0)],
        ));
        let mut parts = Vec::new();
        for (slot, child) in &owner.children {
            if matches!(slot, OwnerSlot::Element(_)) {
                continue;
            }
            let child = self.owner_metadata(span, child, proofs);
            let path = expr::path(span, [self.layouts.metadata_slot(slot)]);
            let nested = expr::prefix(span, child.clone(), path.clone());
            parts.push((memory.clone(), nested.clone(), child.clone(), path.clone()));
            proofs.push(expr::lemma(
                span,
                "cost_prefix",
                vec![child.clone(), path.clone(), expr::integer(span, 0)],
            ));
            proofs.push(expr::lemma(span, "well_formed_prefix", vec![child, path]));
            proofs.push(expr::lemma(span, "well_formed_add", vec![memory.clone(), nested.clone()]));
            proofs.push(expr::lemma(
                span,
                "cost_add",
                vec![memory.clone(), nested.clone(), expr::integer(span, 0)],
            ));
            memory = expr::add(span, memory, nested);
        }
        // Make fixed-child views explicit before exposing the assembled forest.
        // These facts compose through repeated parents without unfolding a
        // recursive selection for every nested field access in a loop query.
        for (_, _, _, selected) in &parts {
            proofs.push(expr::lemma(
                span,
                "select_push",
                vec![empty.clone(), record.clone(), selected.clone()],
            ));
            for (before, nested, child, path) in &parts {
                proofs.push(expr::lemma(
                    span,
                    "select_add",
                    vec![before.clone(), nested.clone(), selected.clone()],
                ));
                proofs.push(expr::lemma(
                    span,
                    "select_prefix",
                    vec![child.clone(), path.clone(), selected.clone()],
                ));
            }
        }
        if let Some(elements) = &owner.elements {
            let records = if elements.precise {
                elements.records.clone()
            } else {
                // Opaque children retain their entire upper bound in one
                // descriptor. They expose no recoverable reservation facts.
                let amount = self.owner_element_bytes(span, elements);
                let record = expr::operation(
                    span,
                    "allocated",
                    vec![
                        expr::path(span, [0]),
                        expr::integer(span, 0),
                        amount,
                        expr::integer(span, 0),
                    ],
                    expr::record_type(),
                );
                let empty = expr::empty(span, expr::record_type());
                proofs.push(expr::lemma(
                    span,
                    "cost_push",
                    vec![empty.clone(), record.clone(), expr::integer(span, 0)],
                ));
                expr::push(span, empty, record)
            };
            proofs.push(expr::lemma(
                span,
                "cost_add",
                vec![memory.clone(), records.clone(), expr::integer(span, 0)],
            ));
            proofs.push(expr::lemma(
                span,
                "well_formed_add",
                vec![memory.clone(), records.clone()],
            ));
            memory = expr::add(span, memory, records);
        }
        memory
    }

    pub(in super::super) fn snapshot_owner_metadata(&mut self, span: &Span, owner: &Owner) -> Expr {
        let mut proofs = Vec::new();
        let value = self.owner_metadata(span, owner, &mut proofs);
        self.growth.before.entry(span.id).or_default().extend(proofs);
        self.metadata_local(span, "owner_records", value)
    }

    fn owner_element_bytes(
        &self,
        span: &Span,
        elements: &super::super::elements::Elements,
    ) -> Expr {
        elements.states.values().fold(contracts::literal(span, 0), |sum, id| {
            contracts::add(span, sum, self.growth.elements[*id].bytes.clone())
        })
    }

    /// Partition an existing forest into disjoint fixed children, runtime
    /// children and this node's remaining charge. Residual paths stay charged;
    /// no assumption about uniqueness or container geometry is needed for sums.
    pub(in super::super) fn owner_from_metadata(
        &mut self,
        span: &Span,
        typ: &Typ,
        memory: Expr,
    ) -> Result<Owner, VirErr> {
        let memory = self.metadata_local(span, "selected_records", memory);
        self.growth.before.entry(span.id).or_default().push(expr::lemma(
            span,
            "inspect",
            vec![memory.clone(), expr::path(span, [])],
        ));
        let mut rest = memory.clone();
        let mut owner = Owner::default();
        for (slot, child_type) in self.layouts.owned_children(typ, span)? {
            let path = expr::path(span, [self.layouts.metadata_slot(&slot)]);
            self.metadata_partition(span, rest.clone(), path.clone());
            let child = expr::subtree(span, rest.clone(), path.clone());
            owner.children.insert(slot, self.owner_from_metadata(span, &child_type, child)?);
            rest = expr::without(span, rest, path);
        }
        if self.layouts.owning_elements(typ) {
            self.growth.before.entry(span.id).or_default().push(expr::lemma(
                span,
                "inspect",
                vec![rest.clone(), expr::path(span, [])],
            ));
            let children =
                expr::operation(span, "runtime", vec![rest.clone()], expr::memory_type());
            self.growth.before.entry(span.id).or_default().push(expr::lemma(
                span,
                "cost_runtime_partition",
                vec![rest.clone(), expr::integer(span, 0)],
            ));
            let amount = self.metadata_sum(span, children.clone());
            let mut elements =
                self.elements_from_bytes(span, [(owner.kind.clone(), amount)].into());
            self.growth.before.entry(span.id).or_default().push(expr::assign(
                span,
                &elements.records,
                children,
            ));
            elements.precise = true;
            owner.elements = Some(elements);
            rest = expr::operation(span, "nonruntime", vec![rest], expr::memory_type());
        }
        self.growth.before.entry(span.id).or_default().push(expr::lemma(
            span,
            "inspect",
            vec![rest.clone(), expr::path(span, [])],
        ));
        let amount = self.metadata_sum(span, rest);
        owner.extent = Some(amount.clone());
        let allocation = super::super::accounting::Accounting::fresh_allocation();
        if self.layouts.vector(typ) {
            let record = expr::lookup(span, memory, expr::path(span, []));
            let capacity = self.metadata_local(
                span,
                "selected_capacity",
                expr::record_field(span, record, "capacity"),
            );
            let id = self.growth.new_vector(
                span,
                capacity.clone(),
                Charge { kind: owner.kind.clone(), amount },
                self.layouts.vector_element(typ, span)?,
                None,
                allocation,
            );
            owner.vector = Some(id);
            owner.capacity = Some(capacity);
            self.storage.set_allocation(
                allocation,
                owner.kind.clone(),
                self.growth.vectors[id].backing.bytes.clone(),
            );
        } else {
            self.storage.set_allocation(allocation, owner.kind.clone(), amount);
        }
        owner.dynamic = Some(allocation);
        Ok(owner)
    }
}
