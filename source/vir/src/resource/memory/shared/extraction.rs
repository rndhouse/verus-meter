//! Recover the executable contents of a proved unique Arc.
use super::*;
use crate::resource::memory::{accounting::Accounting, contracts, metadata::expr as meta};

impl Analysis<'_> {
    /// Only an owned, uniquely identified allocation can yield its payload. A
    /// worker awaiting collection or an alias in a collection can defeat uniqueness.
    pub(super) fn take_shared_payload(
        &mut self,
        expr: &Expr,
        source: &Expr,
    ) -> Result<Owner, VirErr> {
        let span = &expr.span;
        let payload = self.layouts.option_payload(&expr.typ, span)?;
        if !matches!(&*source.typ, TypX::Decorate(TypDecoration::Arc, _, inner)
            if crate::ast_util::types_equal(inner, payload))
        {
            return Err(unsupported(span, "this Arc::into_inner payload type"));
        }
        let handle = self.produce(source)?;
        let root = self
            .result_owner
            .take()
            .and_then(|o| o.shared)
            .and_then(StrongLink::known)
            .ok_or_else(|| {
                unsupported(span, "extracting a shared payload without a known allocation")
            })?;
        if !(self.transitions.owns_fixed_root(root) || self.transitions.recovered_payload(root))
            || self.growth.section_shared.contains(&root)
            || self.growth.peer_results.contains_key(&root)
            || self.growth.occurrence_peers.contains_key(&root)
            || !self
                .heap
                .shared
                .roots
                .get(&root)
                .is_some_and(|r| r.strong == 1 && matches!(r.storage, Backing::Owned(_)))
        {
            return Err(unsupported(
                span,
                "extracting a shared payload without exclusive ownership",
            ));
        }
        if let Some(claims) = self.growth.indexed_shared.get(&root) {
            self.growth.before.entry(span.id).or_default().push(meta::check(
                span,
                crate::ast_util::mk_eq(span, &claims.population.pending, &meta::integer(span, 0)),
                "cannot extract a shared payload while indexed aliases still own it",
            ));
        }
        if self.growth.versioned_shared.contains_key(&root)
            && (!self.heap.shared.payload_settled(root) || self.heap.workers.shares_root(root))
        {
            return Err(unsupported(
                span,
                "extracting a protected payload before composing its worker updates",
            ));
        }
        let mut backing = self.heap.shared.release(root).unwrap();
        let mut result = Owner {
            extracted_arc: Some(root),
            geometry: Some(contracts::literal(span, 1)),
            ..Owner::default()
        };
        if let Some(identity) = self.growth.grouped_inners.get(&root).cloned()
            && !backing.children.contains_key(&OwnerSlot::Contents)
        {
            let child = self.unpack_grouped_inner(span, payload, &backing, identity)?;
            backing.children.insert(OwnerSlot::Contents, child);
        }
        if self.layouts.owner(payload) && !backing.children.contains_key(&OwnerSlot::Contents) {
            return Err(unsupported(
                span,
                "unique Arc extraction without its original payload ownership",
            ));
        }
        if let Some(child) = backing.children.remove(&OwnerSlot::Contents) {
            result.children.insert(OwnerSlot::Contents, child);
        }
        self.release_owner(backing, span);
        self.release_value(handle, span);
        self.transitions.operation(
            span,
            super::super::transfer::checked::Operation::StrongTake { source: source.clone(), root },
        );
        Ok(result)
    }

    /// The selected slot groups the outer backing and its sole privately owned child.
    /// Only the wrapper has a fixed size. The remaining bytes belong to this visit.
    fn unpack_grouped_inner(
        &mut self,
        span: &Span,
        payload: &Typ,
        backing: &Owner,
        identity: Expr,
    ) -> Result<Owner, VirErr> {
        let id = backing
            .dynamic
            .filter(|id| self.storage.contains_allocation(*id))
            .ok_or_else(|| unsupported(span, "a grouped Arc without its byte charge"))?;
        let total = self.storage.dynamic_cost(span, id);
        let header = verus_meter_model::arc_backing_bytes(self.layouts.size(payload, span)?)
            .ok_or_else(|| unsupported(span, "an Arc wrapper exceeding u64"))?;
        let header = contracts::literal(span, header);
        self.growth.before.entry(span.id).or_default().push(meta::check(
            span,
            crate::ast_util::mk_ineq(span, &header, &total, InequalityOp::Le),
            "cannot separate the unique outer Arc from its inner allocation",
        ));
        let bytes = contracts::subtract(span, total, header.clone());
        self.storage.set_allocation(id, backing.kind.clone(), header);
        let inner = Accounting::fresh_allocation();
        self.storage.set_allocation(inner, backing.kind.clone(), bytes.clone());
        let handle = self.heap.shared.insert(Owner {
            dynamic: Some(inner),
            extent: Some(bytes),
            kind: backing.kind.clone(),
            ..Default::default()
        });
        self.growth.shared_occurrences.insert(handle.shared.unwrap().known().unwrap(), identity);
        Ok(handle)
    }
}
