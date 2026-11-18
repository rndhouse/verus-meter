//! Transport one allocation occurrence when all of its strong references move
//! into the same retained worker. Its charged bytes follow the handle until join.
use super::*;

impl Analysis<'_> {
    pub(super) fn transfer_occurrence_backing(
        &mut self,
        span: &Span,
        backing: &Owner,
    ) -> Result<Expr, VirErr> {
        use crate::resource::memory::{elements::References, footprint::MemoryKind};
        if !backing.complete()
            || !backing.inputs().is_empty()
            || backing.references() != References::None
        {
            return Err(unsupported(
                span,
                "indexed Arc payload with incoming storage or nested reference lifetimes",
            ));
        }
        let charges = self.owner_charges(span, backing);
        let upper = self.owner_upper(span, backing);
        let kind = MemoryKind::host_heap();
        if charges.iter().any(|(k, v)| k != &kind && contracts::constant(v) != Some(0)) {
            return Err(unsupported(
                span,
                "transporting a shared allocation with multiple memory kinds",
            ));
        }
        let bytes = upper
            .get(&kind)
            .cloned()
            .ok_or_else(|| unsupported(span, "an occurrence without a heap extent"))?;
        let actual = charges.get(&kind).ok_or_else(|| {
            unsupported(span, "a shared occurrence without a charged heap allocation")
        })?;
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            crate::ast_util::mk_ineq(span, actual, &bytes, InequalityOp::Le),
            "cannot establish the transported shared backing extent",
        ));
        self.release_owner_storage(backing.clone(), span, false)?;
        Ok(bytes)
    }

    /// A returned strong handle takes over the selected worker's byte charge.
    /// Freeze its full allocation key before the pop's proof locals can be reused.
    pub(in crate::resource::memory::workers) fn receive_carried_arc(
        &mut self,
        span: &Span,
        owner: &Owner,
        memory: Expr,
    ) -> Result<Owner, VirErr> {
        let id = owner.dynamic.ok_or_else(|| {
            unsupported(span, "a collected shared allocation without its charged handle")
        })?;
        let packed = self.storage.dynamic_cost(span, id);
        let tag = contracts::literal(span, verus_meter_model::completion_bytes(0).unwrap());
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            crate::ast_util::mk_ineq(span, &tag, &packed, InequalityOp::Le),
            "cannot locate the selected worker's retained shared backing",
        ));
        // Split the charged slot before recording the join's delivery peak.
        // The completion tag stays with the consumed handle until its release.
        let bytes = contracts::subtract(span, packed, tag.clone());
        self.storage.set_allocation(id, owner.kind.clone(), tag);
        let identity = expr::field(
            span,
            expr::lookup(span, memory, expr::path(span, [])),
            "reference_identity",
            expr::sequence_type(crate::ast_util::int_typ()),
        );
        let identity = self.freeze_shared_identity(span, identity, false);
        let allocation = Accounting::fresh_allocation();
        self.storage.set_allocation(allocation, owner.kind.clone(), bytes.clone());
        let handle = self.heap.shared.insert(Owner {
            dynamic: Some(allocation),
            extent: Some(bytes),
            ..Default::default()
        });
        self.growth.shared_occurrences.insert(handle.shared.unwrap().known().unwrap(), identity);
        Ok(handle)
    }
}
