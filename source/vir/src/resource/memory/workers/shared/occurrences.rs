//! Charge an allocation occurrence once in its carrying handle. Restore that extent
//! at join and keep its full identity available for reconciling independently retained peers.
use super::*;

impl Analysis<'_> {
    pub(super) fn check_occurrence_payload(span: &Span, backing: &Owner) -> Result<(), VirErr> {
        if !backing.complete()
            || !backing.inputs().is_empty()
            || backing.references() != crate::resource::memory::elements::References::None
        {
            return Err(unsupported(
                span,
                "indexed Arc payload with incoming storage or nested reference lifetimes",
            ));
        }
        Ok(())
    }

    pub(super) fn transfer_occurrence_backing(
        &mut self,
        span: &Span,
        backing: &Owner,
    ) -> Result<Expr, VirErr> {
        use crate::resource::memory::footprint::MemoryKind;
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
        role: Option<PeerResult>,
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
        let bytes = if let Some(peer) = &role {
            // Each peer slot has only its completion tag. Exactly one slot
            // represents the backing, even when both families return Arc<T>.
            let zero = expr::integer(span, 0);
            self.growth.before.entry(span.id).or_default().push(expr::check(
                span,
                crate::ast_util::disjoin(
                    span,
                    &vec![
                        crate::ast_util::mk_eq(span, &peer.borrowed, &zero),
                        crate::ast_util::mk_eq(span, &bytes, &zero),
                    ],
                ),
                "cannot separate a peer handle from the shared backing charge",
            ));
            if contracts::constant(&peer.borrowed) == Some(1) {
                // The checked membership and packed size above prove this
                // handle carries only its completion tag.
                zero
            } else if contracts::constant(&peer.borrowed) == Some(0)
                && let Some((region, extent)) =
                    &self.growth.occurrence_peers[&peer.site].publication
                && self.growth.loop_regions.last() == Some(region)
            {
                // Split the proof at collection. The source-selected slot must
                // supply the charge; this visit's checked envelope can then be
                // used directly by the drop and the next iteration.
                self.growth.before.entry(span.id).or_default().push(expr::check(
                    span,
                    crate::ast_util::mk_ineq(span, &bytes, extent, InequalityOp::Le),
                    "cannot bound the collected backing by its publication extent",
                ));
                extent.clone()
            } else {
                self.metadata_local(span, "shared_result_bytes", bytes)
            }
        } else {
            bytes
        };
        let allocation = Accounting::fresh_allocation();
        self.storage.set_allocation(allocation, owner.kind.clone(), bytes.clone());
        let handle = self.heap.shared.insert(Owner {
            dynamic: Some(allocation),
            extent: Some(bytes),
            ..Default::default()
        });
        let root = handle.shared.unwrap().known().unwrap();
        if let Some(role) = role {
            self.growth.peer_results.insert(root, role);
        }
        self.growth.shared_occurrences.insert(root, identity);
        Ok(handle)
    }
}
