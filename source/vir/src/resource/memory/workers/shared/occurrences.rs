//! Charge an allocation occurrence once in its carrying handle. Restore that extent
//! at join and keep its full identity available for reconciling independently retained peers.
use super::*;

/// Split a worker slot's charge into backing bytes and its completion tag.
/// A slot holding only a peer's reservation can have zero backing bytes.
pub(super) fn split_carried_charge(
    span: &Span,
    packed: Expr,
    proofs: &mut Vec<Stmt>,
) -> (Expr, Expr) {
    let tag = contracts::literal(span, verus_meter_model::completion_bytes(0).unwrap());
    proofs.push(expr::check(
        span,
        crate::ast_util::mk_ineq(span, &tag, &packed, InequalityOp::Le),
        "cannot locate the selected worker's retained shared backing",
    ));
    (contracts::subtract(span, packed, tag.clone()), tag)
}

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

    /// A returned strong handle takes over the selected worker's byte charge.
    /// Freeze its full allocation key before the pop's proof locals can be reused.
    pub(in crate::resource::memory::workers) fn receive_carried_arc(
        &mut self,
        span: &Span,
        owner: &Owner,
        memory: Expr,
        role: Option<PeerResult>,
        occurrence: &Occurrence,
    ) -> Result<Owner, VirErr> {
        let id = owner.dynamic.ok_or_else(|| {
            unsupported(span, "a collected shared allocation without its charged handle")
        })?;
        let packed = self.storage.dynamic_cost(span, id);
        let (bytes, tag) =
            split_carried_charge(span, packed, self.growth.before.entry(span.id).or_default());
        // The completion tag stays with the handle through result delivery.
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
        let (mut backing, bytes) =
            self.restore_payload_job(span, occurrence, role.is_some(), bytes)?;
        let allocation = Accounting::fresh_allocation();
        self.storage.set_allocation(allocation, owner.kind.clone(), bytes.clone());
        backing.dynamic = Some(allocation);
        backing.extent = Some(bytes);
        self.restore_payload_links(span, occurrence, &mut backing)?;
        let handle = self.heap.shared.insert(backing);
        let root = handle.shared.unwrap().known().unwrap();
        if let Some(role) = role {
            self.growth.peer_results.insert(root, role);
        }
        self.growth.shared_occurrences.insert(root, identity);
        Ok(handle)
    }
}
