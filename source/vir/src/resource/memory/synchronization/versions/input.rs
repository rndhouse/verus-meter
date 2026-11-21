//! Source storage supplied by a previous holder of the same mutex.
use super::*;
use crate::resource::memory::{
    contracts,
    layout::{AllocationLayout, Layouts},
};

impl Layouts {
    /// A sized box always owns its declared payload. A product of such fields
    /// also has a fixed heap layout. A vector, slice or Option needs a value.
    fn fixed_acquired_owner(&self, typ: &Typ, span: &Span) -> Result<Option<Owner>, VirErr> {
        if self.cardinality(typ) {
            return Ok(None);
        }
        let mut owner = Owner::default();
        if let Some(AllocationLayout::Fixed(bytes)) = self.box_layout(typ, span)? {
            owner.extent = Some(contracts::literal(span, bytes));
        }
        for (slot, child) in self.owned_children(typ, span)? {
            let Some(child) = self.fixed_acquired_owner(&child, span)? else { return Ok(None) };
            owner.children.insert(slot, child);
        }
        Ok(Some(owner))
    }
}

/// The fixed shape contains one literal extent per separately owned box.
fn fixed_bytes(owner: &Owner) -> Option<u64> {
    let own = owner.extent.as_ref().map_or(Some(0), contracts::constant)?;
    owner.children.values().try_fold(own, |sum, child| sum.checked_add(fixed_bytes(child)?))
}

impl Analysis<'_> {
    pub(super) fn unrestricted_payload(&mut self, site: &Span, name: &str) -> Expr {
        // Normalize malformed descriptors to the empty forest. Every legal
        // incoming forest is still possible, without adding a trusted premise.
        let any = self.metadata_local(
            site,
            "unknown_protected_contents",
            SpannedTyped::new(site, &expr::memory_type(), ExprX::Nondeterministic),
        );
        let valid =
            expr::operation(site, "well_formed", vec![any.clone()], crate::ast_util::bool_typ());
        self.metadata_local(
            site,
            name,
            SpannedTyped::new(
                site,
                &expr::memory_type(),
                ExprX::If(valid, any, Some(expr::empty(site, expr::record_type()))),
            ),
        )
    }

    pub(super) fn acquired_owner(
        &mut self,
        typ: &Typ,
        site: &Span,
    ) -> Result<(Expr, Owner, Option<u64>), VirErr> {
        if let Some(mut payload) = self.layouts.fixed_acquired_owner(typ, site)? {
            // Each role is an input to this acquisition. No source allocation
            // or destructor occurs when a guard first looks at an existing Box.
            payload.visit_mut(&mut |node| {
                if let Some(bytes) = &node.extent {
                    let id = Accounting::fresh_allocation();
                    node.dynamic = Some(id);
                    self.storage.set_allocation(id, node.kind.clone(), bytes.clone());
                }
            });
            let entry = self.snapshot_owner_metadata(site, &payload);
            let bytes = fixed_bytes(&payload);
            return Ok((entry, payload, bytes));
        }
        let entry = self.unrestricted_payload(site, "protected_contents");
        let mut payload =
            self.owner_from_metadata(site, typ, entry.clone(), metadata::View::Complete, false)?;
        if let Some(id) = payload.vector {
            let length = self.allocation_snapshot(
                site,
                payload.geometry.clone().expect("complete vector geometry"),
            );
            self.growth.vectors[id].protected_length = Some(length.clone());
            payload.geometry = Some(length);
        }
        Ok((entry, payload, None))
    }
}
