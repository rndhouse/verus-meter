//! Transfer and replace fixed child owners through shared structural paths.
//!
//! Detaching changes ownership, not allocation charges. Replacement evaluates
//! its new value before releasing the old one, preserving their peak overlap.
//! Inline parent storage survives partial moves until the parent's lifetime ends.

use super::analysis::Analysis;
use super::heap::Owner;
use super::model::unsupported;
use crate::ast::*;

impl Analysis<'_> {
    pub(super) fn move_owner(&mut self, place: &Place) -> Result<Owner, VirErr> {
        self.move_owner_to(place, &place.typ)
    }

    pub(super) fn move_owner_to(&mut self, place: &Place, typ: &Typ) -> Result<Owner, VirErr> {
        let (name, path) = super::paths::place(place, typ)
            .ok_or_else(|| unsupported(&place.span, "heap ownership outside a fixed child path"))?;
        if super::paths::indexed(&path) {
            return Err(unsupported(&place.span, "moving ownership out of an indexed borrow"));
        }
        if !self.layouts.owner(typ) {
            return Err(unsupported(&place.span, "this heap move"));
        }
        self.access(place, typ)?;
        self.heap.check_transfer(&name, &place.span)?;
        let owner = if path.is_empty() {
            self.heap.take(&name, &place.span)?
        } else {
            self.heap.owners.get_mut(&name).and_then(|owner| owner.take_child(&path)).ok_or_else(
                || unsupported(&place.span, "moving a missing or borrowed child owner"),
            )?
        };
        self.growth.forget_element_places(&owner);
        self.storage
            .event(&place.span, "transfer child ownership without copying allocations".into());
        Ok(owner)
    }

    /// Evaluate the replacement while the displaced owner is still live. Inline
    /// destination storage already belongs to the parent; only ownership changes.
    pub(super) fn assign_owner(
        &mut self,
        place: &Place,
        typ: &Typ,
        rhs: &Expr,
    ) -> Result<(), VirErr> {
        let mut focused = Vec::new();
        self.focus_place(place, &rhs.span, &mut focused)?;
        if !focused.is_empty() {
            self.check_projection_effects(rhs)?;
        }
        self.assign_owner_inner(place, typ, rhs)?;
        self.finish_projections(&rhs.span, focused)
    }

    fn assign_owner_inner(&mut self, place: &Place, typ: &Typ, rhs: &Expr) -> Result<(), VirErr> {
        let (name, path) = super::paths::place(place, typ)
            .ok_or_else(|| unsupported(&place.span, "assignment outside a fixed child path"))?;
        if path.is_empty() {
            return Err(unsupported(&place.span, "reassignment of heap owners"));
        }
        if !super::paths::indexed(&path) {
            self.heap.check_transfer(&name, &place.span)?;
        }
        self.access(place, typ)?;
        let revision = self.growth.revision();
        self.initialize_expr(rhs)?;
        if super::paths::indexed(&path) && revision != self.growth.revision() {
            return Err(unsupported(
                &rhs.span,
                "allocation changes inside an indexed replacement; bind the replacement first",
            ));
        }
        let mut child = self
            .result_owner
            .take()
            .ok_or_else(|| unsupported(&rhs.span, "a replacement without ownership"))?;
        self.bind_collection_sources(
            &rhs.span,
            &mut child,
            typ,
            super::projections::spec_value(&crate::ast_util::place_to_spec_expr(place))?,
        )?;
        self.heap.mark_replaced(&name, &path);
        let owner = self
            .heap
            .root_mut(&name)
            .ok_or_else(|| unsupported(&place.span, "a replacement without a live root"))?;
        if owner.at(&path[..path.len() - 1]).is_none() {
            return Err(unsupported(&place.span, "a replacement without a live parent"));
        }
        if let Some(old) = owner.replace_child(&path, child) {
            self.release_owner(old, &place.span);
        }
        Ok(())
    }
}
