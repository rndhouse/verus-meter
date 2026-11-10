//! Fixed-length owning sequences. The adapter determines layout and conversion
//! effects; allocation snapshots, transfer summaries, and release are shared.

use super::analysis::Analysis;
use super::contracts;
use super::footprint::Charge;
use super::heap::Owner;
use super::layout::AllocationLayout;
use super::model::unsupported;
use crate::ast::*;
use crate::ast_util::*;

impl Analysis<'_> {
    pub(super) fn boxed_slice_expr(&mut self, expr: &Expr) -> Result<Option<Owner>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(None);
        };
        if attrs.resource_intrinsic != Some(ResourceIntrinsic::VecIntoBoxedSlice) {
            return Ok(None);
        }
        let [arg] = args.as_slice() else {
            return Err(unsupported(&expr.span, "this owning-slice conversion"));
        };
        // A named receiver lets us capture its length before consuming it.
        // Temporaries with side effects need an evaluation-order adapter.
        let ExprX::ReadPlace(place, _) = &arg.x else {
            return Err(unsupported(&arg.span, "owning-slice conversion outside a named vector"));
        };
        if !matches!(place.x, PlaceX::Local(_)) || !self.layouts.vector(&place.typ) {
            return Err(unsupported(&arg.span, "owning-slice conversion outside a named vector"));
        }
        self.access(place, &place.typ)?;
        let Some(AllocationLayout::Sequence { element }) =
            self.layouts.box_layout(&expr.typ, &expr.span)?
        else {
            return Err(unsupported(&expr.span, "this owning-slice result"));
        };
        let TypX::Datatype(_, types, _) = &*place.typ else { unreachable!() };
        let len = super::vectors::length(&expr.span, types.clone(), place_to_spec_expr(place));
        let len = self.allocation_snapshot(&expr.span, len);
        let amount =
            contracts::multiply(&expr.span, contracts::literal(&expr.span, element), len.clone());
        let amount = if element == 0 {
            contracts::literal(&expr.span, 0)
        } else {
            self.allocation_snapshot(&expr.span, amount)
        };
        let source_value = self.take_value(place)?;
        let mut source = self.move_owner(place)?;
        let allocation = Charge { kind: source.kind.clone(), amount: amount.clone() };
        // The model permits a length-sized replacement even if an allocator
        // could shrink in place. Old and new backing storage overlap only here.
        self.storage.replacement_peak(&expr.span, &allocation)?;
        self.release_value(source_value, &expr.span);
        let mut elements = source.elements.take();
        if let Some(elements) = &mut elements {
            // Incoming provenance covers the whole old tree. Retaining it with
            // the children conservatively keeps its old buffer charged too.
            if let Some(input) = source.input.take() {
                elements.inputs.insert(input);
            }
        }
        self.release_owner(source, &expr.span);
        let id = super::accounting::Accounting::fresh_allocation();
        self.storage.set_allocation(id, allocation.kind.clone(), amount.clone());
        self.storage.record_live(&expr.span)?;
        Ok(Some(Owner {
            geometry: Some(len),
            kind: allocation.kind,
            elements,
            dynamic: Some(id),
            extent: Some(amount),
            ..Default::default()
        }))
    }
}
