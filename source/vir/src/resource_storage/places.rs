//! Validate source places, reads, and borrows without synthetic address storage.

use super::analysis::Analysis;
use super::model::{slice, unsupported};
use crate::ast::*;

impl Analysis<'_> {
    fn local(&self, place: &Place) -> Result<(), VirErr> {
        if let PlaceX::Local(name) = &place.x {
            if self.var_modes.get(name) == Some(&Mode::Exec) {
                self.layouts.size(&place.typ, &place.span)?;
                if super::heap::boxed(&place.typ) && !self.heap.owners.contains_key(name) {
                    return Err(unsupported(&place.span, "a box without a live local owner"));
                }
                return Ok(());
            }
        }
        Err(unsupported(&place.span, "this place (only executable local variables are supported)"))
    }

    /// Validate a place and evaluate its index expressions. Locations do not
    /// introduce source-level storage objects.
    fn place(&mut self, place: &Place) -> Result<u64, VirErr> {
        match &place.x {
            PlaceX::Local(_) => {
                self.local(place)?;
                Ok(0)
            }
            PlaceX::DerefMut(base) => {
                let TypX::MutRef(inner) = &*base.typ else {
                    return Err(unsupported(&place.span, "this dereference"));
                };
                if !crate::ast_util::types_equal(inner, &place.typ) {
                    return Err(unsupported(&place.span, "this dereference type"));
                }
                // Dereferencing uses the existing reference value.
                self.read(base, &base.typ)
            }
            PlaceX::Field(op, base) => {
                let base_typ = match &*base.typ {
                    TypX::Decorate(TypDecoration::Ref, None, inner)
                    | TypX::Decorate(TypDecoration::Box, _, inner) => inner,
                    _ => &base.typ,
                };
                self.layouts.size(base_typ, &base.span)?;
                let variant = self.layouts.struct_variant(base_typ, &base.span)?;
                let TypX::Datatype(name, _, _) = &**base_typ else { unreachable!() };
                if op.datatype != *name
                    || op.variant != variant.name
                    || op.get_variant
                    || !matches!(op.check, VariantCheck::None)
                {
                    return Err(unsupported(&place.span, "this struct field projection"));
                }
                let field = variant
                    .fields
                    .iter()
                    .find(|f| f.name == op.field)
                    .ok_or_else(|| unsupported(&place.span, "this struct field"))?;
                if !crate::ast_util::types_equal(&field.a.0, &place.typ) {
                    return Err(unsupported(&place.span, "this struct field type"));
                }
                // Accessing a field uses the existing owner's storage.
                self.access(base, base_typ)
            }
            PlaceX::Index(base, index, _, BoundsCheck::Error) => {
                let base_typ = match &*base.typ {
                    TypX::Decorate(TypDecoration::Ref, None, inner)
                    | TypX::Decorate(TypDecoration::Box, _, inner) => inner,
                    _ => &base.typ,
                };
                if !slice(base_typ) && !matches!(&**base_typ, TypX::Primitive(Primitive::Array, _))
                {
                    return Err(unsupported(&base.span, "indexing this type"));
                }
                if !matches!(&*index.typ, TypX::Int(IntRange::USize)) {
                    return Err(unsupported(&index.span, "non-usize indexes"));
                }
                self.access(base, base_typ)?;
                self.discard(index)?;
                Ok(0)
            }
            // Compiler reborrows can materialize a reference expression as a
            // temporary place. Evaluate that reference, which recursively checks
            // its backing place; aggregate/box temporaries remain unsupported.
            PlaceX::Temporary(value)
                if matches!(
                    &*place.typ,
                    TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, None, _)
                ) && crate::ast_util::types_equal(&place.typ, &value.typ) =>
            {
                self.expr(value)
            }
            // Borrowed temporary lifetimes need a separate model. In particular,
            // never release &[...]/&mut [...] at the end of their initializer.
            _ => Err(unsupported(&place.span, "this place or borrowed temporary")),
        }
    }

    /// Account for implicit shared dereferences, which VIR omits as place nodes.
    pub(super) fn access(&mut self, place: &Place, target: &Typ) -> Result<u64, VirErr> {
        let scratch = self.place(place)?;
        if crate::ast_util::types_equal(&place.typ, target) {
            return Ok(scratch);
        }
        if let TypX::Decorate(TypDecoration::Ref, None, inner)
        | TypX::Decorate(TypDecoration::Box, _, inner) = &*place.typ
        {
            if crate::ast_util::types_equal(inner, target) {
                self.layouts.size(&place.typ, &place.span)?;
                return Ok(scratch);
            }
        }
        Err(unsupported(&place.span, "this implicit dereference or coercion"))
    }

    pub(super) fn read(&mut self, place: &Place, result_typ: &Typ) -> Result<u64, VirErr> {
        self.layouts.size(result_typ, &place.span)?;
        if super::heap::boxed(result_typ) {
            return Err(unsupported(
                &place.span,
                "box values outside a local move, borrow, or explicit drop",
            ));
        }
        self.access(place, result_typ)
    }

    pub(super) fn borrow(&mut self, place: &Place, typ: &Typ) -> Result<u64, VirErr> {
        let inner = match &**typ {
            TypX::MutRef(inner) | TypX::Decorate(TypDecoration::Ref, None, inner) => inner,
            _ => return Err(unsupported(&place.span, "this borrow type")),
        };
        self.layouts.size(typ, &place.span)?;
        self.access(place, inner)
    }
}
