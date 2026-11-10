//! Concrete layouts. Structs are sums of executable fields, without ABI padding.

use super::model::{WORD_BYTES, integer_size, integer_type_size, slice, unsupported};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

/// Storage within one allocation. Element storage includes inline fields/handles;
/// allocations owned by those elements require separate ownership accounting.
pub(super) enum AllocationLayout {
    /// One statically sized payload, in model bytes.
    Fixed(u64),
    /// Contiguous inline elements; the operation supplies length or capacity.
    Sequence { element: u64 },
}

pub(super) struct Layouts {
    datatypes: HashMap<Dt, Datatype>,
    global_allocator: Option<Dt>,
    vector: Option<Dt>,
    option: Option<Dt>,
}

impl Layouts {
    pub(super) fn new(
        datatypes: &[Datatype],
        global_allocator: Option<Dt>,
        vector: Option<Dt>,
        option: Option<Dt>,
    ) -> Self {
        Self {
            datatypes: datatypes.iter().map(|d| (d.x.name.clone(), d.clone())).collect(),
            global_allocator,
            vector,
            option,
        }
    }

    pub(super) fn vector(&self, typ: &Typ) -> bool {
        matches!(&**typ, TypX::Datatype(name, _, _) if Some(name) == self.vector.as_ref())
    }

    pub(super) fn borrowed_owner<'t>(&self, typ: &'t Typ) -> Option<&'t Typ> {
        let inner = super::paths::referent(typ);
        (matches!(&**typ, TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, None, _))
            && self.owner(inner))
        .then_some(inner)
    }

    pub(super) fn option(&self, typ: &Typ) -> bool {
        matches!(&**typ, TypX::Datatype(name, _, _) if Some(name) == self.option.as_ref())
    }

    pub(super) fn option_payload<'a>(&self, typ: &'a Typ, span: &Span) -> Result<&'a Typ, VirErr> {
        let TypX::Datatype(_, args, _) = &**typ else {
            return Err(unsupported(span, "this Option type"));
        };
        if !self.option(typ) || args.len() != 1 {
            return Err(unsupported(span, "this Option type"));
        }
        if self.owner(&args[0]) || matches!(&*args[0], TypX::Decorate(..) | TypX::MutRef(_)) {
            return Err(unsupported(span, "owning or reference-valued Option payloads"));
        }
        Ok(&args[0])
    }

    pub(super) fn return_size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        if !self.owner(typ) && matches!(&**typ, TypX::Decorate(..) | TypX::MutRef(_)) {
            return Err(unsupported(span, "reference return values"));
        }
        self.size(typ, span)
    }

    pub(super) fn owner(&self, typ: &Typ) -> bool {
        self.owner_inner(typ, &mut HashSet::new())
    }

    fn owner_inner(&self, typ: &Typ, visiting: &mut HashSet<Dt>) -> bool {
        if super::heap::boxed(typ) || self.vector(typ) {
            return true;
        }
        let TypX::Datatype(name, _, _) = &**typ else { return false };
        let Some(datatype) = self.datatypes.get(name) else { return false };
        if !datatype.x.is_struct || !visiting.insert(name.clone()) {
            return false;
        }
        let owns = datatype
            .x
            .variants
            .iter()
            .any(|v| v.fields.iter().any(|f| self.owner_inner(&f.a.0, visiting)));
        visiting.remove(name);
        owns
    }

    pub(super) fn vector_element(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        let TypX::Datatype(_, args, _) = &**typ else {
            return Err(unsupported(span, "this vector type"));
        };
        if !self.vector(typ) || args.len() != 2 || !self.standard_allocator(&args[1]) {
            return Err(unsupported(span, "vectors with custom allocator types"));
        }
        self.element_size(&args[0], span, &mut HashSet::new())
    }

    /// Runtime sequences expose element shape separately from fixed child paths.
    pub(super) fn owning_elements(&self, typ: &Typ) -> bool {
        if self.vector(typ) {
            let TypX::Datatype(_, args, _) = &**typ else { unreachable!() };
            args.first().is_some_and(|typ| self.owner(typ))
        } else if let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            matches!(&**inner, TypX::Primitive(Primitive::Slice, args) if args.first().is_some_and(|typ| self.owner(typ)))
        } else {
            false
        }
    }

    fn element_size(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<Dt>,
    ) -> Result<u64, VirErr> {
        if matches!(&**typ, TypX::MutRef(_))
            || matches!(&**typ, TypX::Decorate(d, _, _) if *d != TypDecoration::Box)
        {
            return Err(unsupported(span, "reference-valued collection elements"));
        }
        self.size_inner(typ, span, visiting)
    }

    /// Child owners occupy inline storage already counted by the containing value.
    pub(super) fn owned_children(
        &self,
        typ: &Typ,
        span: &Span,
    ) -> Result<std::collections::BTreeMap<super::heap::OwnerSlot, Typ>, VirErr> {
        use super::heap::OwnerSlot;
        let mut children = std::collections::BTreeMap::new();
        if let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            if self.owner(inner) {
                children.insert(OwnerSlot::Contents, inner.clone());
            }
        } else if self.owner(typ) && !self.vector(typ) {
            for field in self.struct_variant(typ, span)?.fields.iter() {
                if self.owner(&field.a.0) {
                    children.insert(OwnerSlot::Field(field.name.clone()), field.a.0.clone());
                }
            }
        }
        Ok(children)
    }

    fn standard_allocator(&self, typ: &Typ) -> bool {
        match &**typ {
            TypX::Primitive(Primitive::Global, _) => true,
            TypX::Datatype(name, args, _) => {
                args.is_empty() && Some(name) == self.global_allocator.as_ref()
            }
            _ => false,
        }
    }

    /// Metadata checks shared by sizing, construction, and field projection.
    /// Field layout validation is performed by `size` before using the variant.
    pub(super) fn struct_variant(&self, typ: &Typ, span: &Span) -> Result<&Variant, VirErr> {
        let TypX::Datatype(name @ Dt::Path(_), args, _) = &**typ else {
            return Err(unsupported(span, "this struct type"));
        };
        let datatype = self
            .datatypes
            .get(name)
            .ok_or_else(|| unsupported(span, "struct layouts outside this crate"))?;
        let d = &datatype.x;
        if !d.is_struct || d.variants.len() != 1 {
            return Err(unsupported(span, "enum or union layouts"));
        }
        if d.destructor {
            return Err(unsupported(span, "structs with destructors"));
        }
        if !args.is_empty() || !d.typ_params.is_empty() || !d.typ_bounds.is_empty() {
            return Err(unsupported(span, "generic struct layouts"));
        }
        if d.proxy.is_some()
            || !matches!(d.transparency, DatatypeTransparency::WhenVisible(_))
            || d.mode != Mode::Exec
            || d.user_defined_invariant_fn.is_some()
        {
            return Err(unsupported(span, "opaque, proxy, ghost, or invariant-bearing structs"));
        }
        Ok(&d.variants[0])
    }

    pub(super) fn size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        self.size_inner(typ, span, &mut HashSet::new())
    }

    /// Select the existing inline layout for a reference, excluding borrowed data.
    pub(super) fn ref_size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        if !matches!(&**typ, TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, None, _)) {
            return Err(crate::messages::error(
                span,
                "ref_size requires a reference type or binding",
            ));
        }
        self.size(typ, span)
    }

    /// Select the existing inline layout for a non-reference value. Allocations
    /// behind owning handles remain separate charges in the accounting model.
    pub(super) fn value_size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        if matches!(&**typ, TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, None, _)) {
            return Err(crate::messages::error(
                span,
                "value_size requires a non-reference type or binding; use ref_size for references",
            ));
        }
        self.size(typ, span)
    }

    /// A box owns a fixed value or a runtime-length sequence of supported values.
    /// Its handle and heap object are sized separately so moves do not duplicate
    /// the allocation and borrows keep backing storage charged to its owner.
    pub(super) fn box_layout(
        &self,
        typ: &Typ,
        span: &Span,
    ) -> Result<Option<AllocationLayout>, VirErr> {
        self.box_layout_inner(typ, span, &mut HashSet::new())
    }

    fn box_layout_inner(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<Dt>,
    ) -> Result<Option<AllocationLayout>, VirErr> {
        let TypX::Decorate(TypDecoration::Box, allocator, inner) = &**typ else {
            return Ok(None);
        };
        if !allocator.as_ref().is_some_and(|a| match &*a.allocator_typ {
            TypX::Primitive(Primitive::Global, _) => true,
            TypX::Datatype(name, args, _) => {
                args.is_empty() && Some(name) == self.global_allocator.as_ref()
            }
            _ => false,
        }) {
            return Err(unsupported(span, "boxes with custom allocator types"));
        }
        if matches!(&**inner, TypX::MutRef(_))
            || matches!(&**inner, TypX::Decorate(d, _, _) if *d != TypDecoration::Box)
        {
            return Err(unsupported(span, "reference-valued heap objects"));
        }
        Ok(Some(if slice(inner) {
            AllocationLayout::Sequence { element: self.slice_element_inner(inner, span, visiting)? }
        } else {
            AllocationLayout::Fixed(self.size_inner(inner, span, visiting)?)
        }))
    }

    pub(super) fn slice_element(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        self.slice_element_inner(typ, span, &mut HashSet::new())
    }

    fn slice_element_inner(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<Dt>,
    ) -> Result<u64, VirErr> {
        let TypX::Primitive(Primitive::Slice, args) = &**typ else {
            return Err(unsupported(span, "this slice type"));
        };
        if args.len() != 1 {
            return Err(unsupported(span, "this slice type"));
        }
        self.element_size(&args[0], span, visiting)
    }

    fn size_inner(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<Dt>,
    ) -> Result<u64, VirErr> {
        match &**typ {
            _ if self.option(typ) => {
                let payload = self.option_payload(typ, span)?;
                self.size_inner(payload, span, visiting)?
                    .checked_add(1)
                    .ok_or_else(|| unsupported(span, "Option sizes exceeding u64"))
            }
            _ if self.vector(typ) => {
                let TypX::Datatype(_, args, _) = &**typ else { unreachable!() };
                if args.len() != 2 || !self.standard_allocator(&args[1]) {
                    return Err(unsupported(span, "vectors with custom allocator types"));
                }
                self.element_size(&args[0], span, visiting)?;
                Ok(3 * WORD_BYTES)
            }
            TypX::Decorate(TypDecoration::Box, _, _) => {
                match self.box_layout_inner(typ, span, visiting)?.unwrap() {
                    AllocationLayout::Fixed(_) => Ok(WORD_BYTES),
                    AllocationLayout::Sequence { .. } => Ok(2 * WORD_BYTES),
                }
            }
            TypX::Bool => Ok(1),
            TypX::Int(range) if integer_size(range).is_some() => Ok(integer_size(range).unwrap()),
            TypX::MutRef(inner) | TypX::Decorate(TypDecoration::Ref, None, inner) => {
                if slice(inner) {
                    self.slice_element(inner, span)?;
                    Ok(2 * WORD_BYTES)
                } else if matches!(
                    &**inner,
                    TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, ..)
                ) {
                    Err(unsupported(span, "nested references"))
                } else {
                    self.size_inner(inner, span, visiting)?;
                    Ok(WORD_BYTES)
                }
            }
            TypX::Datatype(Dt::Tuple(0), _, _) => Ok(0),
            TypX::Datatype(name @ Dt::Path(_), _, _) => {
                let variant = self.struct_variant(typ, span)?;
                if !visiting.insert(name.clone()) {
                    return Err(unsupported(span, "recursive struct layouts"));
                }
                let mut bytes = 0u64;
                for field in variant.fields.iter() {
                    let (typ, mode, _) = &field.a;
                    if *mode != Mode::Exec {
                        return Err(unsupported(span, "ghost or tracked struct fields"));
                    }
                    if matches!(&**typ, TypX::MutRef(_))
                        || matches!(&**typ, TypX::Decorate(d, _, _) if *d != TypDecoration::Box)
                    {
                        return Err(unsupported(span, "reference or decorated struct fields"));
                    }
                    let field_bytes = self.size_inner(typ, span, visiting)?;
                    bytes = bytes
                        .checked_add(field_bytes)
                        .ok_or_else(|| unsupported(span, "struct sizes exceeding u64"))?;
                }
                visiting.remove(name);
                Ok(bytes)
            }
            TypX::Primitive(Primitive::Array, args)
                if args.len() == 2 && integer_type_size(&args[0]).is_some() =>
            {
                let TypX::ConstInt(n) = &*args[1] else {
                    return Err(unsupported(span, "nonliteral array lengths"));
                };
                n.to_string()
                    .parse::<u64>()
                    .ok()
                    .and_then(|n| n.checked_mul(integer_type_size(&args[0]).unwrap()))
                    .ok_or_else(|| unsupported(span, "array sizes exceeding u64"))
            }
            _ => Err(unsupported(
                span,
                "this type (expected bool, a native integer, a fixed integer array, unit, a concrete struct, a local box, or a supported reference)",
            )),
        }
    }
}
