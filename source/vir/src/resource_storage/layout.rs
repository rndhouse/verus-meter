//! Concrete layouts. Structs are sums of executable fields, without ABI padding.

use super::model::{WORD_BYTES, integer_size, integer_type_size, slice, unsupported};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

pub(super) struct Layouts {
    datatypes: HashMap<Dt, Datatype>,
    global_allocator: Option<Dt>,
}

impl Layouts {
    pub(super) fn new(datatypes: &[Datatype], global_allocator: Option<Dt>) -> Self {
        Self {
            datatypes: datatypes.iter().map(|d| (d.x.name.clone(), d.clone())).collect(),
            global_allocator,
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

    /// A box owns a fixed, non-owning value under the standard global allocator.
    /// Its handle and heap object are sized separately so moves do not duplicate
    /// the allocation and borrows keep backing storage charged to its owner.
    pub(super) fn box_contents(&self, typ: &Typ, span: &Span) -> Result<Option<u64>, VirErr> {
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
        if matches!(&**inner, TypX::Decorate(..) | TypX::MutRef(_)) {
            return Err(unsupported(span, "nested boxes or reference-valued heap objects"));
        }
        Ok(Some(self.size(inner, span)?))
    }

    fn size_inner(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<Dt>,
    ) -> Result<u64, VirErr> {
        match &**typ {
            TypX::Decorate(TypDecoration::Box, _, _) => {
                self.box_contents(typ, span)?;
                Ok(WORD_BYTES)
            }
            TypX::Bool => Ok(1),
            TypX::Int(range) if integer_size(range).is_some() => Ok(integer_size(range).unwrap()),
            TypX::MutRef(inner) | TypX::Decorate(TypDecoration::Ref, None, inner) => {
                if slice(inner) {
                    Ok(2 * WORD_BYTES)
                } else if matches!(&**inner, TypX::MutRef(_) | TypX::Decorate(..)) {
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
                    if matches!(&**typ, TypX::MutRef(_) | TypX::Decorate(..)) {
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
