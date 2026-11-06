//! Initializers share their destination's charge.
//!
//! This is a source-level accounting rule, independent of compiler lowering.
//! Locals, parameters, and enclosing aggregates provide initializer storage;
//! an aggregate expression without such a destination owns one result charge.

use super::analysis::Analysis;
use super::model::unsupported;
use crate::ast::*;

pub(super) fn aggregate(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Primitive(Primitive::Array, _) | TypX::Datatype(Dt::Path(_), _, _))
}

impl Analysis<'_> {
    /// Initialize an already reserved local, retaining only that local's charge.
    pub(super) fn initialize(&mut self, place: &Place, typ: &Typ) -> Result<(), VirErr> {
        if let PlaceX::Temporary(expr) = &place.x {
            if matches!(&*expr.typ, TypX::Decorate(TypDecoration::Ref, None, inner) if crate::ast_util::types_equal(inner, typ))
            {
                return self.copy_into_destination(place, typ);
            }
            if !crate::ast_util::types_equal(&expr.typ, typ) {
                return Err(unsupported(&place.span, "this initializer coercion"));
            }
            return self.initialize_expr(expr);
        }
        self.copy_into_destination(place, typ)
    }

    /// Evaluate into storage already charged to a local, field, or parameter.
    pub(super) fn initialize_expr(&mut self, expr: &Expr) -> Result<(), VirErr> {
        if self.layouts.owner(&expr.typ) {
            return Err(unsupported(
                &expr.span,
                "owning values outside a local move, borrow, or explicit drop",
            ));
        }
        if !aggregate(&expr.typ) {
            // Literals, reads, and operators create no implicit storage slots.
            return self.discard(expr);
        }
        self.layouts.size(&expr.typ, &expr.span)?;
        if self.construction(expr, true)?.is_some() {
            return Ok(());
        }
        if let ExprX::ReadPlace(place, kind) = &expr.x {
            if !matches!(kind.preliminary_kind, ReadKind::ImmutBor) {
                if let PlaceX::Temporary(value) = &place.x {
                    return self.initialize_expr(value);
                }
                return self.copy_into_destination(place, &expr.typ);
            }
        }
        // Preserve ordinary rejection of unsupported calls, blocks, and types.
        // No currently supported aggregate-producing expression reaches here.
        self.discard(expr)
    }

    fn copy_into_destination(&mut self, place: &Place, typ: &Typ) -> Result<(), VirErr> {
        self.layouts.size(typ, &place.span)?;
        // Source and destination storage is already accounted for.
        self.access(place, typ)?;
        Ok(())
    }

    /// Account for a constructor, or return None for other expressions.
    /// A destination already has storage, owned here or retained by the caller.
    pub(super) fn construction(
        &mut self,
        expr: &Expr,
        destination: bool,
    ) -> Result<Option<u64>, VirErr> {
        let fields: Vec<&Expr> = match &expr.x {
            ExprX::Ctor(name @ Dt::Path(_), variant_name, fields, None) => {
                let variant = self.layouts.struct_variant(&expr.typ, &expr.span)?;
                let TypX::Datatype(result_name, _, _) = &*expr.typ else { unreachable!() };
                if name != result_name
                    || *variant_name != variant.name
                    || fields.len() != variant.fields.len()
                {
                    return Err(unsupported(&expr.span, "this struct constructor"));
                }
                let mut names = std::collections::HashSet::new();
                for field in fields.iter() {
                    let decl =
                        variant.fields.iter().find(|f| f.name == field.name).ok_or_else(|| {
                            unsupported(&field.a.span, "this struct initializer field")
                        })?;
                    if !names.insert(field.name.clone())
                        || !crate::ast_util::types_equal(&decl.a.0, &field.a.typ)
                    {
                        return Err(unsupported(
                            &field.a.span,
                            "this struct initializer field type",
                        ));
                    }
                }
                fields.iter().map(|f| &f.a).collect()
            }
            ExprX::Ctor(_, _, _, Some(_)) => {
                return Err(unsupported(&expr.span, "struct update syntax"));
            }
            ExprX::ArrayLiteral(elements) => elements.iter().collect(),
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
                args,
                post_args: None,
                body: None,
            } if attrs.resource_intrinsic == Some(ResourceIntrinsic::ArrayRepeat)
                && args.len() == 1 =>
            {
                // Only source array-repeat syntax receives this provenance.
                // Evaluate the repeated value even for a zero-length array.
                args.iter().collect()
            }
            _ => return Ok(None),
        };
        let bytes = self.layouts.size(&expr.typ, &expr.span)?;
        if !destination {
            self.storage.reserve(&expr.span, bytes, "aggregate expression result")?;
        }
        for field in fields {
            self.initialize_expr(field)?;
        }
        Ok(Some(if destination { 0 } else { bytes }))
    }
}
