//! Initializers share their destination's charge.
//!
//! This is a source-level accounting rule, independent of compiler lowering.
//! Locals, parameters, and enclosing aggregates provide initializer storage;
//! an aggregate expression without such a destination owns one result charge.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
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
        if let ExprX::ReadPlace(place, kind) = &expr.x {
            if matches!(kind.preliminary_kind, ReadKind::Move(_))
                && crate::ast_util::types_equal(&place.typ, &expr.typ)
                && matches!(place.x, PlaceX::Local(_))
            {
                let value = self.take_value(place)?;
                self.release_value(value, &expr.span);
            }
        }
        if self.layouts.owner(&expr.typ) {
            self.result_owner = Some(self.owner_expr(expr)?);
            return Ok(());
        }
        if self.value_into(expr)? {
            return Ok(());
        }
        if let Some(_) = self.vector_expr(expr)? {
            return Ok(());
        }
        if matches!(&expr.x, ExprX::Call { .. }) {
            if self.construction(expr, true)?.is_some() {
                return Ok(());
            }
            self.call_expr(expr, true)?;
            return Ok(());
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
        self.discard(expr)
    }

    fn copy_into_destination(&mut self, place: &Place, typ: &Typ) -> Result<(), VirErr> {
        self.layouts.size(typ, &place.span)?;
        // Source and destination storage is already accounted for.
        let scratch = self.read(place, typ)?;
        self.storage.release(
            &place.span,
            MemoryKind::host_local(),
            scratch,
            "source value consumed into destination",
        );
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
            ExprX::Ctor(_, variant, fields, None) if self.layouts.option(&expr.typ) => {
                let payload = self.layouts.option_payload(&expr.typ, &expr.span)?;
                match (variant.as_str(), fields.as_slice()) {
                    ("None", []) => vec![],
                    ("Some", [field]) if crate::ast_util::types_equal(&field.a.typ, payload) => {
                        vec![&field.a]
                    }
                    _ => return Err(unsupported(&expr.span, "this Option constructor")),
                }
            }
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
            self.storage.reserve(
                &expr.span,
                MemoryKind::host_local(),
                bytes,
                "aggregate expression result",
            )?;
        }
        let mut owner = super::heap::Owner::default();
        let mut transitions = Vec::new();
        for (index, field) in fields.into_iter().enumerate() {
            let mut owned_slot = None;
            self.initialize_expr(field)?;
            if self.layouts.owner(&field.typ) {
                let ExprX::Ctor(_, _, initializers, _) = &expr.x else {
                    return Err(unsupported(&field.span, "owning elements in runtime collections"));
                };
                let name = initializers[index].name.clone();
                let child = self
                    .result_owner
                    .take()
                    .ok_or_else(|| unsupported(&field.span, "an owning field without ownership"))?;
                let slot = if self.layouts.option(&expr.typ) {
                    super::heap::OwnerSlot::Contents
                } else {
                    super::heap::OwnerSlot::Field(name)
                };
                let mut child = child;
                if self.layouts.option(&expr.typ) {
                    self.freeze_owner_geometry(field, &mut child);
                }
                owned_slot = Some(slot.clone());
                owner.children.insert(slot, child);
            }
            transitions.push((field.clone(), owned_slot));
        }
        if self.layouts.owner(&expr.typ) {
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Aggregate {
                    fields: transitions,
                    tag: u64::from(self.layouts.option(&expr.typ) && !owner.children.is_empty()),
                },
            );
            if self.layouts.option(&expr.typ) {
                owner.geometry = Some(super::contracts::literal(
                    &expr.span,
                    u64::from(!owner.children.is_empty()),
                ));
            }
            if self.layouts.option(&expr.typ) && owner.children.is_empty() {
                let payload = self.layouts.option_payload(&expr.typ, &expr.span)?.clone();
                let name = VarIdent(
                    std::sync::Arc::new("$memory_none".into()),
                    VarIdentDisambiguate::VirTemp(super::accounting::Accounting::fresh_allocation()),
                );
                let mut child = self.input_owner(
                    &payload,
                    &expr.span,
                    0,
                    &name,
                    &mut vec![],
                    &Default::default(),
                )?;
                // The payload is absent, so all of its logical counts and
                // storage are zero regardless of its nested container types.
                child.visit_mut(&mut |node| {
                    node.view = super::metadata::View::Complete;
                    node.geometry = Some(super::contracts::literal(&expr.span, 0));
                    node.geometry_known = true;
                    if let Some(elements) = &mut node.elements {
                        elements.precise = true;
                        elements.view = super::metadata::View::Complete;
                    }
                });
                owner.children.insert(super::heap::OwnerSlot::Contents, child);
            }
            self.result_owner = Some(owner);
        } else if matches!(&expr.x, ExprX::Call { .. }) {
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Evaluate {
                    args: std::sync::Arc::new(
                        transitions.into_iter().map(|(field, _)| field).collect(),
                    ),
                },
            );
        }
        Ok(Some(if destination { 0 } else { bytes }))
    }
}
