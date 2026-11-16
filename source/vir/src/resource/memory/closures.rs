//! Executable closure construction transfers fields, not the closure body.
//!
//! Runtime capture information comes from rustc after proof erasure. In
//! particular, free variables mentioned only in specifications do not become
//! runtime fields, and a partial capture does not consume its enclosing owner.

use super::{
    analysis::Analysis,
    concurrency::{Capture, CaptureMode},
    heap::{Owner, OwnerSlot},
    lifetime::Value,
    model::unsupported,
    synchronization::flow::Projection,
};
use crate::ast::*;
use crate::messages::Span;
use std::collections::HashMap;

/// Only executed closure creation requires capture evidence. Merely mentioning
/// closure types in specifications does not query lifetime MIR.
pub(super) fn needs_evidence(function: &Function, modes: &HashMap<VarIdent, Mode>) -> bool {
    use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
    struct Find<'a> {
        found: bool,
        modes: &'a HashMap<VarIdent, Mode>,
    }
    impl AstVisitor<Walk, (), NoScoper> for Find<'_> {
        fn visit_expr(&mut self, expr: &Expr) -> Result<(), ()> {
            if super::execution::ignored_expression(expr) {
                return Ok(());
            }
            if matches!(expr.x, ExprX::NonSpecClosure { proof_fn_modes: None, .. }) {
                self.found = true;
                return Ok(());
            }
            self.visit_expr_rec(expr)
        }
        fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), ()> {
            if super::execution::ignored_statement(stmt, self.modes) {
                Ok(())
            } else {
                self.visit_stmt_rec(stmt)
            }
        }
        fn visit_place(&mut self, place: &Place) -> Result<(), ()> {
            self.visit_place_rec(place)
        }
        fn visit_typ(&mut self, _: &Typ) -> Result<(), ()> {
            Ok(())
        }
        fn visit_pattern(&mut self, _: &Pattern) -> Result<(), ()> {
            Ok(())
        }
    }
    let mut find = Find { found: false, modes };
    if let Some(body) = &function.x.body {
        let _ = find.visit_expr(body);
    }
    find.found
}

impl Analysis<'_> {
    /// Executable capture erasure can make an originally non-Copy closure Copy.
    /// Normalize only the private accounting read, preserving its source site.
    pub(super) fn copied_closure_read(&self, expr: &Expr) -> Option<Expr> {
        let ExprX::ReadPlace(place, kind) = &expr.x else { return None };
        if !self.layouts.copy_closure(&expr.typ) {
            return None;
        }
        let preliminary_kind = match kind.preliminary_kind {
            ReadKind::Move(_) => ReadKind::Copy,
            ReadKind::Unused => ReadKind::UnusedCopy,
            _ => return None,
        };
        Some(SpannedTyped::new(
            &expr.span,
            &expr.typ,
            ExprX::ReadPlace(place.clone(), UnfinalizedReadKind { preliminary_kind, id: kind.id }),
        ))
    }
    /// Translate a compiler capture path using the same typed places and fixed
    /// ownership paths as ordinary source moves. Immutable dereferences remain
    /// implicit in VIR; field selection retains the real enclosing root type.
    fn capture_place(&self, capture: &Capture, span: &Span) -> Result<Place, VirErr> {
        let mut place =
            SpannedTyped::new(span, &capture.source_typ, PlaceX::Local(capture.source.clone()));
        let mut typ = capture.source_typ.clone();
        for projection in &capture.projection {
            match projection {
                Projection::Deref => {
                    let TypX::Decorate(TypDecoration::Ref | TypDecoration::Box, _, inner) = &*typ
                    else {
                        return Err(unsupported(span, "this executable capture dereference"));
                    };
                    typ = inner.clone();
                }
                Projection::Field(index) => {
                    let variant = self.layouts.struct_variant(&typ, span)?;
                    let field = variant.fields.get(*index).ok_or_else(|| {
                        unsupported(
                            span,
                            "an executable capture outside its enclosing field layout",
                        )
                    })?;
                    if field.a.1 != Mode::Exec {
                        return Err(unsupported(span, "a runtime capture of an erased field"));
                    }
                    let TypX::Datatype(datatype, _, _) = &*typ else { unreachable!() };
                    place = SpannedTyped::new(
                        span,
                        &field.a.0,
                        PlaceX::Field(
                            FieldOpr {
                                datatype: datatype.clone(),
                                variant: variant.name.clone(),
                                field: field.name.clone(),
                                get_variant: false,
                                check: VariantCheck::None,
                            },
                            place,
                        ),
                    );
                    typ = field.a.0.clone();
                }
                Projection::Variant(_) => {
                    return Err(unsupported(
                        span,
                        "an enum-variant capture without an established active ownership variant",
                    ));
                }
            }
        }
        if !crate::ast_util::types_equal(&typ, &capture.typ) {
            return Err(unsupported(span, "an executable capture with inconsistent source types"));
        }
        Ok(place)
    }

    /// Form one source value from captured fields. Moved inline values keep
    /// their charge and separately owned descendants; copied fields create only
    /// their own inline storage. No worker or helper body runs at construction.
    pub(super) fn capture_closure(&mut self, expr: &Expr) -> Result<Value, VirErr> {
        let TypX::AnonymousClosure(_, _, _, id) = &*expr.typ else {
            return Err(unsupported(&expr.span, "a closure without a concrete compiler identity"));
        };
        let closure = self.concurrency.closures.get(id).ok_or_else(|| {
            unsupported(&expr.span, "a closure without post-erasure capture information")
        })?;
        if !closure.by_move || closure.captures.iter().any(|c| c.mode == CaptureMode::Borrow) {
            return Err(unsupported(&expr.span, "borrowed or non-move executable closures"));
        }
        let bytes = self.layouts.size(&expr.typ, &expr.span)?;
        let copy = self.layouts.copy_closure(&expr.typ);
        let captures = closure.captures.clone();
        let mut owner = Owner { closure: Some(*id), ..Default::default() };
        let mut values = Vec::new();
        let mut checked = Vec::new();
        for (index, capture) in captures.iter().enumerate() {
            let place = self.capture_place(capture, &expr.span)?;
            let owns = self.layouts.owner(&capture.typ);
            let mode = if self.layouts.copy_closure(&capture.typ) {
                CaptureMode::Copy
            } else {
                capture.mode
            };
            let value = match mode {
                CaptureMode::Move if owns => {
                    let value = self.owner_value(&place, &capture.typ, &expr.span)?;
                    let child = self.capture_owner(&place, &capture.typ)?;
                    owner.children.insert(OwnerSlot::Capture(index), child);
                    value
                }
                CaptureMode::Copy if owns => {
                    return Err(unsupported(&expr.span, "copying an owning executable capture"));
                }
                mode => {
                    self.produce_place(&place, &capture.typ, mode == CaptureMode::Copy, &expr.span)?
                }
            };
            let location = super::paths::place(&place, &capture.typ).ok_or_else(|| {
                unsupported(&expr.span, "a capture without a fixed source ownership path")
            })?;
            checked.push((
                mode,
                super::transfer::checked::Place {
                    source: SpannedTyped::new(
                        &expr.span,
                        &capture.typ,
                        ExprX::ReadPlace(
                            place,
                            UnfinalizedReadKind { preliminary_kind: ReadKind::Copy, id: 0 },
                        ),
                    ),
                    typ: capture.typ.clone(),
                    location,
                },
            ));
            values.push(value);
        }
        let fields: Vec<_> = values.iter().map(|value| (&value.ids, value.bytes)).collect();
        let id = self.storage.pack_values(&fields, bytes);
        let mut origins = values
            .iter()
            .flat_map(|value| value.origins.iter().copied())
            .collect::<std::collections::HashSet<_>>();
        origins.insert(id);
        if copy {
            assert!(owner.children.is_empty(), "a Copy closure cannot copy owning fields");
            self.result_owner = None;
        } else {
            self.result_owner = Some(owner);
        }
        self.transitions.operation(
            &expr.span,
            super::transfer::checked::Operation::Closure { captures: checked },
        );
        self.storage
            .event(&expr.span, "construct executable closure; transfer capture ownership".into());
        Ok(Value { bytes, ids: [id].into_iter().collect(), origins, parameter: None })
    }
}
