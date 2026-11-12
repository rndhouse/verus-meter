//! Zero-charge geometry completes incoming views without inventing allocations.

use super::expr;
use crate::resource::memory::{analysis::Analysis, heap::Owner};
use crate::{
    ast::*,
    ast_util::{bool_typ, int_typ},
    messages::Span,
};
use std::sync::Arc;

impl Analysis<'_> {
    /// Missing local records denote untouched caller storage. Supply its logical
    /// shape with zero-byte records, before the actual charged records, so known
    /// allocation descriptors retain precedence and every charge remains once.
    pub(in super::super) fn call_metadata(
        &mut self,
        span: &Span,
        owner: &Owner,
        proofs: &mut Vec<Stmt>,
    ) -> Result<Expr, VirErr> {
        if owner.complete() {
            return Ok(self.owner_metadata(span, owner, proofs));
        }
        let Some((typ, source)) = &owner.source else {
            return Ok(self.owner_metadata(span, owner, proofs));
        };
        let shape = self.source_geometry(span, typ, source.clone())?;
        if self.growth.owner_zero_charge(owner) {
            return Ok(super::super::transfer::simplify::simplify(&shape));
        }
        let mut charged_owner = owner.clone();
        charged_owner.visit_mut(&mut |node| {
            // Descriptor-only histories can be arbitrarily long while their
            // charge stays zero. The logical source supplies those views anew.
            if node.elements.as_ref().is_some_and(|elements| elements.zero_charge(&self.growth)) {
                node.elements = None;
            }
        });
        let charged = self.owner_metadata(span, &charged_owner, proofs);
        let memory = expr::add(span, shape, charged);
        Ok(super::super::transfer::simplify::simplify(&memory))
    }

    /// Follow the structural type once; runtime children use the existing
    /// parametric generator rather than enumerating container nesting shapes.
    fn source_geometry(&self, span: &Span, typ: &Typ, source: Expr) -> Result<Expr, VirErr> {
        let value = Owner { source: Some((typ.clone(), source.clone())), ..Default::default() };
        let record = expr::operation(
            span,
            "allocated",
            vec![
                expr::path(span, []),
                expr::integer(span, 0),
                expr::integer(span, 0),
                expr::integer(span, 0),
                self.owner_length(span, &value),
            ],
            expr::record_type(),
        );
        let mut memory = expr::push(span, expr::empty(span, expr::record_type()), record);
        for (slot, child_type) in self.layouts.owned_children(typ, span)? {
            let child = if self.layouts.option(typ) {
                let TypX::Datatype(datatype, _, _) = &**typ else { unreachable!() };
                SpannedTyped::new(
                    span,
                    &child_type,
                    ExprX::UnaryOpr(
                        UnaryOpr::Field(FieldOpr {
                            datatype: datatype.clone(),
                            variant: Arc::new("Some".into()),
                            field: crate::def::positional_field_ident(0),
                            get_variant: true,
                            check: VariantCheck::None,
                        }),
                        source.clone(),
                    ),
                )
            } else {
                self.fixed_value(span, typ, source.clone(), &slot, &child_type)?
            };
            let child = self.source_geometry(span, &child_type, child)?;
            let child =
                expr::prefix(span, child, expr::path(span, [self.layouts.metadata_slot(&slot)]));
            let child = if self.layouts.option(typ) {
                let TypX::Datatype(datatype, _, _) = &**typ else { unreachable!() };
                let present = SpannedTyped::new(
                    span,
                    &bool_typ(),
                    ExprX::UnaryOpr(
                        UnaryOpr::IsVariant {
                            datatype: datatype.clone(),
                            variant: Arc::new("Some".into()),
                        },
                        source.clone(),
                    ),
                );
                SpannedTyped::new(
                    span,
                    &expr::memory_type(),
                    ExprX::If(present, child, Some(expr::empty(span, expr::record_type()))),
                )
            } else {
                child
            };
            memory = expr::add(span, memory, child);
        }
        if self.layouts.owning_elements(typ) {
            let name = VarIdent(
                Arc::new("$memory_geometry_index".into()),
                VarIdentDisambiguate::VirTemp(
                    super::super::accounting::Accounting::fresh_allocation(),
                ),
            );
            let index = SpannedTyped::new(span, &int_typ(), ExprX::Var(name.clone()));
            let (child_type, child, length) = self.runtime_value(span, typ, source, index);
            let body = self.source_geometry(span, &child_type, child)?;
            let body = expr::prefix(span, body, expr::path(span, [0]));
            let builder = SpannedTyped::new(
                span,
                &Arc::new(TypX::SpecFn(Arc::new(vec![int_typ()]), expr::memory_type())),
                ExprX::Closure(Arc::new(vec![Arc::new(VarBinderX { name, a: int_typ() })]), body),
            );
            let generated = expr::operation(
                span,
                "generate_children",
                vec![
                    builder,
                    expr::integer(span, 1),
                    SpannedTyped::new(span, &int_typ(), length.x.clone()),
                    expr::integer(span, 0),
                ],
                expr::memory_type(),
            );
            memory = expr::add(span, memory, generated);
        }
        Ok(memory)
    }
}
