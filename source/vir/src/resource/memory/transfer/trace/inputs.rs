//! Build parameter-relative forests, reservation minima, and completeness symbols.
//!
//! Fixed descriptors stay explicit; runtime children retain their symbolic
//! forests. Local charge views do not establish physical backing capacity.

use super::*;
use crate::resource::memory::accounting;

impl Trace<'_> {
    /// Fixed ownership is finite even when runtime children have unbounded
    /// depth. Keep the fixed descriptors explicit so composing helpers does
    /// not repeatedly select scalar properties from an opaque whole forest.
    pub(super) fn input_memory(
        &mut self,
        span: &Span,
        parameter: usize,
        typ: &Typ,
        forest: &Expr,
        path: &mut Vec<OwnerSlot>,
    ) -> Option<Expr> {
        let mut property =
            |field| self.symbol(span, Input::Property(parameter, path.clone(), field), int_typ());
        let bytes = property("bytes");
        let capacity = property("capacity");
        let length = property("length");
        let mut memory = expr::push(
            span,
            expr::empty(span, expr::record_type()),
            allocated(span, bytes, capacity, length),
        );
        for (slot, child) in self.layouts.owned_children(typ, span).ok()? {
            path.push(slot.clone());
            let child = self.input_memory(span, parameter, &child, forest, path)?;
            path.pop();
            memory = expr::add(
                span,
                memory,
                expr::prefix(span, child, expr::path(span, [self.layouts.metadata_slot(&slot)])),
            );
        }
        if self.layouts.owning_elements(typ) {
            let selected = path.iter().fold(forest.clone(), |memory, slot| {
                expr::subtree(span, memory, expr::path(span, [self.layouts.metadata_slot(slot)]))
            });
            memory = expr::add(
                span,
                memory,
                expr::operation(span, "runtime", vec![selected], expr::memory_type()),
            );
        }
        Some(memory)
    }

    /// The same template supports full caller forests and local charge views.
    fn completeness(&mut self, span: &Span) -> Expr {
        if let Some(value) = &self.complete {
            return value.clone();
        }
        let value = self.symbol(span, Input::Complete, bool_typ());
        let ExprX::Var(name) = &value.x else { unreachable!() };
        self.proof_values.insert(name.clone(), crate::ast_util::mk_bool(span, false));
        self.complete = Some(value.clone());
        value
    }

    /// Fresh root extents are complete even when their children contain inputs.
    /// Keep view-dependent capacity branches out of fully local allocations.
    pub(super) fn complete_for(&mut self, span: &Span, values: &[Expr]) -> Expr {
        let mut partial = false;
        for value in values {
            let _ = crate::ast_visitor::expr_visitor_check(value, &mut |scope, value| {
                if let ExprX::Var(name) = &value.x {
                    if !scope.contains_key(name) {
                        partial |= crate::ast_util::types_equal(&value.typ, &expr::memory_type())
                            || self.symbols.iter().any(|symbol| {
                                &symbol.name == name
                                    && matches!(
                                        symbol.input,
                                        Input::Forest(_) | Input::Property(_, _, "bytes")
                                    )
                            });
                    }
                }
                Ok::<(), VirErr>(())
            });
        }
        if partial { self.completeness(span) } else { crate::ast_util::mk_bool(span, true) }
    }

    /// Record a fresh caller observation and return its symbolic expression.
    pub(super) fn symbol(&mut self, span: &Span, input: Input, typ: Typ) -> Expr {
        let name = VarIdent(
            Arc::new("$memory_transfer_input".into()),
            VarIdentDisambiguate::VirTemp(accounting::Accounting::fresh_allocation()),
        );
        self.symbols.push(Symbol { name: name.clone(), input });
        SpannedTyped::new(span, &typ, ExprX::Var(name))
    }

    /// Collect reservation lower bounds along fixed and repeated ownership paths.
    pub(super) fn input_minima(
        &mut self,
        span: &Span,
        parameter: usize,
        typ: &Typ,
        path: &mut Vec<Step>,
        result: &mut Minima,
    ) -> Option<()> {
        if self.layouts.vector(typ) {
            let capacity = self.symbol(span, Input::Minimum(parameter, path.clone()), int_typ());
            result.insert(
                path.clone(),
                Floor { capacity, element: self.layouts.vector_element(typ, span).ok()? },
            );
        }
        for (slot, child) in self.layouts.owned_children(typ, span).ok()? {
            path.push(Step::Fixed(slot));
            self.input_minima(span, parameter, &child, path, result)?;
            path.pop();
        }
        if let Some(child) = self.element_type(typ) {
            if self.layouts.owner(&child) {
                path.push(Step::Repeated);
                self.input_minima(span, parameter, &child, path, result)?;
                path.pop();
            }
        }
        Some(())
    }

    /// Identify the element type of the supported runtime owning collections.
    fn element_type(&self, typ: &Typ) -> Option<Typ> {
        if self.layouts.vector(typ) {
            let TypX::Datatype(_, types, _) = &**typ else {
                return None;
            };
            return types.first().cloned();
        }
        if let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            if let TypX::Primitive(Primitive::Slice, types) = &**inner {
                return types.first().cloned();
            }
        }
        None
    }
}
