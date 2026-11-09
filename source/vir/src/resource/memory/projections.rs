//! Operation-local borrows into runtime collections.
//!
//! The aggregate retains all existing child charges. A projection mirrors the
//! selected child's ownership shape with zero original charges, just like a
//! borrowed function input. Operations use the ordinary owner machinery; their
//! newly retained allocations are then added to the aggregate. This deliberately
//! gives no credit for the selected child's old storage: aggregate summaries do
//! not yet describe an individual element's allocations or spare capacity.

use super::analysis::Analysis;
use super::heap::Owner;
use super::model::unsupported;
use super::paths::LocalPath;
use crate::ast::*;
use crate::messages::Span;

/// Read an executable projection as a pure value. In particular, do not repeat
/// an executable indexing call or its bounds assertion inside a memory formula.
/// Rust's original operation remains responsible for checking the index.
pub(super) fn spec_value(value: &Expr) -> Result<Expr, VirErr> {
    if let Some(args) = super::paths::vector_index(value) {
        let ExprX::Call { target: CallTarget::Fun(_, _, types, _, _), .. } = &value.x else {
            unreachable!()
        };
        return Ok(SpannedTyped::new(
            &value.span,
            super::paths::referent(&value.typ),
            ExprX::Call {
                target: CallTarget::Fun(
                    CallTargetKind::Static,
                    crate::fun!(CrateId::Vstd => "std_specs", "vec"; "spec_vec_index"),
                    types.clone(),
                    std::sync::Arc::new(vec![]),
                    CallTargetAttrs {
                        resource_intrinsic: None,
                        autospec: AutospecUsage::Final,
                        const_var: false,
                        assume_external_allowed: false,
                    },
                ),
                args: std::sync::Arc::new(vec![spec_value(&args[0])?, spec_value(&args[1])?]),
                post_args: None,
                body: None,
            },
        ));
    }
    let x = match &value.x {
        ExprX::ReadPlace(place, _) | ExprX::BorrowMut(place) | ExprX::TwoPhaseBorrowMut(place) => {
            return spec_place(place);
        }
        ExprX::Const(_) | ExprX::Var(_) => return Ok(value.clone()),
        ExprX::Unary(op, inner) => ExprX::Unary(*op, spec_value(inner)?),
        ExprX::Binary(op, left, right) => {
            // Preserve values (including explicit truncation), while leaving
            // overflow checks on the original executable index.
            let op = match op {
                BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Error(_))) => {
                    BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow))
                }
                BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Error(_))) => {
                    BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Allow))
                }
                BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Error(_))) => {
                    BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Allow))
                }
                _ => *op,
            };
            ExprX::Binary(op, spec_value(left)?, spec_value(right)?)
        }
        _ => return Err(unsupported(&value.span, "an effectful indexed receiver or index")),
    };
    Ok(SpannedTyped::new(&value.span, &value.typ, x))
}

fn spec_place(place: &Place) -> Result<Expr, VirErr> {
    let x = match &place.x {
        PlaceX::Local(_) => {
            let value = crate::ast_util::place_to_spec_expr(place);
            return Ok(if let TypX::MutRef(inner) = &*place.typ {
                SpannedTyped::new(&place.span, inner, ExprX::Unary(UnaryOp::MutRefCurrent, value))
            } else {
                value
            });
        }
        PlaceX::Temporary(value) => return spec_value(value),
        PlaceX::DerefMut(base) => return spec_place(base),
        PlaceX::Field(op, base) => ExprX::UnaryOpr(UnaryOpr::Field(op.clone()), spec_place(base)?),
        PlaceX::Index(base, index, kind, _) => ExprX::Binary(
            BinaryOp::Index(*kind, BoundsCheck::Allow),
            spec_place(base)?,
            spec_value(index)?,
        ),
        _ => return Err(unsupported(&place.span, "this indexed receiver place")),
    };
    Ok(SpannedTyped::new(&place.span, &place.typ, x))
}

impl Analysis<'_> {
    pub(super) fn focus_arguments(
        &mut self,
        args: &Exprs,
        span: &Span,
    ) -> Result<Vec<LocalPath>, VirErr> {
        let mut focused = Vec::new();
        for arg in args.iter() {
            self.focus_expression(arg, span, &mut focused)?;
        }
        Ok(focused)
    }

    fn focus_expression(
        &mut self,
        value: &Expr,
        span: &Span,
        focused: &mut Vec<LocalPath>,
    ) -> Result<(), VirErr> {
        if let Some(args) = super::paths::vector_index(value) {
            self.focus_expression(&args[0], span, focused)?;
            let typ = super::paths::referent(&value.typ);
            if self.layouts.owner(typ) {
                let location = super::paths::expr(value, typ).ok_or_else(|| {
                    unsupported(&value.span, "indexing an untracked collection owner")
                })?;
                self.focus_owner(location, typ, span, focused)?;
            }
        } else {
            match &value.x {
                ExprX::ReadPlace(place, _)
                | ExprX::BorrowMut(place)
                | ExprX::TwoPhaseBorrowMut(place) => self.focus_place(place, span, focused)?,
                _ => {}
            }
        }
        Ok(())
    }

    pub(super) fn focus_place(
        &mut self,
        place: &Place,
        span: &Span,
        focused: &mut Vec<LocalPath>,
    ) -> Result<(), VirErr> {
        match &place.x {
            PlaceX::DerefMut(base) | PlaceX::Field(_, base) => {
                self.focus_place(base, span, focused)?;
            }
            PlaceX::Index(base, _, _, BoundsCheck::Error) => {
                self.focus_place(base, span, focused)?;
                if self.layouts.owner(&place.typ) {
                    let location = super::paths::place(place, &place.typ).ok_or_else(|| {
                        unsupported(&place.span, "indexing an untracked collection owner")
                    })?;
                    self.focus_owner(location, &place.typ, span, focused)?;
                }
            }
            PlaceX::Temporary(value) => self.focus_expression(value, span, focused)?,
            _ => {}
        }
        Ok(())
    }

    fn focus_owner(
        &mut self,
        location: LocalPath,
        typ: &Typ,
        span: &Span,
        focused: &mut Vec<LocalPath>,
    ) -> Result<(), VirErr> {
        let (name, path) = &location;
        if self.heap.root(name).and_then(|root| root.at(path)).is_some() {
            return Ok(());
        }
        let (_, parent) = path.split_last().expect("indexed child path");
        if self
            .heap
            .root(name)
            .and_then(|root| root.at(parent))
            .and_then(|owner| owner.elements.as_ref())
            .is_none()
        {
            return Err(unsupported(span, "indexing an untracked collection owner"));
        }
        self.layouts.size(typ, span)?;
        let child = self.input_owner(typ, span, 0, name, &mut vec![], &Default::default())?;
        self.heap.root_mut(name).unwrap().replace_child(path, child);
        focused.push(location);
        Ok(())
    }

    /// Finish innermost borrows first, so arbitrarily nested runtime and fixed
    /// children use the same additive transition. Projection slots never escape
    /// the operation or appear in function summaries.
    pub(super) fn finish_projections(
        &mut self,
        span: &Span,
        focused: Vec<LocalPath>,
    ) -> Result<(), VirErr> {
        if focused.is_empty() {
            return Ok(());
        }
        for (name, path) in focused.into_iter().rev() {
            let child = self
                .heap
                .root_mut(&name)
                .and_then(|root| root.take_child(&path))
                .ok_or_else(|| unsupported(span, "an indexed borrow lost its owner"))?;
            if !self.projection_changed(&child) {
                self.release_owner_storage(child, span, false);
                continue;
            }
            let (_, parent) = path.split_last().unwrap();
            let mut elements = self
                .heap
                .root_mut(&name)
                .unwrap()
                .at_mut(parent)
                .unwrap()
                .elements
                .take()
                .expect("collection state");
            self.merge_projected_child(span, &mut elements, child)?;
            self.heap.root_mut(&name).unwrap().at_mut(parent).unwrap().elements = Some(elements);
        }
        self.record_element_updates(span)
    }

    fn projection_changed(&self, child: &Owner) -> bool {
        let mut changed = !child.inputs().is_empty();
        child.visit(&mut |node| {
            changed |= node.bytes != 0 || node.extent.is_some();
            if let Some(id) = node.vector {
                changed |= self.growth.vectors[id].backing.changed;
            } else {
                changed |= node.dynamic.is_some();
            }
            if let Some(elements) = &node.elements {
                changed |= elements.states.values().any(|id| self.growth.elements[*id].changed);
            }
        });
        changed
    }
}
