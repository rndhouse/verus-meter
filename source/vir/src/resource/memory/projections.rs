//! Operation-local borrows into runtime collections.
//!
//! A precise projection partitions the selected allocation subtree out of the
//! parent forest and restores its ordinary ownership shape. For incoming
//! collections this forest contains only charges introduced in the helper;
//! the caller retains the original allocations. Finishing the loan returns
//! its updated descriptors and charge. Opaque transfers remain unsupported.

use super::analysis::Analysis;
use super::model::unsupported;
use super::paths::LocalPath;
use crate::ast::*;
use crate::messages::Span;

pub(super) struct Projection {
    /// Operation-local slot used while the child is borrowed.
    location: LocalPath,
    /// Checked mutation log at loan entry; reads do not export write effects.
    revision: usize,
    /// A precise loan has already removed this subtree from the parent sum.
    path: Expr,
    /// Parent forest before detachment, used to prove preservation of siblings.
    original: Expr,
}

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
            &types[0],
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
    ) -> Result<Vec<Projection>, VirErr> {
        let mut focused = Vec::new();
        for arg in args.iter() {
            self.focus_expression(arg, span, &mut focused)?;
        }
        if !focused.is_empty() {
            for arg in args.iter() {
                self.check_projection_effects(arg)?;
            }
        }
        Ok(focused)
    }

    /// Metadata is selected before argument evaluation. Fail closed when a
    /// sibling expression could change the runtime index in that interval.
    pub(super) fn check_projection_effects(&self, value: &Expr) -> Result<(), VirErr> {
        crate::ast_visitor::expr_visitor_check(value, &mut |_, expression| {
            let effectful = match &expression.x {
                ExprX::Assign { .. } => true,
                ExprX::Call { target: CallTarget::Fun(_, fun, _, _, attrs), .. } => {
                    matches!(
                        attrs.resource_intrinsic,
                        Some(
                            ResourceIntrinsic::VecPush
                                | ResourceIntrinsic::VecPop
                                | ResourceIntrinsic::VecRemove
                        )
                    ) || self.functions.get(fun).is_some_and(|f| {
                        f.x.params.iter().any(|p| matches!(&*p.x.typ, TypX::MutRef(_)))
                    })
                }
                _ => false,
            };
            if effectful {
                Err(unsupported(
                    &expression.span,
                    "effects inside indexed operation arguments; bind the arguments first",
                ))
            } else {
                Ok(())
            }
        })
    }

    fn focus_expression(
        &mut self,
        value: &Expr,
        span: &Span,
        focused: &mut Vec<Projection>,
    ) -> Result<(), VirErr> {
        if let Some(args) = super::paths::vector_index(value) {
            self.focus_expression(&args[0], span, focused)?;
            let typ = super::paths::indexed_type(value).expect("validated indexing adapter");
            if self.layouts.owner(typ) {
                let location = super::paths::expr(value, typ).ok_or_else(|| {
                    unsupported(&value.span, "indexing an untracked collection owner")
                })?;
                self.focus_owner(
                    location,
                    typ,
                    args[1].clone(),
                    spec_value(value)?,
                    span,
                    focused,
                )?;
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
        focused: &mut Vec<Projection>,
    ) -> Result<(), VirErr> {
        match &place.x {
            PlaceX::DerefMut(base) | PlaceX::Field(_, base) => {
                self.focus_place(base, span, focused)?;
            }
            PlaceX::Index(base, index, _, BoundsCheck::Error) => {
                self.focus_place(base, span, focused)?;
                if self.layouts.owner(&place.typ) {
                    let location = super::paths::place(place, &place.typ).ok_or_else(|| {
                        unsupported(&place.span, "indexing an untracked collection owner")
                    })?;
                    self.focus_owner(
                        location,
                        &place.typ,
                        index.clone(),
                        spec_place(place)?,
                        span,
                        focused,
                    )?;
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
        index: Expr,
        value: Expr,
        span: &Span,
        focused: &mut Vec<Projection>,
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
        let elements =
            self.heap.root(name).unwrap().at(parent).unwrap().elements.as_ref().unwrap().clone();
        let precise = elements.precise
            && elements.states.values().all(|id| !self.growth.protected_elements.contains(id));
        if !precise {
            return Err(unsupported(span, "indexing a child without precise allocation metadata"));
        }
        let original = self.metadata_local(span, "loan_parent", elements.records.clone());
        let selected_path = self.metadata_path(span, spec_value(&index)?)?;
        let partition = super::metadata::operations::detach(
            span,
            elements.records.clone(),
            selected_path.clone(),
        );
        let selected = self.metadata_local(span, "element_loan", partition.selected);
        self.assert_owner_minima(span, typ, value.clone(), selected.clone(), &elements.minima)?;
        self.metadata_partition(span, elements.records.clone(), selected_path.clone());
        self.growth.before.entry(span.id).or_default().push(super::metadata::expr::assign(
            span,
            &elements.records,
            partition.remaining,
        ));
        self.set_element_records(span, &elements, false);
        let mut child = self.owner_from_metadata(
            span,
            typ,
            selected,
            elements.view,
            elements.zero_charge(&self.growth),
        )?;
        self.install_owner_minima(&mut child, &elements.minima);
        self.bind_collection_sources(span, &mut child, typ, value)?;
        let mut collections = Vec::new();
        child.visit(&mut |node| {
            if let Some(elements) = &node.elements {
                collections.push(elements.clone());
            }
        });
        for elements in collections {
            self.assert_element_minima(span, &elements, false)?;
        }
        self.heap.root_mut(name).unwrap().replace_child(path, child);
        focused.push(Projection {
            location,
            path: selected_path,
            original,
            revision: self.transitions.revision(),
        });
        Ok(())
    }

    /// Finish innermost borrows first, so arbitrarily nested runtime and fixed
    /// children use the same additive transition. Projection slots never escape
    /// the operation or appear in function summaries.
    pub(super) fn finish_projections(
        &mut self,
        span: &Span,
        focused: Vec<Projection>,
    ) -> Result<(), VirErr> {
        if focused.is_empty() {
            return Ok(());
        }
        for projection in focused.into_iter().rev() {
            let changed = self.transitions.changed_since(projection.revision, &projection.location);
            let (name, path) = projection.location;
            let child = self
                .heap
                .root_mut(&name)
                .and_then(|root| root.take_child(&path))
                .ok_or_else(|| unsupported(span, "an indexed borrow lost its owner"))?;
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
            self.return_element_loan(
                span,
                &mut elements,
                projection.original,
                projection.path,
                child,
                changed,
            )?;
            self.heap.root_mut(&name).unwrap().at_mut(parent).unwrap().elements = Some(elements);
        }
        self.record_element_updates(span)
    }
}
