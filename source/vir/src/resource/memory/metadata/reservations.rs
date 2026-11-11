//! Uniform facts describe ownership classes: fixed steps select a field or box
//! payload, and a repeated step ranges over every live runtime child. Candidates
//! are inferred from insertions and proved as ordinary loop invariants.

use super::super::{
    analysis::Analysis,
    contracts,
    elements::Elements,
    heap::{Owner, OwnerSlot},
    model::unsupported,
};
use super::expr;
use crate::ast::*;
use crate::ast_util::{bool_typ, conjoin, int_typ, mk_implies, mk_ineq};
use crate::messages::Span;
use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(in super::super) enum Step {
    Fixed(OwnerSlot),
    Repeated,
}

#[derive(Clone)]
pub(in super::super) struct Floor {
    /// Guaranteed reserved slots for every owner in this class.
    pub(in super::super) capacity: Expr,
    /// Inline bytes per element, independent of its separately owned children.
    pub(in super::super) element: u64,
}

pub(in super::super) type Minima = BTreeMap<Vec<Step>, Floor>;

pub(in super::super) fn join_minima(span: &Span, left: &mut Minima, right: &Minima) {
    for (path, floor) in right {
        left.entry(path.clone())
            .and_modify(|old| {
                old.capacity = match (
                    contracts::constant(&old.capacity),
                    contracts::constant(&floor.capacity),
                ) {
                    (Some(left), Some(right)) => contracts::literal(span, left.min(right)),
                    (Some(0), _) | (_, Some(0)) => contracts::literal(span, 0),
                    _ if Arc::ptr_eq(&old.capacity, &floor.capacity) => old.capacity.clone(),
                    _ => super::super::growth::select(
                        span,
                        mk_ineq(span, &old.capacity, &floor.capacity, InequalityOp::Le),
                        old.capacity.clone(),
                        floor.capacity.clone(),
                    ),
                };
            })
            .or_insert_with(|| floor.clone());
    }
}

impl Analysis<'_> {
    pub(in super::super) fn owner_minima(
        &self,
        owner: &Owner,
        path: &mut Vec<Step>,
        result: &mut Minima,
    ) {
        if let Some(id) = owner.vector {
            let state = &self.growth.vectors[id];
            result.insert(
                path.clone(),
                Floor {
                    capacity: state
                        .uniform_minimum
                        .clone()
                        .unwrap_or_else(|| state.minimum.clone()),
                    element: state.element,
                },
            );
        }
        for (slot, child) in &owner.children {
            if matches!(slot, OwnerSlot::Element(_)) {
                continue;
            }
            path.push(Step::Fixed(slot.clone()));
            self.owner_minima(child, path, result);
            path.pop();
        }
        if let Some(elements) = &owner.elements {
            for (child, floor) in &elements.minima {
                let key = path
                    .iter()
                    .cloned()
                    .chain([Step::Repeated])
                    .chain(child.iter().cloned())
                    .collect();
                result.insert(key, floor.clone());
            }
        }
    }

    pub(in super::super) fn merge_element_minima(
        &self,
        span: &Span,
        elements: &mut Elements,
        child: &Owner,
    ) {
        // Updating one incoming child establishes no uniform reservation for
        // its untouched siblings. Per-child lower bounds remain in the records.
        if elements.view == super::View::Local {
            return;
        }
        let mut minima = BTreeMap::new();
        self.owner_minima(child, &mut vec![], &mut minima);
        join_minima(span, &mut elements.minima, &minima);
    }

    /// Restore class candidates on a selected owner. Loop and reusable-loan
    /// boundaries check them against the actual allocation metadata.
    pub(in super::super) fn install_owner_minima(&mut self, owner: &mut Owner, minima: &Minima) {
        if let (Some(id), Some(floor)) = (owner.vector, minima.get(&vec![])) {
            self.growth.vectors[id].uniform_minimum = Some(floor.capacity.clone());
        }
        if let Some(elements) = &mut owner.elements {
            elements.minima = minima
                .iter()
                .filter(|(path, _)| matches!(path.first(), Some(Step::Repeated)))
                .map(|(path, floor)| (path[1..].to_vec(), floor.clone()))
                .collect();
        }
        for (slot, child) in &mut owner.children {
            let selected = minima
                .iter()
                .filter(|(path, _)| path.first() == Some(&Step::Fixed(slot.clone())))
                .map(|(path, floor)| (path[1..].to_vec(), floor.clone()))
                .collect();
            self.install_owner_minima(child, &selected);
        }
    }

    fn usable_floor(&self, floor: &Floor) -> bool {
        if contracts::constant(&floor.capacity) == Some(0) {
            return false;
        }
        let mut in_scope = true;
        let _ = crate::ast_visitor::expr_visitor_check(&floor.capacity, &mut |_, value| {
            if let ExprX::Var(name) = &value.x {
                in_scope &= self.slots.contains_key(name);
            }
            Ok::<(), VirErr>(())
        });
        in_scope
    }

    fn check_reservation(&mut self, span: &Span, value: Expr, after: bool) {
        let assertion = SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::AssertAssume {
                is_assume: false,
                expr: value,
                msg: Some(crate::messages::error(
                    span,
                    if after {
                        "cannot preserve inferred child reservation after this operation"
                    } else {
                        "cannot establish inferred child reservation before this operation"
                    },
                )),
            },
        );
        let statement = crate::def::Spanned::new(span.clone(), StmtX::Expr(assertion));
        let schedule = if after { &mut self.growth.after } else { &mut self.growth.before };
        schedule.entry(span.id).or_default().push(statement);
    }

    pub(in super::super) fn assert_owner_minima(
        &mut self,
        span: &Span,
        typ: &Typ,
        value: Expr,
        memory: Expr,
        minima: &Minima,
    ) -> Result<(), VirErr> {
        if self.growth.loop_depth == 0 {
            return Ok(());
        }
        for (path, floor) in minima {
            if self.usable_floor(floor) {
                let fact =
                    self.reservation(span, typ, value.clone(), memory.clone(), path, floor)?;
                self.check_reservation(span, fact, false);
            }
        }
        Ok(())
    }

    pub(in super::super) fn assert_element_minima(
        &mut self,
        span: &Span,
        elements: &Elements,
        after: bool,
    ) -> Result<(), VirErr> {
        if !elements.precise || self.growth.loop_depth == 0 {
            return Ok(());
        }
        let Some((typ, value)) = &elements.source else {
            return Ok(());
        };
        for (path, floor) in &elements.minima {
            if self.usable_floor(floor) {
                let fact = self.repeated_reservation(
                    span,
                    typ,
                    value.clone(),
                    elements.records.clone(),
                    path,
                    floor,
                )?;
                self.check_reservation(span, fact, after);
            }
        }
        Ok(())
    }

    pub(in super::super) fn bind_collection_sources(
        &self,
        span: &Span,
        owner: &mut Owner,
        typ: &Typ,
        value: Expr,
    ) -> Result<(), VirErr> {
        let value = as_value(span, value);
        owner.source = Some((typ.clone(), value.clone()));
        if let Some(elements) = &mut owner.elements {
            elements.source = Some((typ.clone(), value.clone()));
        }
        if self.layouts.option(typ) {
            return Ok(());
        }
        for (slot, child_type) in self.layouts.owned_children(typ, span)? {
            if let Some(child) = owner.children.get_mut(&slot) {
                let selected = self.fixed_value(span, typ, value.clone(), &slot, &child_type)?;
                self.bind_collection_sources(span, child, &child_type, selected)?;
            }
        }
        Ok(())
    }

    fn fixed_value(
        &self,
        span: &Span,
        typ: &Typ,
        value: Expr,
        slot: &OwnerSlot,
        child: &Typ,
    ) -> Result<Expr, VirErr> {
        match slot {
            OwnerSlot::Contents => Ok(SpannedTyped::new(span, child, value.x.clone())),
            OwnerSlot::Field(name) => {
                let variant = self.layouts.struct_variant(typ, span)?;
                let TypX::Datatype(datatype, _, _) = &**typ else { unreachable!() };
                Ok(SpannedTyped::new(
                    span,
                    child,
                    ExprX::UnaryOpr(
                        UnaryOpr::Field(FieldOpr {
                            datatype: datatype.clone(),
                            variant: variant.name.clone(),
                            field: name.clone(),
                            get_variant: false,
                            check: VariantCheck::None,
                        }),
                        value,
                    ),
                ))
            }
            OwnerSlot::Element(_) => {
                Err(unsupported(span, "a runtime index used as a fixed reservation path"))
            }
        }
    }

    pub(in super::super) fn element_reservation_invariants(
        &self,
        span: &Span,
        allowed: &HashSet<VarIdent>,
    ) -> Result<Vec<Expr>, VirErr> {
        let mut result = Vec::new();
        for owner in self.heap.owners.values().chain(self.heap.borrowed.values()) {
            let mut collections = Vec::new();
            owner.visit(&mut |node| {
                if let Some(elements) = &node.elements {
                    if elements.precise && elements.source.is_some() {
                        collections.push(elements.clone());
                    }
                }
            });
            for elements in collections {
                let (typ, value) = elements.source.as_ref().unwrap();
                for (path, floor) in &elements.minima {
                    let mut in_scope = true;
                    crate::ast_visitor::expr_visitor_check(&floor.capacity, &mut |_, value| {
                        if let ExprX::Var(name) = &value.x {
                            in_scope &= allowed.contains(name) && self.slots.contains_key(name);
                        }
                        Ok::<(), VirErr>(())
                    })?;
                    if in_scope && contracts::constant(&floor.capacity) != Some(0) {
                        result.push(self.repeated_reservation(
                            span,
                            typ,
                            value.clone(),
                            elements.records.clone(),
                            path,
                            floor,
                        )?);
                    }
                }
            }
        }
        Ok(result)
    }

    fn reservation(
        &self,
        span: &Span,
        typ: &Typ,
        value: Expr,
        memory: Expr,
        path: &[Step],
        floor: &Floor,
    ) -> Result<Expr, VirErr> {
        match path.split_first() {
            None => {
                let record = expr::lookup(span, memory, expr::path(span, []));
                Ok(conjoin(
                    span,
                    &vec![
                        crate::ast_util::mk_eq(
                            span,
                            &expr::record_field(span, record.clone(), "kind"),
                            &contracts::literal(span, 0),
                        ),
                        mk_ineq(
                            span,
                            &floor.capacity,
                            &expr::record_field(span, record.clone(), "capacity"),
                            InequalityOp::Le,
                        ),
                        mk_ineq(
                            span,
                            &contracts::multiply(
                                span,
                                floor.capacity.clone(),
                                contracts::literal(span, floor.element),
                            ),
                            &expr::record_field(span, record, "bytes"),
                            InequalityOp::Le,
                        ),
                    ],
                ))
            }
            Some((Step::Fixed(slot), rest)) => {
                if self.layouts.option(typ) {
                    return Ok(crate::ast_util::mk_bool(span, true));
                }
                let children = self.layouts.owned_children(typ, span)?;
                let child = children.get(slot).cloned().ok_or_else(|| {
                    unsupported(span, "a reservation path outside the owner's structural layout")
                })?;
                let value = self.fixed_value(span, typ, value, slot, &child)?;
                let memory = expr::subtree(
                    span,
                    memory,
                    expr::path(span, [self.layouts.metadata_slot(slot)]),
                );
                self.reservation(span, &child, value, memory, rest, floor)
            }
            Some((Step::Repeated, rest)) => {
                self.repeated_reservation(span, typ, value, memory, rest, floor)
            }
        }
    }

    fn repeated_reservation(
        &self,
        span: &Span,
        typ: &Typ,
        value: Expr,
        records: Expr,
        path: &[Step],
        floor: &Floor,
    ) -> Result<Expr, VirErr> {
        let name = VarIdent(
            Arc::new("$memory_child_index".into()),
            VarIdentDisambiguate::VirTemp(super::super::accounting::Accounting::fresh_allocation()),
        );
        let index = SpannedTyped::new(span, &int_typ(), ExprX::Var(name.clone()));
        let value = as_value(span, value);
        let (child_type, selected, length) = if self.layouts.vector(typ) {
            let TypX::Datatype(_, types, _) = &**typ else { unreachable!() };
            let length = super::super::vectors::length(span, types.clone(), value.clone());
            let selected = SpannedTyped::new(
                span,
                &types[0],
                ExprX::Call {
                    target: CallTarget::Fun(
                        CallTargetKind::Static,
                        crate::fun!(CrateId::Vstd => "std_specs", "vec"; "spec_vec_index"),
                        types.clone(),
                        Arc::new(vec![]),
                        CallTargetAttrs {
                            autospec: AutospecUsage::Final,
                            const_var: false,
                            assume_external_allowed: false,
                            resource_intrinsic: None,
                        },
                    ),
                    args: Arc::new(vec![value, index.clone()]),
                    post_args: None,
                    body: None,
                },
            );
            (types[0].clone(), selected, length)
        } else {
            let TypX::Decorate(TypDecoration::Box, _, slice) = &**typ else { unreachable!() };
            let TypX::Primitive(Primitive::Slice, types) = &**slice else { unreachable!() };
            let value = SpannedTyped::new(span, slice, value.x.clone());
            let length = SpannedTyped::new(
                span,
                &int_typ(),
                ExprX::Unary(UnaryOp::Length(ArrayKind::Slice), value.clone()),
            );
            let selected = SpannedTyped::new(
                span,
                &types[0],
                ExprX::Binary(
                    BinaryOp::Index(ArrayKind::Slice, BoundsCheck::Allow),
                    value,
                    index.clone(),
                ),
            );
            (types[0].clone(), selected, length)
        };
        let length = SpannedTyped::new(span, &int_typ(), length.x.clone());
        let memory =
            expr::subtree(span, records, expr::push(span, expr::path(span, []), index.clone()));
        let body = self.reservation(span, &child_type, selected, memory.clone(), path, floor)?;
        let range = conjoin(
            span,
            &vec![
                mk_ineq(span, &contracts::literal(span, 0), &index, InequalityOp::Le),
                mk_ineq(span, &index, &length, InequalityOp::Lt),
            ],
        );
        // One ownership class can cross several runtime collections. Quantify
        // its indices together and trigger on the complete leaf selection;
        // instantiating an outer quantifier merely to introduce another
        // quantified metadata view creates excessive matching in deep loops.
        let mut binders = vec![Arc::new(VarBinderX { name, a: int_typ() })];
        let (body, triggers) = if let ExprX::Quant(quantifier, inner_binders, inner) = &body.x {
            if *quantifier == crate::ast_util::QUANT_FORALL {
                if let ExprX::WithTriggers { triggers, body } = &inner.x {
                    binders.extend(inner_binders.iter().cloned());
                    (body.clone(), triggers.clone())
                } else {
                    (body.clone(), Arc::new(vec![Arc::new(vec![memory])]))
                }
            } else {
                (body.clone(), Arc::new(vec![Arc::new(vec![memory])]))
            }
        } else {
            (body.clone(), Arc::new(vec![Arc::new(vec![memory])]))
        };
        let body = SpannedTyped::new(
            span,
            &bool_typ(),
            ExprX::WithTriggers { triggers, body: mk_implies(span, &range, &body) },
        );
        Ok(SpannedTyped::new(
            span,
            &bool_typ(),
            ExprX::Quant(crate::ast_util::QUANT_FORALL, Arc::new(binders), body),
        ))
    }
}

fn as_value(span: &Span, value: Expr) -> Expr {
    match &*value.typ {
        TypX::MutRef(inner) => {
            SpannedTyped::new(span, inner, ExprX::Unary(UnaryOp::MutRefCurrent, value.clone()))
        }
        TypX::Decorate(TypDecoration::Ref, None, inner) => {
            SpannedTyped::new(span, inner, value.x.clone())
        }
        _ => value,
    }
}
