//! Values begin contributing when produced. A move transfers an existing charge.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use super::model::{unit, unsupported};
use crate::ast::*;
use crate::messages::Span;

#[derive(Clone)]
pub(super) struct Value {
    pub(super) bytes: u64,
    pub(super) origins: std::collections::HashSet<u64>,
    pub(super) ids: std::collections::HashSet<u64>,
    // Origins identify earlier points where this same value already existed.
    pub(super) parameter: Option<usize>,
}

#[derive(Clone)]
pub(super) struct Profile {
    pub(super) cost: super::footprint::Footprint,
    pub(super) result: bool,
    pub(super) inputs: std::collections::HashSet<usize>,
}

impl Analysis<'_> {
    pub(super) fn fresh_value(&mut self, span: &Span, typ: &Typ) -> Result<Value, VirErr> {
        let bytes = self.layouts.size(typ, span)?;
        let id = self.storage.reserve_value(span, MemoryKind::host_local(), bytes)?;
        Ok(Value {
            bytes,
            origins: [id].into_iter().collect(),
            ids: [id].into_iter().collect(),
            parameter: None,
        })
    }

    pub(super) fn take_value(&mut self, place: &Place) -> Result<Value, VirErr> {
        let PlaceX::Local(name) = &place.x else {
            return Err(unsupported(&place.span, "moving part of a stored value"));
        };
        self.access(place, &place.typ)?;
        let mut value = self
            .slots
            .remove(name)
            .ok_or_else(|| unsupported(&place.span, "a moved or uninitialized value"))?;
        let id = self.storage.transfer_values(&value.ids, value.bytes);
        value.ids = [id].into_iter().collect();
        value.origins.insert(id);
        Ok(value)
    }

    pub(super) fn release_value(&mut self, value: Value, span: &Span) {
        self.storage.release_values(&value.ids);
        self.storage.event(span, "value lifetime ends".into());
    }

    pub(super) fn expression_value(&mut self, value: Value, span: &Span) -> Result<u64, VirErr> {
        self.storage.release_values(&value.ids);
        self.storage.reserve(span, MemoryKind::host_local(), value.bytes, "expression value")?;
        Ok(value.bytes)
    }

    pub(super) fn produce_place(
        &mut self,
        place: &Place,
        typ: &Typ,
        copy: bool,
        span: &Span,
    ) -> Result<Value, VirErr> {
        if let PlaceX::Temporary(expr) = &place.x {
            if crate::ast_util::types_equal(&expr.typ, typ) {
                return self.produce(expr);
            }
        } else if !copy && self.layouts.owner(typ) {
            let value = self.owner_value(place, typ, span)?;
            self.result_owner = Some(self.move_owner_to(place, typ)?);
            return Ok(value);
        } else if !copy && crate::ast_util::types_equal(&place.typ, typ) {
            let value = self.take_value(place)?;
            self.result_owner =
                if self.layouts.owner(typ) { Some(self.move_owner(place)?) } else { None };
            return Ok(value);
        }
        let value = self.fresh_value(span, typ)?;
        self.initialize(place, typ)?;
        Ok(value)
    }

    /// Partial moves keep the parent's inline storage until its lifetime ends.
    /// The extracted value receives a new slot, while its allocations transfer.
    fn owner_value(&mut self, place: &Place, typ: &Typ, span: &Span) -> Result<Value, VirErr> {
        if matches!(place.x, PlaceX::Local(_)) && crate::ast_util::types_equal(&place.typ, typ) {
            self.take_value(place)
        } else {
            self.access(place, typ)?;
            self.fresh_value(span, typ)
        }
    }

    pub(super) fn produce(&mut self, expr: &Expr) -> Result<Value, VirErr> {
        if unit(&expr.typ) {
            self.discard(expr)?;
            return Ok(Value {
                bytes: 0,
                origins: Default::default(),
                ids: Default::default(),
                parameter: None,
            });
        }
        match &expr.x {
            ExprX::If(cond, yes, Some(no)) => {
                return self
                    .conditional(expr, cond, yes, Some(no), true)?
                    .ok_or_else(|| unsupported(&expr.span, "missing conditional result"));
            }
            ExprX::Match(scrutinee, arms, _) => {
                self.option_match(expr, scrutinee, arms, true)?;
                return self
                    .produced
                    .take()
                    .ok_or_else(|| unsupported(&expr.span, "missing match result"));
            }
            ExprX::Block(stmts, tail) => {
                self.block_new(expr, stmts, tail)?;
                return self
                    .produced
                    .take()
                    .ok_or_else(|| unsupported(&expr.span, "a block without a produced result"));
            }
            ExprX::ReadPlace(place, kind)
                if self.layouts.owner(&expr.typ)
                    && matches!(kind.preliminary_kind, ReadKind::Move(_) | ReadKind::Unused) =>
            {
                if let PlaceX::Temporary(value) = &place.x {
                    if crate::ast_util::types_equal(&value.typ, &expr.typ) {
                        return self.produce(value);
                    }
                }
                let value = self.owner_value(place, &expr.typ, &expr.span)?;
                self.result_owner = Some(self.move_owner_to(place, &expr.typ)?);
                return Ok(value);
            }
            ExprX::ReadPlace(place, kind)
                if matches!(kind.preliminary_kind, ReadKind::Move(_) | ReadKind::Unused)
                    && crate::ast_util::types_equal(&place.typ, &expr.typ) =>
            {
                if let PlaceX::Temporary(value) = &place.x {
                    return self.produce(value);
                }
                let value = self.take_value(place)?;
                self.result_owner = if self.layouts.owner(&expr.typ) {
                    Some(self.move_owner(place)?)
                } else {
                    None
                };
                return Ok(value);
            }
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, target, _, _, _),
                ..
            } if self.budgets.contains_key(target) => {
                self.call_expr(expr, false)?;
                return self
                    .produced
                    .take()
                    .ok_or_else(|| unsupported(&expr.span, "a call without a produced result"));
            }
            _ => {}
        }
        let value = self.fresh_value(&expr.span, &expr.typ)?;
        self.initialize_expr(expr)?;
        Ok(value)
    }
}

#[derive(Clone)]
pub(super) struct BranchState {
    storage: super::accounting::Accounting,
    slots: std::collections::HashMap<VarIdent, Value>,
    heap: super::heap::Heap,
}
impl Value {
    pub(super) fn merge(&mut self, other: &Self) {
        assert_eq!(self.bytes, other.bytes);
        self.ids.extend(other.ids.iter().copied());
        self.origins.retain(|id| other.origins.contains(id));
        self.origins.extend(self.ids.iter().copied());
        if self.parameter != other.parameter {
            self.parameter = None;
        }
    }
}
impl Analysis<'_> {
    pub(super) fn branch_state(&self) -> BranchState {
        BranchState {
            storage: self.storage.clone(),
            slots: self.slots.clone(),
            heap: self.heap.clone(),
        }
    }
    pub(super) fn restore_branch(&mut self, state: &BranchState) {
        self.storage.restore_live(&state.storage);
        self.storage.set_peak(state.storage.peak());
        self.slots = state.slots.clone();
        self.heap = state.heap.clone();
        self.produced = None;
        self.result_owner = None;
    }
    pub(super) fn join_branch(&mut self, state: &BranchState) -> Result<(), VirErr> {
        self.storage.join_live(&state.storage)?;
        let mut peak = self.storage.peak();
        peak.merge(&state.storage.peak());
        self.storage.set_peak(peak);
        for (name, old) in state.heap.owners.iter().chain(state.heap.borrowed.iter()) {
            if let Some(current) = self.heap.root_mut(name) {
                old.visit_paths(&mut vec![], &mut |path, node| {
                    if let Some(elements) =
                        current.at_mut(path).and_then(|owner| owner.elements.as_mut())
                    {
                        elements.precise &= node.elements.as_ref().is_some_and(|old| old.precise);
                        if let Some(old) = &node.elements {
                            super::metadata::reservations::join_minima(
                                &old.records.span,
                                &mut elements.minima,
                                &old.minima,
                            );
                            elements.inputs.extend(old.inputs.iter().copied());
                        }
                    }
                });
            }
        }
        for (name, value) in &state.slots {
            self.slots
                .entry(name.clone())
                .and_modify(|v| v.merge(value))
                .or_insert_with(|| value.clone());
        }
        Ok(())
    }

    /// Join original lifetimes by fixed ownership role. Earlier branch peak
    /// witnesses keep their separate identities; only live exit paths switch to
    /// the conditional identity consumed by later operations and loop summaries.
    fn join_conditional_inputs(
        &mut self,
        span: &Span,
        yes: &mut BranchState,
    ) -> Result<(), VirErr> {
        if self.heap.owners.keys().collect::<std::collections::HashSet<_>>()
            != yes.heap.owners.keys().collect::<std::collections::HashSet<_>>()
        {
            return Err(unsupported(span, "branch-dependent surviving ownership slots"));
        }
        let mut joins = Vec::new();
        for (name, owner) in &yes.heap.owners {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                joins.push((name.clone(), path.clone(), node.input));
            });
        }
        for (name, owner) in &yes.heap.borrowed {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                joins.push((name.clone(), path.clone(), node.input));
            });
        }
        // Fixed child slots must also agree in both directions. A branch-local
        // subtree cannot be silently retained as though it existed on both paths.
        let mut current_paths = Vec::new();
        for (name, owner) in self.heap.owners.iter().chain(self.heap.borrowed.iter()) {
            owner.visit_paths(&mut vec![], &mut |path, _| {
                current_paths.push((name.clone(), path.clone()));
            });
        }
        if current_paths.len() != joins.len()
            || current_paths.iter().any(|(name, path)| {
                !joins.iter().any(|(other, other_path, _)| name == other && path == other_path)
            })
        {
            return Err(unsupported(span, "branch-dependent fixed ownership slots"));
        }
        let mut choices = Vec::new();
        for (name, path, input) in joins {
            let current = self
                .heap
                .root_mut(&name)
                .and_then(|owner| owner.at_mut(&path))
                .ok_or_else(|| unsupported(span, "branch-dependent fixed ownership slots"))?;
            if current.input == input {
                continue;
            }
            let other = current.input;
            let result = self.transitions.fresh_region();
            for id in input.into_iter().chain(other) {
                self.storage.release_input(id);
                yes.storage.release_input(id);
            }
            self.storage.add_input(result);
            yes.storage.add_input(result);
            current.input = Some(result);
            yes.heap.root_mut(&name).unwrap().at_mut(&path).unwrap().input = Some(result);
            choices.push(super::transfer::checked::InputChoice { yes: input, no: other, result });
        }
        if !choices.is_empty() {
            self.transitions.branches.insert(span.id, choices);
        }
        Ok(())
    }

    pub(super) fn conditional(
        &mut self,
        expr: &Expr,
        cond: &Expr,
        yes: &Expr,
        no: Option<&Expr>,
        new_value: bool,
    ) -> Result<Option<Value>, VirErr> {
        if self.layouts.owner(&expr.typ) {
            return Err(unsupported(&expr.span, "conditional heap ownership results"));
        }
        let protection = self.heap.protect_branch(self.growth.loop_depth > 0);
        self.discard(cond)?;
        let entry = self.branch_state();
        let mut result = if new_value {
            Some(self.produce(yes)?)
        } else {
            self.initialize_expr(yes)?;
            None
        };
        let mut yes_state = self.branch_state();
        self.restore_branch(&entry);
        if let Some(no) = no {
            if new_value {
                let value = self.produce(no)?;
                result.as_mut().unwrap().merge(&value);
            } else {
                self.initialize_expr(no)?;
            }
        }
        self.join_conditional_inputs(&expr.span, &mut yes_state)?;
        self.join_branch(&yes_state)?;
        self.heap.unprotect(protection);
        Ok(result)
    }
}
