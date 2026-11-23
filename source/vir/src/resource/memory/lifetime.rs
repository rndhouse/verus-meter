//! Values begin contributing when produced. A move transfers an existing charge.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use super::model::{unit, unsupported};
use crate::ast::*;
use crate::messages::Span;

#[derive(Clone, PartialEq, Eq)]
pub(super) struct Value {
    pub(super) bytes: u64,
    pub(super) origins: std::collections::HashSet<u64>,
    pub(super) ids: std::collections::HashSet<u64>,
    // Origins identify earlier points where this same value already existed.
    pub(super) parameter: Option<usize>,
    /// Identity behind an immutable reference binding, when it agrees on every path.
    pub(super) synchronization_view: Option<super::synchronization::local::View>,
    /// Capture inputs from the actual closure construction, preserved by copies
    /// and moves. Absence never authorizes rereading the parent's variables.
    pub(super) environment: Option<super::closures::observations::EnvironmentId>,
}

/// Inline value and separately owned descendants travel together across a
/// temporary, worker-entry or completion boundary. Snapshot clones do not copy
/// executable storage or increment any strong-reference count.
#[derive(Clone)]
pub(super) struct Storage {
    /// Concrete executable layout of the transferred value.
    pub(super) typ: Typ,
    /// Its existing inline charge and lifetime provenance.
    pub(super) value: Value,
    /// Owned descendants or canonical links, absent for a non-owning value.
    pub(super) owner: Option<super::heap::Owner>,
}

impl Storage {
    pub(super) fn compatible(&self, other: &Self) -> bool {
        crate::ast_util::types_equal(&self.typ, &other.typ)
            && self.value == other.value
            && match (&self.owner, &other.owner) {
                (None, None) => true,
                (Some(a), Some(b)) => super::control::compatible(a, b),
                _ => false,
            }
    }
}

impl Value {
    /// Unreachable expressions do not manufacture a value or allocation charge.
    pub(super) fn unit() -> Self {
        Self {
            bytes: 0,
            origins: Default::default(),
            ids: Default::default(),
            parameter: None,
            synchronization_view: None,
            environment: None,
        }
    }
}

#[derive(Clone)]
pub(super) struct Profile {
    /// Acquisitions on the same source path as this cost and input lifetime.
    pub(super) condition: super::synchronization::local::Condition,
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
            synchronization_view: None,
            environment: None,
        })
    }

    pub(super) fn take_value(&mut self, place: &Place) -> Result<Value, VirErr> {
        let PlaceX::Local(name) = &place.x else {
            return Err(unsupported(&place.span, "moving part of a stored value"));
        };
        self.access(place, &place.typ)?;
        if self.capture_views.contains(name) {
            // Captured fields occupy the retained environment. A source move
            // transfers descendants, while its destination has a new inline slot.
            return self.fresh_value(&place.span, &place.typ);
        }
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
        let copy = copy || self.layouts.copy_closure(typ);
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
        let environment = self.copied_environment(place, typ)?;
        let mut value = self.fresh_value(span, typ)?;
        value.environment = environment;
        if matches!(&**typ, TypX::Decorate(TypDecoration::Ref, _, _) | TypX::MutRef(_)) {
            value.synchronization_view = self.synchronization_place(place);
        }
        self.initialize(place, typ)?;
        Ok(value)
    }

    /// Partial moves keep the parent's inline storage until its lifetime ends.
    /// The extracted value receives a new slot, while its allocations transfer.
    pub(super) fn owner_value(
        &mut self,
        place: &Place,
        typ: &Typ,
        span: &Span,
    ) -> Result<Value, VirErr> {
        if matches!(place.x, PlaceX::Local(_)) && crate::ast_util::types_equal(&place.typ, typ) {
            self.take_value(place)
        } else {
            self.access(place, typ)?;
            self.fresh_value(span, typ)
        }
    }

    pub(super) fn produce(&mut self, expr: &Expr) -> Result<Value, VirErr> {
        let evaluation = self.enter_temporary_scope(expr.span.id);
        let view = match &*expr.typ {
            TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, _, _) => {
                self.synchronization_view(expr)
            }
            _ => None,
        };
        let mut result = self.produce_inner(expr)?;
        if view.is_some() {
            result.synchronization_view = view;
        }
        self.finish_temporary_scope(evaluation);
        Ok(result)
    }

    fn produce_inner(&mut self, expr: &Expr) -> Result<Value, VirErr> {
        // The mode checker enters proof/spec mode inside these constructors.
        // An executable block or call returning the same type still runs.
        if matches!(expr.x, ExprX::Ghost { alloc_wrapper: true, .. }) {
            return Ok(Value::unit());
        }
        if let Some(value) = self.extract_worker_result(expr)? {
            return Ok(value);
        }
        if let Some(value) = self.join_worker(expr)? {
            return Ok(value);
        }
        if let Some(copied) = self.copied_closure_read(expr) {
            return self.produce(&copied);
        }
        if let ExprX::UnaryOpr(UnaryOpr::LoopIsolationBoundary(_), inner) = &expr.x {
            self.record_collection_loop_header(inner);
            return self.produce(inner);
        }
        if let ExprX::NeverToAny(inner) = &expr.x {
            self.discard(inner)?;
            if self.flow.reachable {
                return Err(unsupported(
                    &expr.span,
                    "a diverging expression with reachable fallthrough",
                ));
            }
            return Ok(Value::unit());
        }
        if matches!(expr.x, ExprX::Return(_) | ExprX::BreakOrContinue { .. }) {
            self.discard(expr)?;
            return Ok(Value::unit());
        }
        if unit(&expr.typ) || matches!(&*expr.typ, TypX::Decorate(TypDecoration::Never, _, _)) {
            self.discard(expr)?;
            return Ok(Value {
                bytes: 0,
                origins: Default::default(),
                ids: Default::default(),
                parameter: None,
                synchronization_view: None,
                environment: None,
            });
        }
        match &expr.x {
            ExprX::NonSpecClosure { proof_fn_modes: None, .. } => {
                return self.capture_closure(expr);
            }
            ExprX::ReadPlace(place, kind)
                if matches!(&*expr.typ, TypX::AnonymousClosure(..))
                    && matches!(kind.preliminary_kind, ReadKind::Copy | ReadKind::UnusedCopy) =>
            {
                return self.produce_place(place, &expr.typ, true, &expr.span);
            }
            ExprX::Loop { .. } => {
                self.analyze_loop(expr)?;
                return if self.flow.reachable {
                    self.produced.take().ok_or_else(|| {
                        unsupported(&expr.span, "a loop without a produced exit value")
                    })
                } else {
                    Ok(Value::unit())
                };
            }
            ExprX::If(cond, yes, Some(no)) => {
                let result = self.conditional(expr, cond, yes, Some(no), true)?;
                return if self.flow.reachable {
                    result.ok_or_else(|| unsupported(&expr.span, "missing conditional result"))
                } else {
                    Ok(Value::unit())
                };
            }
            ExprX::Match(scrutinee, arms, _) => {
                self.option_match(expr, scrutinee, arms, true)?;
                if !self.flow.reachable {
                    return Ok(Value::unit());
                }
                return self
                    .produced
                    .take()
                    .ok_or_else(|| unsupported(&expr.span, "missing match result"));
            }
            ExprX::Block(stmts, tail) => {
                self.block_new(expr, stmts, tail)?;
                if !self.flow.reachable {
                    return Ok(Value::unit());
                }
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

/// Path-local state shared by ordinary branches and pending lexical exits.
#[derive(Clone)]
pub(super) struct BranchState {
    /// Live charges and the peak history that can precede this path.
    pub(super) storage: super::accounting::Accounting,
    /// Inline lifetimes still owned by source bindings.
    pub(super) slots: std::collections::HashMap<VarIdent, Value>,
    /// Separately allocated ownership, including borrowed proof states.
    pub(super) heap: super::heap::Heap,
    /// Whether this snapshot has an ordinary continuing path.
    pub(super) reachable: bool,
}
impl Value {
    pub(super) fn merge(&mut self, other: &Self) {
        assert_eq!(self.bytes, other.bytes);
        self.ids.extend(other.ids.iter().copied());
        self.origins.retain(|id| other.origins.contains(id));
        self.origins.extend(self.ids.iter().copied());
        if self.synchronization_view != other.synchronization_view {
            self.synchronization_view = None;
        }
        if self.parameter != other.parameter {
            self.parameter = None;
        }
        if self.environment != other.environment {
            // Numeric branch joins can remain valid while the precise capture
            // substitution is unavailable. Worker entry must reject that case.
            self.environment = None;
        }
    }
}
impl Analysis<'_> {
    pub(super) fn branch_state(&self) -> BranchState {
        BranchState {
            storage: self.storage.clone(),
            slots: self.slots.clone(),
            heap: self.heap.clone(),
            reachable: self.flow.reachable,
        }
    }
    pub(super) fn restore_branch(&mut self, state: &BranchState) {
        self.storage.restore_live(&state.storage);
        self.storage.set_peak(state.storage.peak());
        self.slots = state.slots.clone();
        self.heap = state.heap.clone();
        self.flow.reachable = state.reachable;
        self.produced = None;
        self.result_owner = None;
    }
    pub(super) fn join_branch(&mut self, span: &Span, state: &BranchState) -> Result<(), VirErr> {
        if !self.heap.shared.compatible(&state.heap.shared)
            || !self.heap.workers.compatible(&state.heap.workers)
            || !super::temporaries::compatible(&self.heap.temporaries, &state.heap.temporaries)
        {
            return Err(unsupported(
                span,
                "branch-dependent shared roots or outstanding worker ownership",
            ));
        }
        let mut roles = std::collections::BTreeMap::new();
        for (name, old) in state.heap.owners.iter().chain(&state.heap.borrowed) {
            if let Some(current) = self.heap.root(name) {
                current.align_fixed_roles(old, &mut roles);
            }
        }
        if roles.is_empty() {
            self.storage.join_live(&state.storage)?;
        } else {
            let mut incoming = state.storage.clone();
            incoming.align_owned(span, &roles)?;
            self.storage.join_live(&incoming)?;
        }
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
                            elements.references = elements.references.combine(old.references);
                            super::metadata::reservations::join_minima(
                                &old.records.span,
                                &mut elements.minima,
                                &old.minima,
                            );
                            elements.inputs.extend(old.inputs.iter().copied());
                        }
                    }
                });
                let mut incomplete_references = false;
                current.visit(&mut |owner| {
                    incomplete_references |= owner.elements.as_ref().is_some_and(|elements| {
                        elements.references != super::elements::References::None
                            && !elements.precise
                    });
                });
                if incomplete_references {
                    return Err(unsupported(
                        span,
                        "branch-dependent incomplete identity descriptors",
                    ));
                }
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
    pub(super) fn join_conditional_inputs(
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
        for (name, owner) in yes.heap.owners.iter().chain(&yes.heap.borrowed) {
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
            if !current.same_synchronization(yes.heap.root(&name).unwrap().at(&path).unwrap()) {
                return Err(unsupported(
                    span,
                    "branch-dependent synchronization owners at a continuing slot",
                ));
            }
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
        let guard_option = self.layouts.optional_guard_payload(&expr.typ).is_some();
        if self.layouts.owner(&expr.typ) && !guard_option {
            return Err(unsupported(&expr.span, "conditional heap ownership results"));
        }
        // The condition always runs before either alternative. Its completed
        // transfers belong to both paths; only conditional work needs protection.
        self.open_branch_payloads(std::iter::once(yes).chain(no).cloned(), &expr.span)?;
        self.discard(cond)?;
        let protection = self.heap.protect_branch(self.growth.loop_depth > 0);
        let entry = self.branch_state();
        let first_checkpoint = self.transitions.shared_checkpoints.len();
        let mut result = if new_value {
            Some(self.produce(yes)?)
        } else {
            self.initialize_expr(yes)?;
            None
        };
        let else_checkpoint = self.transitions.shared_checkpoints.len();
        let mut yes_state = self.branch_state();
        if !yes_state.reachable {
            result = None;
        }
        let yes_owner = self.result_owner.take();
        self.restore_branch(&entry);
        if let Some(no) = no {
            if new_value {
                let value = self.produce(no)?;
                if self.flow.reachable {
                    if let Some(result) = &mut result {
                        result.merge(&value);
                    } else {
                        result = Some(value);
                    }
                }
            } else {
                self.initialize_expr(no)?;
            }
        }
        self.guard_shared_checkpoints(cond, first_checkpoint, else_checkpoint);
        let owner = if guard_option {
            match (yes_state.reachable, self.flow.reachable) {
                (true, true) => {
                    super::control::merge_result(&expr.span, yes_owner, self.result_owner.take())?
                }
                (true, false) => yes_owner,
                _ => self.result_owner.take(),
            }
        } else {
            None
        };
        if yes_state.reachable && self.flow.reachable {
            self.join_conditional_inputs(&expr.span, &mut yes_state)?;
            self.join_branch(&expr.span, &yes_state)?;
        } else if yes_state.reachable {
            self.restore_branch(&yes_state);
        }
        self.result_owner = owner;
        self.heap.unprotect(protection);
        Ok(result)
    }
}
