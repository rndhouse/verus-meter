//! Executable synchronization parameters and normal return obligations.

use super::{
    Acquisition, Instance, LibraryType, LibraryTypes,
    local::{Interval, Owned, View},
};
use crate::{
    ast::*,
    resource::memory::{accounting::Accounting, analysis::Analysis, model::unsupported},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(in super::super) enum Parameter {
    Mutex,
    BorrowMutex,
    Guard,
    BorrowGuard,
}

fn kind<'a>(typ: &'a Typ, types: &LibraryTypes) -> Option<(LibraryType, &'a Typs)> {
    let TypX::Datatype(name, args, _) = &**typ else { return None };
    Some((*types.get(name)?, args))
}

/// Return the reviewed outer interface and the payload still subject to
/// ordinary eligibility checks. An outer mutex never licenses a nested guard.
pub(super) fn parameter<'t>(typ: &'t Typ, types: &LibraryTypes) -> Option<(Parameter, &'t Typ)> {
    let (mut inner, borrowed) = match &**typ {
        TypX::Decorate(TypDecoration::Ref, None, inner) => (inner, true),
        TypX::MutRef(inner) if matches!(kind(inner, types), Some((LibraryType::MutexGuard, _))) => {
            (inner, true)
        }
        _ => (typ, false),
    };
    if borrowed && let TypX::Decorate(TypDecoration::Arc, _, payload) = &**inner {
        if !matches!(kind(payload, types), Some((LibraryType::Mutex, _))) {
            return None;
        }
        inner = payload;
    }
    let (native, args) = kind(inner, types)?;
    let [payload] = args.as_slice() else { return None };
    let param = match (native, borrowed) {
        (LibraryType::Mutex, true) => Parameter::BorrowMutex,
        (LibraryType::Mutex, false) => Parameter::Mutex,
        (LibraryType::MutexGuard, true) => Parameter::BorrowGuard,
        (LibraryType::MutexGuard, false) => Parameter::Guard,
        _ => return None,
    };
    Some((param, payload))
}

pub(in super::super) fn parameter_type(typ: &Typ, types: &LibraryTypes) -> Option<Parameter> {
    parameter(typ, types).map(|(param, _)| param)
}

pub(in super::super) fn borrowed_view(typ: &Typ, types: &LibraryTypes) -> bool {
    matches!(parameter_type(typ, types), Some(Parameter::BorrowGuard | Parameter::BorrowMutex))
}

/// Only a native acquisition's actual result can supply its conditional owner.
pub(in super::super) fn result_payload<'t>(typ: &'t Typ, types: &LibraryTypes) -> Option<&'t Typ> {
    let (native, args) = kind(typ, types)?;
    match (native, args.as_slice()) {
        (LibraryType::Mutex | LibraryType::MutexGuard, [payload]) => Some(payload),
        (LibraryType::Result, [ok, err])
            if matches!(kind(err, types),
            Some((LibraryType::TryLockError | LibraryType::PoisonError, args))
            if matches!(args.as_slice(), [guard] if crate::ast_util::types_equal(ok, guard))) =>
        {
            match kind(ok, types)? {
                (LibraryType::MutexGuard, args) => args.first(),
                _ => None,
            }
        }
        _ => None,
    }
}

#[derive(Clone, Default)]
pub(in super::super) struct Inputs(pub(super) BTreeMap<usize, (Parameter, Owned)>);

impl Inputs {
    pub(in super::super) fn intervals(&self) -> BTreeSet<Interval> {
        self.0.values().filter_map(|(_, owner)| owner.interval()).collect()
    }

    pub(in super::super) fn has_guards(&self) -> bool {
        self.0.values().any(|(_, owner)| owner.interval().is_some())
    }

    pub(in super::super) fn owned_input(&self, index: usize) -> Option<Owned> {
        let (parameter, owner) = *self.0.get(&index)?;
        matches!(parameter, Parameter::Guard | Parameter::Mutex).then_some(owner)
    }

    /// Independently described protected trees can be updated together only
    /// if a write cannot invalidate another formal's entry snapshot.
    pub(in super::super) fn require_distinct_payloads(
        &self,
        payloads: &BTreeSet<usize>,
        modified: &BTreeSet<usize>,
    ) -> BTreeSet<(usize, usize)> {
        let mut pairs = BTreeSet::new();
        for &left in payloads {
            for &right in payloads {
                if left < right
                    && self.0.contains_key(&left)
                    && self.0.contains_key(&right)
                    && (modified.contains(&left) || modified.contains(&right))
                {
                    pairs.insert((left, right));
                }
            }
        }
        pairs
    }

    pub(in super::super) fn input_view(&self, index: usize) -> Option<View> {
        match self.0.get(&index)? {
            (Parameter::BorrowMutex, Owned::Mutex(instance)) => Some(View::Mutex(*instance)),
            (Parameter::BorrowGuard, Owned::Guard(interval)) => Some(View::Guard(*interval)),
            _ => None,
        }
    }
}

impl Analysis<'_> {
    pub(in super::super) fn bind_synchronization_inputs(&mut self, function: &Function) -> Inputs {
        let mut inputs = Inputs::default();
        for (index, formal) in
            function.x.params.iter().enumerate().filter(|(_, p)| p.x.mode == Mode::Exec)
        {
            let Some(parameter) = self.layouts.synchronization_parameter(&formal.x.typ) else {
                continue;
            };
            let instance = Instance::Input(index);
            let owner = match parameter {
                Parameter::Mutex | Parameter::BorrowMutex => Owned::Mutex(instance),
                Parameter::Guard | Parameter::BorrowGuard => {
                    let interval = Interval {
                        instance,
                        acquisition: Acquisition(Accounting::fresh_allocation()),
                    };
                    self.storage.enter_guard(interval);
                    Owned::Guard(interval)
                }
            };
            inputs.0.insert(index, (parameter, owner));
        }
        self.transitions.synchronization_inputs = inputs.clone();
        inputs
    }

    /// A guard borrow addresses the mutex's tree without owning its destructor.
    /// At modular entry a protected vector may have any legal logical length.
    /// Callers specialize the separately checked forest with their actual length.
    pub(in super::super) fn bind_protected_input(
        &mut self,
        owner: &mut crate::resource::memory::heap::Owner,
        index: usize,
        inputs: &Inputs,
        entry: &crate::messages::Span,
    ) {
        owner.synchronization = match inputs.input_view(index) {
            Some(View::Mutex(id)) => Some(Owned::Mutex(id)),
            Some(View::Guard(interval)) => Some(Owned::Mutex(interval.instance)),
            _ => inputs.owned_input(index),
        };
        if owner.mutex_instance().is_some()
            && let Some(child) =
                owner.children.get_mut(&crate::resource::memory::heap::OwnerSlot::Contents)
            && let Some(id) = child.vector
        {
            let unknown = SpannedTyped::new(
                entry,
                &std::sync::Arc::new(TypX::Int(IntRange::Nat)),
                ExprX::Nondeterministic,
            );
            let length = self.allocation_snapshot(entry, unknown);
            let initial = self.allocation_snapshot(entry, length.clone());
            child.geometry = Some(length.clone());
            child.geometry_known = true;
            self.growth.vectors[id].protected_length = Some(length);
            self.growth.vectors[id].entry_length = Some(initial);
        }
    }

    /// Rust destroys remaining owned guard parameters on each returning edge.
    /// A moved or returned guard has already left its parameter slot.
    pub(in super::super) fn drop_guard_parameters(&mut self, function: &Function, inputs: &Inputs) {
        if !inputs.0.values().any(|(kind, _)| *kind == Parameter::Guard) {
            return;
        }
        self.cleanup_edges(0, |analysis, exit| {
            for (index, param) in function.x.params.iter().enumerate().rev() {
                if matches!(inputs.owned_input(index), Some(Owned::Guard(_)))
                    && let Some(owner) = analysis.heap.owners.remove(&param.x.name)
                {
                    analysis.release_owner_after(owner, exit.unwrap_or(&function.span));
                }
            }
        });
    }

    pub(in super::super) fn finish_synchronization_interface(
        &self,
        function: &Function,
        inputs: &Inputs,
    ) -> Result<Option<Owned>, VirErr> {
        let result = self.result_owner.as_ref().and_then(|owner| owner.synchronization);
        if self.layouts.synchronization_result(&function.x.outer_ret.x.typ) && result.is_none() {
            return Err(unsupported(
                &function.span,
                "a synchronization return without its executable owner",
            ));
        }
        let borrowed = inputs
            .0
            .values()
            .filter_map(|(param, owner)| {
                (*param == Parameter::BorrowGuard).then(|| owner.interval()).flatten()
            })
            .collect();
        self.storage.check_exit_intervals(&function.span, &borrowed, result)?;
        Ok(result)
    }
}
