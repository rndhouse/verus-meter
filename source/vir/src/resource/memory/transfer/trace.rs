//! Specialize checked ownership transitions into parametric forests.
//!
//! Source syntax supplies scalar expressions and control flow. Ownership rules,
//! layout sizes, and resolved paths come exclusively from body accounting; a
//! template is exported only after every recorded transition is consumed.
//! Unrepresentable effects fail inference; runtime ownership interfaces then
//! report unsupported instead of exporting a byte-only approximation.
//!
//! This module owns trace state, summary export, and coverage validation. Input
//! modeling, checked places, expression evaluation, and branch joins live beside
//! the operation, loop, pattern, exit, and provenance adapters.

mod branches;
mod evaluation;
mod exits;
mod inputs;
mod iterators;
mod loops;
mod operations;
mod patterns;
mod places;
mod provenance;

#[cfg(test)]
mod tests;

use super::*;
use crate::ast_util::{bool_typ, int_typ, mk_eq, mk_ineq};
use crate::messages::Span;
use crate::resource::memory::{
    contracts, growth,
    heap::OwnerSlot,
    metadata::reservations::{Step, join_minima},
};
use std::collections::HashSet;
use std::sync::Arc;

use super::effects::{Effect, Location};

/// Persistent symbolic bindings and scalar definitions on one continuing path.
#[derive(Clone, Default)]
struct State {
    /// Traced values of live local and parameter bindings.
    values: HashMap<VarIdent, Value>,
    /// Pure source initializers for immutable scalar bindings. Keeping their
    /// actual definitions avoids inventing logical postconditions for callees.
    definitions: BTreeMap<VarIdent, Expr>,
    /// Owner bindings changed along this path, including borrowed parameters.
    written: HashSet<VarIdent>,
}

/// First-visit witnesses for one selected child and its optional presence.
/// Repetition substitutes both the payload forest and the per-visit tag.
#[derive(Clone)]
struct Selection {
    /// Complete physical child selected on the representative visit.
    memory: Expr,
    /// Original input region, independently of newly introduced storage.
    original: Option<(VarIdent, Expr)>,
    /// Temporary presence symbol and its first-visit zero-or-one witness.
    presence: (VarIdent, Expr),
}

/// One checked body visit and the evidence needed to export its ownership effects.
#[derive(Clone)]
struct Trace<'a> {
    /// Only a checked successful visit can specialize next to Some(item).
    active_iterator: Option<VarIdent>,
    /// Continuing path and deferred exits use the same symbolic forest states.
    reachable: bool,
    /// Guard selecting the continuing path.
    path: Expr,
    /// Detached return, break, and continue states awaiting their destination.
    exits: Vec<exits::Edge>,
    /// Supported inline layouts and ownership projections.
    layouts: &'a super::super::layout::Layouts,
    /// Function declarations used by checked call composition.
    functions: &'a HashMap<Fun, Function>,
    /// Resource and ownership summaries for resolved callees.
    summaries: &'a HashMap<Fun, super::super::summary::FunctionSummary>,
    /// Binding modes used to exclude erased proof and specification code.
    modes: &'a HashMap<VarIdent, Mode>,
    /// Authoritative operation decisions made by body accounting.
    checked: &'a Checked,
    /// Whole-body coverage, including branches and representative loop bodies.
    used: HashSet<(checked::Kind, u64)>,
    /// Persistent bindings on the current continuing path.
    state: State,
    /// Caller observations permitted as free symbols in exported templates.
    symbols: Vec<Symbol>,
    /// A local view must never infer physical capacity from zero local bytes.
    complete: Option<Expr>,
    /// Immutable allocation regions addressed by body lifetime identities.
    regions: BTreeMap<usize, Expr>,
    /// Effects on persistent owners distinguish collection regions from
    /// temporary child construction during a representative loop iteration.
    effects: Vec<Effect>,
    /// Pattern branches keep unsupported mutations opaque; `if` branches record
    /// explicit guards instead.
    branch_depth: usize,
    /// Temporary payload symbols expose data flow within one iteration. They
    /// must be eliminated by the loop summary, never exported as free symbols.
    loop_tokens: Option<HashSet<VarIdent>>,
    /// Only persistent roles need range tokens; temporary construction keeps
    /// its concrete forest so it can compose as fresh output.
    loop_roots: Option<HashSet<VarIdent>>,
    /// Concrete first-iteration witnesses close intermediate lifetime regions.
    loop_inputs: HashMap<VarIdent, Selection>,
    /// Allocation-site observations and candidate extents for this iteration.
    loop_allocations: Vec<(Span, Expr, Expr)>,
    /// Retained-growth candidates for completed nested loops, proved by the
    /// containing visit's ordinary byte induction rather than a synthetic site.
    loop_nested: Vec<Expr>,
    /// Helper workspace observations, including calls with no escaping allocation.
    loop_calls: Vec<(Span, Expr, Expr)>,
    /// Closed helper workspace ceilings for generated body headroom candidates.
    loop_scratch: HashMap<u64, Expr>,
    /// Checked allocation ceilings used to prove recurrence charge induction.
    loop_repetitions: HashMap<u64, Expr>,
    /// Invariant-proposed scalar ceiling; uses are checked at their operations.
    loop_size_ceiling: Option<Expr>,
    /// Bounds published only when the complete ownership template succeeds.
    allocation_checks: Vec<(Span, Expr)>,
    /// Structural transfers from completed loop graphs. No proof expressions
    /// are constructed here; evidence is published only with a complete template.
    loop_transfers: HashMap<u64, Vec<super::super::loops::Transfer>>,
    /// Checked visit counts and scalar/length proof candidates.
    loop_progress: HashMap<u64, super::super::loops::progress::Evidence>,
    /// Per-role append envelopes, expressed in ordinary immutable inputs.
    loop_growth: HashMap<u64, Vec<(super::super::paths::LocalPath, Expr)>>,
    /// Convert immutable symbolic inputs back into body-proof observations.
    proof_values: HashMap<VarIdent, Expr>,
}

/// Export a template only after checking transition coverage and closing its symbols.
pub(super) fn summarize(
    function: &Function,
    layouts: &super::super::layout::Layouts,
    functions: &HashMap<Fun, Function>,
    summaries: &HashMap<Fun, super::super::summary::FunctionSummary>,
    modes: &HashMap<VarIdent, Mode>,
    checked: &Checked,
) -> Option<Inferred> {
    let mut trace = Trace {
        active_iterator: None,
        reachable: true,
        path: crate::ast_util::mk_bool(&function.span, true),
        exits: Vec::new(),
        layouts,
        functions,
        summaries,
        modes,
        checked,
        used: HashSet::new(),
        state: State::default(),
        symbols: vec![],
        complete: None,
        regions: BTreeMap::new(),
        effects: vec![],
        branch_depth: 0,
        loop_tokens: None,
        loop_roots: None,
        loop_inputs: HashMap::new(),
        loop_allocations: Vec::new(),
        loop_nested: Vec::new(),
        loop_calls: Vec::new(),
        loop_scratch: HashMap::new(),
        loop_repetitions: HashMap::new(),
        loop_size_ceiling: None,
        allocation_checks: Vec::new(),
        loop_transfers: HashMap::new(),
        loop_progress: HashMap::new(),
        loop_growth: HashMap::new(),
        proof_values: HashMap::new(),
    };
    for (index, parameter) in function.x.params.iter().enumerate() {
        if parameter.x.mode != Mode::Exec {
            continue;
        }
        let typ = layouts.borrowed_owner(&parameter.x.typ).unwrap_or(&parameter.x.typ);
        let value = if layouts.owner(typ) {
            let memory = trace.symbol(&parameter.span, Input::Forest(index), expr::memory_type());
            let memory = trace.input_memory(&parameter.span, index, typ, &memory, &mut vec![])?;
            let mut minima = Minima::new();
            trace.input_minima(&parameter.span, index, typ, &mut vec![], &mut minima)?;
            Value::Owner(Node { origin: Some(index), typ: typ.clone(), memory, minima })
        } else if contracts::scalar(typ) {
            let symbol = trace.symbol(&parameter.span, Input::Scalar(index), typ.clone());
            let ExprX::Var(name) = &symbol.x else { unreachable!() };
            trace.proof_values.insert(
                name.clone(),
                SpannedTyped::new(&parameter.span, typ, ExprX::Var(parameter.x.name.clone())),
            );
            Value::Scalar(symbol)
        } else {
            Value::Unknown
        };
        trace.state.values.insert(parameter.x.name.clone(), value);
    }
    trace.initialize_regions(function)?;
    let result = trace.value(function.x.body.as_ref()?)?;
    let result = trace.finish_exits(
        &function.span,
        result,
        &crate::resource::memory::control::Target::Return,
    )?;
    if !checked.covered(&trace.used) {
        return None;
    }
    if layouts.owner(&function.x.outer_ret.x.typ) && !matches!(result, Value::Owner(_)) {
        return None;
    }
    let mut borrowed = BTreeMap::new();
    for (index, parameter) in function.x.params.iter().enumerate() {
        if matches!(&*parameter.x.typ, TypX::MutRef(_))
            && trace.state.written.contains(&parameter.x.name)
        {
            let Value::Owner(node) = trace.state.values.get(&parameter.x.name)? else {
                continue;
            };
            borrowed.insert(index, node.clone());
        }
    }
    let effects = trace.parameter_effects(function, &result);
    let origins: super::Origins<Expr> = checked
        .outputs
        .iter()
        .map(|(target, paths)| {
            Some((
                *target,
                paths
                    .iter()
                    .map(|(path, id)| Some((path.clone(), trace.regions.get(id)?.clone())))
                    .collect::<Option<_>>()?,
            ))
        })
        .collect::<Option<_>>()?;
    // Unused scalar arguments need no snapshot or additional representability restriction.
    let mut names = HashSet::new();
    let mut collect = |value: &Expr| {
        let _ = crate::ast_visitor::expr_visitor_check(value, &mut |scope, value| {
            if let ExprX::Var(name) = &value.x {
                if !scope.contains_key(name) {
                    names.insert(name.clone());
                }
            }
            Ok::<(), VirErr>(())
        });
    };
    for node in borrowed.values().chain(match &result {
        Value::Owner(node) => Some(node),
        _ => None,
    }) {
        collect(&node.memory);
        for floor in node.minima.values() {
            collect(&floor.capacity);
        }
    }
    if let Value::Scalar(value) = &result {
        collect(value);
    }
    if let Value::Iterator(sequence) = &result {
        collect(&sequence.first);
        collect(&sequence.count);
        collect(&sequence.position);
    }
    trace.regions.retain(|id, _| *id >= checked.inputs.len());
    for region in trace.regions.values() {
        collect(region);
    }
    for region in origins.values().flat_map(|paths| paths.values()) {
        collect(region);
    }
    if let Some(effects) = &effects {
        for (_, effect) in effects {
            effect.expressions(&mut collect);
        }
    }
    // A template may refer only to caller observations. In particular, a
    // representative iteration's counter and extracted-child tokens cannot
    // escape through intermediate lifetime regions or returned descriptors.
    if names.iter().any(|name| !trace.symbols.iter().any(|symbol| &symbol.name == name)) {
        return None;
    }
    trace.symbols.retain(|symbol| names.contains(&symbol.name));
    let ordered = !trace.loop_repetitions.is_empty() || checked.operations.values().any(|operation| matches!(operation, checked::Operation::Call { target, .. } if summaries.get(target).and_then(|summary| summary.transfer.as_ref()).is_some_and(|template| template.ordered)));
    Some(Inferred {
        loops: trace.loop_transfers,
        progress: trace.loop_progress,
        growth: trace.loop_growth,
        checks: trace.allocation_checks,
        scratch: trace.loop_scratch,
        repetitions: trace.loop_repetitions,
        template: Template {
            ordered,
            origins,
            regions: trace.regions,
            symbols: trace.symbols,
            effects,
            borrowed,
            result,
        },
    })
}

impl Trace<'_> {
    /// Export only checked, parameter-relative effects. Captured input forests
    /// in a payload require a transfer relation, not repeated fresh construction.
    fn parameter_effects(
        &self,
        function: &Function,
        result: &Value,
    ) -> Option<Vec<(usize, Effect)>> {
        let closed = |value: &Expr| {
            let mut closed = true;
            let _ = crate::ast_visitor::expr_visitor_check(value, &mut |scope, value| {
                if let ExprX::Var(name) = &value.x {
                    if scope.contains_key(name) {
                        return Ok::<(), VirErr>(());
                    }
                    closed &= self.symbols.iter().any(|symbol| {
                        &symbol.name == name
                            && matches!(symbol.input, Input::Scalar(_) | Input::Complete)
                    });
                }
                Ok::<(), VirErr>(())
            });
            closed
        };
        if let Value::Owner(node) = result {
            if node.origin.is_none() && !closed(&node.memory) {
                return None;
            }
        }
        let mut effects = Vec::new();
        for effect in &self.effects {
            let Some(index) = function.x.params.iter().position(|parameter| {
                matches!(&*parameter.x.typ, TypX::MutRef(_)) && &parameter.x.name == effect.root()
            }) else {
                continue;
            };
            if !effect.exportable() {
                return None;
            }
            fn valid(effect: &Effect, closed: &impl Fn(&Expr) -> bool) -> bool {
                match effect {
                    Effect::Guarded { condition, effect, .. } => {
                        closed(condition) && valid(effect, closed)
                    }
                    Effect::Append {
                        child: Value::Owner(Node { origin: Some(_), .. }), ..
                    } => true,
                    _ => {
                        let mut valid = true;
                        effect.expressions(&mut |value| valid &= closed(value));
                        valid
                    }
                }
            }
            if !valid(effect, &closed) {
                return None;
            }
            effects.push((index, effect.clone()));
        }
        Some(effects)
    }
}
