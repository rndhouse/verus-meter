//! Shared loop structure for body proofs and caller ownership summaries.
//!
//! Classify source control flow and proof requirements once, before accounting.
//! Publish the record only after its body operations and boundary lifetimes have
//! been checked. Consumers may specialize expressions, but cannot rediscover a
//! different loop shape or invent effects from unchecked syntax.

mod analysis;
pub(super) mod progress;

use super::{layout::Layouts, model, paths::LocalPath, summary::FunctionSummary};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

/// A comparison observation; the checked iteration determines its progress.
#[derive(Clone)]
pub(super) struct Control {
    /// Left-hand scalar or collection length, observed at the loop head.
    pub(super) start: Expr,
    /// Right-hand observation, which may also have a checked affine transition.
    pub(super) end: Expr,
    /// Comparison direction and whether its boundary is included.
    pub(super) comparison: InequalityOp,
    /// A direct scalar observation, used to admit allocation-size expressions.
    counter: Option<VarIdent>,
}

impl Control {
    pub(super) fn counter(&self) -> Option<&VarIdent> {
        self.counter.as_ref()
    }
}

/// Source observations used to select proof candidates, not assumed effects.
/// Body accounting and checked operation records remain authoritative.
#[derive(Clone, Default)]
struct Effects {
    /// Direct appends and retained helper growth invalidate entry-byte ceilings.
    appends: HashSet<LocalPath>,
    /// Replacements can increase the enclosing runtime child's footprint.
    replacements: HashSet<LocalPath>,
    /// Assigned locals are checked against the summary's persistent scalar state.
    writes: HashSet<VarIdent>,
    /// Helper effects whose iteration metadata is not yet representable.
    opaque_helpers: bool,
    /// Calls, owner expressions, or returns prevent a read-only summary.
    ownership: bool,
}

/// One loop's shared structure, proof snapshots, and original-input boundary.
#[derive(Clone)]
pub(super) struct Loop {
    /// Source identity used by both proof instrumentation and summary coverage.
    pub(super) span: Span,
    /// Executable condition, accounted before each body execution.
    pub(super) condition: Expr,
    /// Executable body evaluated by both consumers in their own state domains.
    pub(super) body: Expr,
    /// User invariants to preserve alongside compiler-generated memory facts.
    pub(super) invariants: LoopInvariants,
    /// Optional closed-count control form, classified once at loop entry.
    pub(super) control: Option<Control>,
    /// Literal scalar ceiling proposed by user invariants. It is only a proof
    /// candidate: every use remains checked by the ordinary loop obligations.
    pub(super) size_ceiling: Option<u64>,
    /// Stable symbolic quantities proposed by invariant comparisons. Allocation
    /// sites must prove these ceilings; they never replace complete descriptors.
    pub(super) size_candidates: Vec<Expr>,
    /// Syntactic scalar transition candidates, validated by the checked evaluator.
    pub(super) scalar_steps: HashMap<VarIdent, (Typ, i128)>,
    /// Entry snapshots and visit ordinal used only by ordinary proof obligations.
    pub(super) progress: Option<progress::Observation>,
    /// Entry forests of nested loops may already reflect earlier outer visits.
    pub(super) nested: bool,
    /// Closed visit ceiling, retained only with accepted progress evidence.
    visits_bound: Option<Expr>,
    /// Completed visits and their immutable entry observation. Both their
    /// nonnegativity and byte bounds remain ordinary inductive candidates.
    completed: Option<(Expr, Expr)>,
    /// Original regions after all iterations, distinct from first-iteration IDs.
    pub(super) regions: Vec<Region>,
    /// Entry snapshots for local child-charge conservation proofs.
    charges: Vec<Charge>,
    /// Entry heap and temporary-storage candidates, frozen only when requested
    /// by a completed transformation and checked before ownership changes.
    entry_headroom: Vec<Expr>,
    /// Simultaneous body costs used to bound temporary local storage. Helper
    /// allowances are specialized only after their iteration observations close.
    local_costs: Vec<super::footprint::Footprint>,
    /// Shared source classification; consumers do not rescan the body.
    effects: Effects,
    /// State identities and source lengths at this loop, independent of later
    /// moves. An enclosing loop supplies the completed charge policy.
    element_ids: Vec<usize>,
    /// Executable lengths at this source location, retained across owner moves.
    element_sources: HashMap<usize, Expr>,
    /// Immutable scalars eligible for completed element-charge policies.
    proof_scalars: HashSet<VarIdent>,
    /// Inductive element bounds supplied after enclosing policies are complete.
    element_facts: Vec<Expr>,
}

/// Fixed ownership roles at a loop boundary; indices remain in each forest.
#[derive(Clone)]
pub(super) struct Region {
    /// Persistent collection slot; runtime indices stay inside its forest.
    pub(super) location: LocalPath,
    /// Original region before any iterations, absent for fresh local storage.
    pub(super) entry: Option<usize>,
    /// Region produced by the checked representative body, before repetition.
    pub(super) body: usize,
    /// Original region after all iterations, distinct from first-iteration IDs.
    pub(super) exit: usize,
}

/// Inductive child-charge candidates for a persistent collection role.
#[derive(Clone)]
struct Charge {
    /// Persistent collection whose local child counters form this sum.
    location: LocalPath,
    /// Mutable sum of this frame's child allocations at the loop head.
    current: Expr,
    /// Immutable snapshot of the same sum before entering the loop.
    entry: Expr,
    /// Collection backing and its entry snapshot for identity frame proofs.
    backing: Option<(Expr, Expr)>,
    /// Executable occupied length and its immutable loop-entry observation.
    length: (Expr, Expr),
    /// Current capacity, its entry snapshot, and inline size for append proofs.
    reservation: Option<(Expr, Expr, u64)>,
}

impl Loop {
    /// Immutable body observations may close entry facts without referring to
    /// a scalar that changes during the loop.
    pub(super) fn stable_scalar(&self, name: &VarIdent) -> bool {
        self.proof_scalars.contains(name)
    }

    /// Fixed collection roles whose logical lengths have entry snapshots.
    pub(super) fn length_roles(&self) -> impl Iterator<Item = &LocalPath> {
        self.charges.iter().map(|charge| &charge.location)
    }

    /// Immutable proof observation for a role's length at this loop invocation.
    pub(super) fn entry_length(&self, path: &LocalPath) -> Option<Expr> {
        self.charges
            .iter()
            .find(|charge| &charge.location == path)
            .map(|charge| charge.length.1.clone())
    }

    pub(super) fn new(
        value: &Expr,
        layouts: &Layouts,
        summaries: &HashMap<Fun, FunctionSummary>,
    ) -> Result<Self, VirErr> {
        let ExprX::Loop {
            cond: Some(condition),
            body,
            invs,
            source: LoopSource::Loop,
            is_for_loop: false,
            atomic_call: false,
            ..
        } = &value.x
        else {
            return Err(model::unsupported(
                &value.span,
                "this executable expression or control-flow exit",
            ));
        };
        if !model::unit(&value.typ) {
            return Err(model::unsupported(
                &value.span,
                "this executable expression or control-flow exit",
            ));
        }
        let control = match &condition.x {
            ExprX::Binary(BinaryOp::Inequality(comparison), start, end) => Some(Control {
                start: start.clone(),
                end: end.clone(),
                comparison: *comparison,
                counter: local(start),
            }),
            _ => None,
        };
        let mut effects = Effects::default();
        for (region, in_body) in [(condition, false), (body, true)] {
            crate::ast_visitor::expr_visitor_check(region, &mut |_, expression| {
                effects.ownership |= layouts.owner(&expression.typ)
                    || matches!(expression.x, ExprX::Call { .. } | ExprX::Return(_));
                if !in_body {
                    return Ok::<(), VirErr>(());
                }
                if let ExprX::Assign { place, typ, .. } = &expression.x {
                    if layouts.owner(typ) {
                        if let Some(location) = super::paths::place(place, typ) {
                            effects.replacements.insert(location);
                        }
                    }
                    if let PlaceX::Local(name) = &place.x {
                        effects.writes.insert(name.clone());
                    }
                }
                if let ExprX::Call { target: CallTarget::Fun(_, fun, _, _, attrs), args, .. } =
                    &expression.x
                {
                    if attrs.resource_intrinsic == Some(ResourceIntrinsic::VecPush) {
                        if let Some(receiver) = args.first() {
                            if let Some(location) =
                                super::paths::expr(receiver, super::paths::referent(&receiver.typ))
                            {
                                effects.appends.insert(location);
                            }
                        }
                    }
                    if let Some(summary) = summaries.get(fun) {
                        let changes = !summary.allocations.retained.is_empty()
                            || !summary.allocations.collections.is_empty()
                            || !summary.allocations.children.is_empty()
                            || !summary.vectors.removals.is_empty();
                        // A complete recurrence may have no monotone effect
                        // program. Its checked retained allocations still mark
                        // enclosing runtime-child byte sums as potentially growing.
                        for (parameter, changed) in summary.allocations.retained.keys() {
                            if let Some(argument) = args.get(*parameter) {
                                if let Some((name, mut path)) = super::paths::expr(
                                    argument,
                                    super::paths::referent(&argument.typ),
                                ) {
                                    path.extend(changed.iter().cloned());
                                    effects.appends.insert((name, path));
                                }
                            }
                        }
                        for (parameter, replaced) in summary.allocations.children.keys() {
                            if let Some(argument) = args.get(*parameter) {
                                if let Some((name, mut path)) = super::paths::expr(
                                    argument,
                                    super::paths::referent(&argument.typ),
                                ) {
                                    path.extend(replaced.iter().cloned());
                                    effects.replacements.insert((name, path));
                                }
                            }
                        }
                        if let Some(program) =
                            summary.transfer.as_ref().and_then(|template| template.effects.as_ref())
                        {
                            for (index, effect) in program {
                                if effect.appends() {
                                    if let Some(argument) = args.get(*index) {
                                        if let Some((name, mut path)) = super::paths::expr(
                                            argument,
                                            super::paths::referent(&argument.typ),
                                        ) {
                                            if let Some(location) = effect.location() {
                                                path.extend(location.1.iter().cloned());
                                                effects.appends.insert((name, path));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        effects.opaque_helpers |= changes && summary.transfer.is_none();
                    }
                }
                Ok(())
            })?;
        }
        let mut size_ceiling = None;
        let mut size_candidates = Vec::new();
        for invariant in invs.iter() {
            crate::ast_visitor::expr_visitor_check(&invariant.inv, &mut |scope, value| {
                if let Some(n) = super::contracts::constant(value) {
                    size_ceiling = Some(size_ceiling.unwrap_or(0).max(n));
                }
                if let ExprX::Binary(BinaryOp::Inequality(op), left, right) = &value.x {
                    let candidate = match op {
                        InequalityOp::Lt | InequalityOp::Le => right,
                        InequalityOp::Gt | InequalityOp::Ge => left,
                    };
                    let stable = crate::ast_visitor::expr_visitor_check(candidate, &mut |_, value| {
                        if matches!(&value.x, ExprX::Var(name) if scope.contains_key(name) || effects.writes.contains(name)) { Err(()) } else { Ok(()) }
                    }).is_ok();
                    if stable {
                        size_candidates.push(candidate.clone());
                    }
                }
                Ok::<(), VirErr>(())
            })?;
        }
        let scalar_steps = progress::scalar_steps(body);
        Ok(Self {
            scalar_steps,
            progress: None,
            nested: false,
            visits_bound: None,
            size_ceiling,
            size_candidates,
            completed: None,
            span: value.span.clone(),
            condition: condition.clone(),
            body: body.clone(),
            invariants: invs.clone(),
            control,
            effects,
            regions: vec![],
            charges: vec![],
            entry_headroom: vec![],
            local_costs: vec![],
            element_ids: vec![],
            element_sources: HashMap::new(),
            proof_scalars: HashSet::new(),
            element_facts: vec![],
        })
    }

    /// Growth beneath an indexed child changes its parent's byte sum even if
    /// the parent never appends. Path classes suffice to omit a frame candidate;
    /// the ordered recurrence still retains the actual runtime index.
    pub(super) fn grows_children(&self, location: &LocalPath) -> bool {
        self.effects
            .appends
            .iter()
            .any(|changed| changed == location || nested_runtime_path(location, changed))
            || self
                .effects
                .replacements
                .iter()
                .any(|changed| nested_runtime_path(location, changed))
    }

    /// An append can allocate root backing even when children carry no bytes.
    pub(super) fn grows_backing(&self, location: &LocalPath) -> bool {
        self.effects.appends.contains(location) || self.effects.replacements.contains(location)
    }

    /// A replacement can reduce reservations in the selected ownership class.
    /// It does not change the descriptors of untouched children.
    pub(super) fn replaces_class(
        &self,
        location: &LocalPath,
        class: &[super::metadata::reservations::Step],
    ) -> bool {
        self.effects.replacements.iter().any(|changed| {
            if changed.0 != location.0 || !changed.1.starts_with(&location.1) {
                return false;
            }
            let suffix = &changed.1[location.1.len()..];
            if !matches!(suffix.first(), Some(super::heap::OwnerSlot::Element(_))) {
                return false;
            }
            let selected: Vec<_> = suffix[1..]
                .iter()
                .map(|slot| match slot {
                    super::heap::OwnerSlot::Element(_) => {
                        super::metadata::reservations::Step::Repeated
                    }
                    _ => super::metadata::reservations::Step::Fixed(slot.clone()),
                })
                .collect();
            class.starts_with(&selected)
        })
    }

    pub(super) fn check_helpers(&self) -> Result<(), VirErr> {
        if self.effects.opaque_helpers {
            Err(model::unsupported(
                &self.span,
                "loop-carried helper effects without precise allocation metadata",
            ))
        } else {
            Ok(())
        }
    }

    pub(super) fn writes(&self) -> impl Iterator<Item = &VarIdent> {
        self.effects.writes.iter()
    }

    pub(super) fn read_only(&self) -> bool {
        !self.effects.ownership && self.regions.is_empty()
    }

    /// Resolve a transfer against the same persistent charge roles captured by
    /// body accounting. Missing roles cannot manufacture a conservation proof.
    pub(super) fn transfer(&self, source: &LocalPath, target: &LocalPath) -> Option<Transfer> {
        Some(Transfer {
            source: self.charges.iter().position(|charge| &charge.location == source)?,
            target: self.charges.iter().position(|charge| &charge.location == target)?,
            additional: None,
        })
    }
}

/// A whole-child transfer inferred from a fully accepted ownership summary.
/// It contains role identities only; the proof consumer constructs inequalities.
/// Equal endpoints denote restoration of one role, including unchanged backing.
#[derive(Clone)]
pub(super) struct Transfer {
    /// Index of the source role in the associated checked loop's charge table.
    source: usize,
    /// Index of the destination role in that same table.
    target: usize,
    /// Proved per-append ceiling for allocations introduced while transforming
    /// a child. Original input storage remains in the conservation group.
    pub(super) additional: Option<Expr>,
}

fn local(value: &Expr) -> Option<VarIdent> {
    match &value.x {
        ExprX::Var(name) => Some(name.clone()),
        ExprX::ReadPlace(place, _) => match &place.x {
            PlaceX::Local(name) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn nested_runtime_path(parent: &LocalPath, child: &LocalPath) -> bool {
    parent.0 == child.0
        && child.1.starts_with(&parent.1)
        && child.1[parent.1.len()..]
            .iter()
            .any(|slot| matches!(slot, super::heap::OwnerSlot::Element(_)))
}
