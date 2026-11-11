//! Shared loop structure for body proofs and caller ownership summaries.
//!
//! Classify source control flow and proof requirements once, before accounting.
//! Publish the record only after its body operations and boundary lifetimes have
//! been checked. Consumers may specialize expressions, but cannot rediscover a
//! different loop shape or invent effects from unchecked syntax.

mod analysis;

use super::{layout::Layouts, model, paths::LocalPath, summary::FunctionSummary};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

/// Control forms with a closed iteration count in the current ownership model.
/// Other loops may still have valid body proofs without an exportable summary.
#[derive(Clone)]
pub(super) enum Control {
    /// Candidate `counter < end` form; summary evaluation checks unit progress.
    Counted { counter: VarIdent, start: Expr, end: Expr },
    /// Candidate `length > end` form; checked operations must pop that receiver.
    Consuming { start: Expr, end: Expr },
}

impl Control {
    pub(super) fn counter(&self) -> Option<&VarIdent> {
        match self {
            Self::Counted { counter, .. } => Some(counter),
            Self::Consuming { .. } => None,
        }
    }

    pub(super) fn bounds(&self) -> (&Expr, &Expr) {
        match self {
            Self::Counted { start, end, .. } | Self::Consuming { start, end } => (start, end),
        }
    }
}

/// Source observations used to select proof candidates, not assumed effects.
/// Body accounting and checked operation records remain authoritative.
#[derive(Clone, Default)]
struct Effects {
    /// Direct append receivers cannot use a non-growing entry-byte ceiling.
    appends: HashSet<LocalPath>,
    /// Assigned locals are checked against the summary's persistent scalar state.
    writes: HashSet<VarIdent>,
    /// Helper templates require runtime-forest classification in the loop proof.
    templates: bool,
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
    /// Original regions after all iterations, distinct from first-iteration IDs.
    pub(super) regions: Vec<Region>,
    /// Entry snapshots for local child-charge conservation proofs.
    charges: Vec<Charge>,
    /// Shared source classification; consumers do not rescan the body.
    effects: Effects,
}

/// Fixed ownership roles at a loop boundary; indices remain in each forest.
#[derive(Clone)]
pub(super) struct Region {
    /// Persistent collection slot; runtime indices stay inside its forest.
    pub(super) location: LocalPath,
    /// Original region before any iterations, absent for fresh local storage.
    pub(super) entry: Option<usize>,
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
}

impl Loop {
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
            ExprX::Binary(BinaryOp::Inequality(op), start, end) => match op {
                InequalityOp::Lt => local(start).map(|counter| Control::Counted {
                    counter,
                    start: start.clone(),
                    end: end.clone(),
                }),
                InequalityOp::Gt => {
                    Some(Control::Consuming { start: start.clone(), end: end.clone() })
                }
                _ => None,
            },
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
                if let ExprX::Assign { place, .. } = &expression.x {
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
                        effects.templates |= summary.transfer.is_some();
                        let changes = !summary.allocations.collections.is_empty()
                            || !summary.allocations.children.is_empty()
                            || !summary.vectors.removals.is_empty();
                        effects.opaque_helpers |= changes
                            && summary.transfer.as_ref().is_none_or(|template| template.appends);
                    }
                }
                Ok(())
            })?;
        }
        Ok(Self {
            span: value.span.clone(),
            condition: condition.clone(),
            body: body.clone(),
            invariants: invs.clone(),
            control,
            effects,
            regions: vec![],
            charges: vec![],
        })
    }

    pub(super) fn appends_to(&self, location: &LocalPath) -> bool {
        self.effects.appends.contains(location)
    }

    pub(super) fn uses_templates(&self) -> bool {
        self.effects.templates
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
