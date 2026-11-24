//! A fixed worker is represented by its byte bounds in each native mutex state.
//! A coordinator point selects its outstanding actors by their completion tags.
//! Advancing one actor stays inside its checked local observations. Mutual
//! exclusion rules out simultaneous ownership of the same mutex by two actors.
//! This product therefore covers each step, including waits and explicit release,
//! without ordering independent workers by the compiler's traversal order.

use super::{WorkerId, execution::Execution};
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{
    accounting::{CheckKind, Obligation},
    analysis::Analysis,
    contracts,
    footprint::MemoryBudget,
    loops::progress::difference,
    model::unit,
    synchronization::Instance,
    transfer::simplify,
};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// For the same lock set, discard only costs separated by a known constant.
/// Incomparable symbolic costs remain independent proof alternatives.
#[derive(Default)]
struct Phases(BTreeMap<BTreeSet<Instance>, Vec<Expr>>);

impl Phases {
    fn insert(&mut self, locks: BTreeSet<Instance>, amount: Expr) {
        let costs = self.0.entry(locks).or_default();
        for cost in costs.iter_mut() {
            if let Some(delta) = difference(&amount, cost) {
                if delta > 0 {
                    *cost = amount;
                }
                return;
            }
        }
        costs.push(amount);
    }

    fn together(&self, peer: &Self, remaining: &BTreeSet<Instance>, span: &Span) -> Self {
        let mut result = Self::default();
        for (left, costs) in &self.0 {
            for (right, others) in &peer.0 {
                if left.is_disjoint(right) {
                    // Once all actors that could contend for an instance have
                    // been combined, its identity no longer distinguishes states.
                    let held: BTreeSet<_> =
                        left.union(right).filter(|i| remaining.contains(i)).copied().collect();
                    for a in costs {
                        for b in others {
                            result.insert(held.clone(), contracts::add(span, a.clone(), b.clone()));
                        }
                    }
                }
            }
        }
        result
    }

    fn peak(&self, span: &Span) -> Option<Expr> {
        fn maximum(span: &Span, costs: &[&Expr]) -> Expr {
            if let [one] = costs {
                return (*one).clone();
            }
            let (left, right) = costs.split_at(costs.len() / 2);
            contracts::maximum(span, maximum(span, left), maximum(span, right))
        }
        let costs: Vec<_> = self.0.values().flatten().collect();
        (!costs.is_empty()).then(|| maximum(span, &costs))
    }
}

/// Only immutable scalar inputs can be read outside the worker. A vector's
/// initial reservation is a candidate bound on its current charge. Each use
/// of that candidate is checked in the worker before it is exported.
fn export(
    value: &Expr,
    reservations: &HashMap<VarIdent, Expr>,
    captures: &HashMap<VarIdent, Expr>,
) -> Option<(Expr, Expr)> {
    let local = simplify::specialize(value, reservations);
    fn stable(value: &Expr, captures: &HashMap<VarIdent, Expr>) -> bool {
        match &value.x {
            ExprX::Const(Constant::Int(_)) => true,
            ExprX::Var(name) => captures.contains_key(name),
            ExprX::Binary(BinaryOp::Arith(_), a, b) => stable(a, captures) && stable(b, captures),
            _ => false,
        }
    }
    stable(&local, captures).then(|| (local.clone(), simplify::specialize(&local, captures)))
}

impl Execution {
    fn fixed_phases(
        &self,
        analysis: &Analysis<'_>,
        parameters: &HashSet<VarIdent>,
        reservations: &HashMap<VarIdent, Expr>,
        checks: &mut Vec<Obligation>,
    ) -> Option<Phases> {
        let span = &self.entry.definition.span;
        let initial = self.initial.live_expression(span).total();
        // Separately owned descendants and results need their own transfer
        // phases. Imported Arc handles borrow the coordinator's charged backing.
        if self.publication.caller.is_some()
            || !analysis.growth.worker_occurrences.get(&self.actor)?.is_empty()
            || !unit(&self.result.typ)
            || contracts::constant(&self.retained.live_expression(span).total()) != Some(0)
            || contracts::constant(&initial) != Some(self.entry.storage.value.bytes)
            || !self.effects.calls.is_empty()
            || !self.effects.ownership.holders.is_empty()
        {
            return None;
        }
        let mut captures = HashMap::new();
        for input in &self.inputs {
            if contracts::scalar(&input.typ) {
                if let Some(name) = self.immutable_scalars.get(&input.name)
                    && parameters.contains(name)
                {
                    captures.insert(
                        input.name.clone(),
                        SpannedTyped::new(span, &input.typ, ExprX::Var(name.clone())),
                    );
                }
            } else if !matches!(&*input.typ, TypX::Decorate(TypDecoration::Arc, _, item)
                if contracts::scalar(item) || analysis.layouts.mutex_payload(item).is_some_and(|t| contracts::scalar(t) || unit(t)))
            {
                return None;
            }
        }
        let native: BTreeSet<_> = self.effects.ownership.fixed_mutex_intervals().collect();
        let mut phases = Phases::default();
        // Enter with captures intact and no acquired guard. Unit completion
        // contributes zero, so this unrestricted alternative also covers it.
        phases.insert(BTreeSet::new(), initial);
        for p in self.effects.points.iter() {
            let value = p.cost.total();
            let (local, exported) = export(&value, reservations, &captures)?;
            if !simplify::inspect::same_expression(&value, &local) {
                checks.push(Obligation {
                    span: p.span.clone(),
                    cost: p.cost.clone(),
                    bound: MemoryBudget::total(local),
                    kind: CheckKind::WorkerState("at a fixed worker phase"),
                });
            }
            let held = p
                .condition
                .held
                .iter()
                .filter(|i| native.contains(i))
                .map(|i| i.instance)
                .collect();
            phases.insert(held, exported);
        }
        Some(phases)
    }
}

impl Analysis<'_> {
    /// Combine closed direct publications. Ineligible domains keep the existing
    /// deferred diagnostic and all their independently checked local obligations.
    pub(super) fn compose_fixed_workers(&mut self, function: &Function) -> bool {
        let params = contracts::inputs(function);
        if function.x.params.iter().any(|p| p.x.mode == Mode::Exec && !params.contains(&p.x.name))
            || !unit(&function.x.outer_ret.x.typ)
            || !self.calls.is_empty()
            || !self.growth.retained_worker_families.is_empty()
            || !self.growth.versioned_shared.is_empty()
        {
            return false;
        }
        let body = function.x.body.as_ref().expect("checked executable body");
        // Scoped observations require a subtree proof. Loop publication and
        // nested lifecycles have a different occurrence domain as well.
        let mut scoped_or_repeated = false;
        crate::ast_visitor::expr_visitor_walk(body, &mut |e| {
            scoped_or_repeated |= matches!(
                e.x,
                ExprX::Loop { .. }
                    | ExprX::ResourceSection(_)
                    | ExprX::ResourceAssert(_)
                    | ExprX::ResourceAssertCurrent(_)
            );
            crate::visitor::VisitorControlFlow::Recurse
        });
        if scoped_or_repeated {
            return false;
        }
        let reservations = self
            .growth
            .vectors
            .iter()
            .filter(|v| v.local_constructor)
            .filter_map(|v| {
                let ExprX::Var(name) = &v.backing.bytes.x else { return None };
                Some((name.clone(), v.backing.initial_bytes.clone()))
            })
            .collect();
        let mut checks = Vec::new();
        let mut workers = BTreeMap::new();
        for (&id, w) in &self.growth.worker_executions {
            if !self
                .growth
                .worker_joins
                .values()
                .flatten()
                .any(|j| j.families.len() == 1 && j.families.contains(&id))
            {
                return false;
            }
            let Some(phases) = w.fixed_phases(self, &params, &reservations, &mut checks) else {
                return false;
            };
            workers.insert(id, phases);
        }
        let mut cache = BTreeMap::<Vec<WorkerId>, Expr>::new();
        let mut additions = Vec::new();
        for p in self.storage.points() {
            // The tag is reserved while the publisher still owns the closure.
            // That fork observation already includes its captures. Publication
            // records another caller point immediately after transferring them.
            let active: Vec<_> = self
                .growth
                .worker_executions
                .iter()
                .filter(|(_, w)| {
                    p.values.contains(&w.completion)
                        && p.values.is_disjoint(&w.entry.storage.value.ids)
                })
                .map(|(id, _)| *id)
                .collect();
            if active.is_empty() {
                additions.push(None);
                continue;
            }
            let extra = cache.entry(active.clone()).or_insert_with(|| {
                let mut product = Phases::default();
                product.insert(Default::default(), contracts::literal(&p.span, 0));
                for (index, id) in active.iter().enumerate() {
                    let remaining = active[index + 1..]
                        .iter()
                        .flat_map(|id| workers[id].0.keys().flatten().copied())
                        .collect();
                    product = product.together(&workers[id], &remaining, &p.span);
                }
                product.peak(&p.span).expect("unrestricted worker entry")
            });
            additions.push(Some(extra.clone()));
        }
        self.obligations.extend(checks);
        self.storage.include_worker_costs(additions);
        true
    }
}
