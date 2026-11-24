//! Each worker has a checked byte bound for each combination of intact holders.
//! A coordinator point selects its outstanding actors by their completion tags.
//! Advancing one actor stays inside its checked local observations. Mutual
//! exclusion and verified holder limits constrain simultaneous phases.
//! This product therefore covers each step, including waits and explicit release,
//! without ordering independent workers by the compiler's traversal order.

mod population;
mod roles;
use roles::{Class, Constraints, Held};

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

/// For the same holder counts, discard only costs separated by a known constant.
/// Incomparable symbolic costs remain independent proof alternatives.
#[derive(Default)]
struct Phases(BTreeMap<Held, Vec<Expr>>);

impl Phases {
    fn insert(&mut self, held: Held, amount: Expr) {
        let costs = self.0.entry(held).or_default();
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

    fn together(
        &self,
        peer: &Self,
        remaining: &BTreeSet<Class>,
        constraints: &Constraints,
        span: &Span,
    ) -> Self {
        let mut result = Self::default();
        for (left, costs) in &self.0 {
            for (right, others) in &peer.0 {
                let Some((held, feasible)) = constraints.combine(span, left, right, remaining)
                else {
                    continue;
                };
                for a in costs {
                    for b in others {
                        let cost = contracts::add(span, a.clone(), b.clone());
                        // An infeasible state contributes zero to a maximum of byte counts.
                        let cost = feasible.iter().fold(cost, |v, condition| {
                            super::super::growth::select(
                                span,
                                condition.clone(),
                                v,
                                contracts::literal(span, 0),
                            )
                        });
                        result.insert(held.clone(), cost);
                    }
                }
            }
        }
        result
    }

    fn peak(&self, span: &Span) -> Option<Expr> {
        let costs: Vec<_> = self.0.values().flatten().cloned().collect();
        (!costs.is_empty()).then(|| maximum_cost(span, &costs))
    }
}

/// Balance maxima so later expression walks stay shallow even with many paths.
fn maximum_cost(span: &Span, costs: &[Expr]) -> Expr {
    if let [one] = costs {
        return one.clone();
    }
    let (left, right) = costs.split_at(costs.len() / 2);
    contracts::maximum(span, maximum_cost(span, left), maximum_cost(span, right))
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
    fn phases(
        &self,
        analysis: &Analysis<'_>,
        parameters: &HashSet<VarIdent>,
        reservations: &HashMap<VarIdent, Expr>,
        checks: &mut Vec<Obligation>,
        constraints: &mut Constraints,
    ) -> Option<Phases> {
        let span = &self.entry.definition.span;
        let initial = self.initial.live_expression(span).total();
        // Separately owned descendants and results need their own transfer
        // phases. Imported Arc handles borrow the coordinator's charged backing.
        let completed = self.retained.live_expression(span).total();
        let indexed_scalar = analysis.growth.retained_worker_families.contains(&self.actor)
            && contracts::scalar(&self.result.typ);
        if self.publication.caller.is_some()
            || !(unit(&self.result.typ) || indexed_scalar)
            || self.result.owner.is_some()
            || contracts::constant(&completed) != Some(self.result.value.bytes)
            || contracts::constant(&initial) != Some(self.entry.storage.value.bytes)
            || self.effects.calls.iter().any(|(f, _)| !analysis.protocol_helper(f))
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
            } else if !analysis.layouts.inline_protocol_value(&input.typ)
                && !matches!(&*input.typ, TypX::Decorate(TypDecoration::Arc, _, item)
                if contracts::scalar(item) || analysis.layouts.inline_protocol_value(item) || analysis.layouts.mutex_payload(item).is_some_and(|t| contracts::scalar(t) || unit(t)))
            {
                return None;
            }
        }
        let native: BTreeSet<_> =
            self.effects.ownership.mutex_intervals(&analysis.transitions).collect();
        let mut phases = Phases::default();
        // Completion releases the working frame but retains the inline result
        // with its handle until join. Both entry and completion are unrestricted.
        phases.insert(Held::new(), initial);
        phases.insert(Held::new(), completed);
        for p in self.effects.points.iter() {
            let value = p.cost.total();
            let (local, exported) = export(&value, reservations, &captures)?;
            if !simplify::inspect::same_expression(&value, &local) {
                checks.push(Obligation {
                    span: p.span.clone(),
                    cost: p.cost.clone(),
                    bound: MemoryBudget::total(local),
                    kind: CheckKind::WorkerState("at a worker phase"),
                });
            }
            let mut held: Held = p
                .condition
                .held
                .iter()
                .filter(|i| native.contains(i))
                .map(|i| (Class::Mutex(i.instance), 1))
                .collect();
            for witness in &p.holders {
                if let Some(role) = self.effects.ownership.holders.population_role(*witness) {
                    let class = constraints.register(analysis, parameters, span, role);
                    held.insert(class, 1);
                }
            }
            phases.insert(held, exported);
        }
        Some(phases)
    }
}

impl Analysis<'_> {
    /// Combine closed worker domains. Ineligible domains keep the existing
    /// deferred diagnostic and all their independently checked local obligations.
    pub(super) fn compose_workers(&mut self, function: &Function) -> bool {
        let params = contracts::inputs(function);
        if function.x.params.iter().any(|p| {
            p.x.mode == Mode::Exec
                && !params.contains(&p.x.name)
                && !(matches!(&*p.x.typ, TypX::Decorate(TypDecoration::Ref, None, _))
                    && !p.x.user_mut
                    && self.layouts.inline_protocol_value(&p.x.typ))
        }) || !unit(&function.x.outer_ret.x.typ)
            || self.calls.iter().any(|(f, _)| !self.protocol_helper(f))
            || !self.growth.versioned_shared.is_empty()
        {
            return false;
        }
        let body = function.x.body.as_ref().expect("checked executable body");
        // Scoped observations require a separate subtree proof.
        let mut scoped = false;
        crate::ast_visitor::expr_visitor_walk(body, &mut |e| {
            scoped |= matches!(
                e.x,
                ExprX::ResourceSection(_)
                    | ExprX::ResourceAssert(_)
                    | ExprX::ResourceAssertCurrent(_)
            );
            crate::visitor::VisitorControlFlow::Recurse
        });
        if scoped {
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
        let mut constraints = Constraints::default();
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
            let Some(phases) =
                w.phases(self, &params, &reservations, &mut checks, &mut constraints)
            else {
                return false;
            };
            workers.insert(id, phases);
        }
        if !self.growth.retained_worker_families.is_empty() {
            return self.compose_population(function, workers, checks, &constraints);
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
                        .flat_map(|id| workers[id].0.keys().flat_map(|held| held.keys().copied()))
                        .collect();
                    product = product.together(&workers[id], &remaining, &constraints, &p.span);
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
