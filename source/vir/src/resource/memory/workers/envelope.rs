//! Each worker has a checked byte bound for each combination of intact holders.
//! A coordinator point selects its outstanding actors by their completion tags.
//! Advancing one actor stays inside its checked local observations. Mutual
//! exclusion and verified holder limits constrain simultaneous phases.
//! This product therefore covers each step, including waits and explicit release,
//! without ordering independent workers by the compiler's traversal order.

mod actor;
mod population;
mod roles;
use roles::{Class, Constraints, Held};

use super::{WorkerId, execution::Execution};
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{
    accounting::{CheckKind, Obligation, Point},
    analysis::Analysis,
    contracts,
    footprint::{Footprint, MemoryBudget},
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

/// Keep the classes of descendants until all peers outside their subtree have
/// been considered. Child activity comes from this publisher's actual ledger.
fn outstanding<'a>(
    point: &Point,
    children: &'a [(WorkerId, Phases)],
    analysis: &Analysis<'_>,
) -> impl Iterator<Item = (WorkerId, &'a Phases)> {
    children.iter().filter_map(move |(id, phases)| {
        let worker = &analysis.growth.worker_executions[id];
        (point.values.contains(&worker.completion)
            && point.collected_tag != Some(worker.completion)
            && point.values.is_disjoint(&worker.entry.storage.value.ids))
        .then_some((*id, phases))
    })
}

impl crate::resource::memory::layout::Layouts {
    pub(in crate::resource::memory::workers) fn private_worker_buffer(&self, typ: &Typ) -> bool {
        (self.vector(typ) || matches!(&**typ, TypX::Decorate(TypDecoration::Box, _, _)))
            && self.plain_protected_payload(typ)
    }

    /// Fixed completion ledgers with an exportable inline or private result.
    pub(in crate::resource::memory::workers) fn phase_result(&self, typ: &Typ) -> bool {
        unit(typ)
            || contracts::scalar(typ)
            || self.private_worker_buffer(typ)
            || (self.option(typ) && self.plain_protected_payload(typ))
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
        }) || self.calls.iter().any(|(target, _)| {
            self.summaries.get(target).is_some_and(|s| s.worker_parameter().is_some())
        }) || !unit(&function.x.outer_ret.x.typ)
            || self
                .growth
                .versioned_shared
                .keys()
                .any(|root| !self.transitions.protected_histories.contains_key(root))
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
        // A completion can be charged in its publisher's subtree only while
        // its tag stays there. Handle delegation needs a separate routing proof.
        let mut children = BTreeMap::<Option<WorkerId>, Vec<WorkerId>>::new();
        for (&id, worker) in &self.growth.worker_executions {
            let mut joins = self
                .growth
                .worker_joins
                .values()
                .flatten()
                .filter(|j| j.families.contains(&id))
                .peekable();
            if joins.peek().is_none()
                || !joins.all(|j| j.families.len() == 1 && j.collects_in(worker.publication.caller))
            {
                return false;
            }
            children.entry(worker.publication.caller).or_default().push(id);
        }
        let mut order = children.get(&None).cloned().unwrap_or_default();
        let mut i = 0;
        while i < order.len() {
            if let Some(descendants) = children.get(&Some(order[i])) {
                order.extend(descendants);
            }
            i += 1;
        }
        if order.len() != self.growth.worker_executions.len() {
            return false;
        }
        let mut subtrees = BTreeMap::<Option<WorkerId>, Vec<(WorkerId, Phases)>>::new();
        for id in order.into_iter().rev() {
            let w = &self.growth.worker_executions[&id];
            let descendants = subtrees.remove(&Some(id)).unwrap_or_default();
            let Some(phases) =
                w.phases(self, &params, &reservations, &mut checks, &mut constraints, &descendants)
            else {
                return false;
            };
            subtrees.entry(w.publication.caller).or_default().push((id, phases));
        }
        let workers = subtrees.remove(&None).unwrap_or_default();
        if !self.growth.retained_worker_families.is_empty() {
            // An indexed join needs an occurrence-relative result ledger for
            // owning payloads. The fixed completion tags below cannot price it.
            if self.growth.worker_executions.len() != 1
                || self.growth.worker_executions.values().any(|w| w.result.owner.is_some())
            {
                return false;
            }
            return self.compose_population(
                function,
                workers.into_iter().collect(),
                checks,
                &constraints,
            );
        }
        let idle: BTreeMap<_, _> = self
            .transitions
            .protected_histories
            .iter()
            .map(|(&root, history)| {
                let mut phases = Phases::default();
                phases.insert(Held::new(), contracts::literal(&function.span, 0));
                phases.insert(
                    [(Class::Payload(root), 1)].into(),
                    history.idle_bytes(&function.span)?,
                );
                Some((root, phases))
            })
            .collect::<Option<_>>()
            .expect("a linked history has a publication");
        let views: Vec<_> = workers
            .iter()
            .flat_map(|(id, _)| {
                let worker = &self.growth.worker_executions[id];
                worker.versioned_roots().collect::<BTreeSet<_>>().into_iter().map(|root| {
                    (
                        worker.completion,
                        root,
                        self.published_cell_slots(*id, root).collect::<BTreeSet<_>>(),
                    )
                })
            })
            .collect();
        let native: BTreeSet<_> = self.transitions.mutex_intervals(&self.transitions).collect();
        let mut cache = BTreeMap::new();
        let mut additions = Vec::new();
        let mut cells = Vec::new();
        for p in self.storage.points() {
            let actors: Vec<_> = outstanding(p, &workers, self).collect();
            let mut roots = BTreeSet::new();
            let mut slots = BTreeSet::new();
            for (tag, root, ids) in &views {
                if p.values.contains(tag) {
                    roots.insert(*root);
                    slots.extend(ids);
                }
            }
            cells.push(slots);
            let active: Vec<_> = actors
                .iter()
                .map(|(_, phases)| *phases)
                .chain(roots.iter().map(|root| &idle[root]))
                .collect();
            if active.is_empty() {
                additions.push(None);
                continue;
            }
            // The publisher is also an actor. Preserve a held native guard
            // across its own helper calls while pricing the outstanding peers.
            let held: Held = p
                .condition
                .held
                .iter()
                .filter(|i| native.contains(i))
                .map(|i| (Class::Mutex(i.instance), 1))
                .collect();
            let key = (actors.iter().map(|(id, _)| *id).collect::<Vec<_>>(), roots, held.clone());
            let extra = cache.entry(key).or_insert_with(|| {
                let mut product = Phases::default();
                product.insert(held, contracts::literal(&p.span, 0));
                for (index, worker) in active.iter().enumerate() {
                    let remaining = active[index + 1..]
                        .iter()
                        .flat_map(|peer| peer.0.keys().flat_map(|held| held.keys().copied()))
                        .collect();
                    product = product.together(worker, &remaining, &constraints, &p.span);
                }
                product.peak(&p.span).expect("unrestricted worker entry")
            });
            additions.push(Some(extra.clone()));
        }
        self.obligations.extend(checks);
        self.storage.replace_published_cells(cells);
        self.storage.include_worker_costs(additions);
        true
    }
}
