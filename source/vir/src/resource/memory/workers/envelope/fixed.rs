//! Compose the publisher's live storage and its fixed worker subtrees at one observation.

use super::*;
use crate::resource::memory::{shared::RootId, synchronization::local::Interval};

/// An outstanding publication can cover these allocations in the publisher's ledger.
struct PublishedCell {
    completion: u64,
    root: RootId,
    allocations: BTreeSet<u64>,
}

pub(super) struct FixedWorkers<'a> {
    workers: &'a [(WorkerId, Phases)],
    constraints: &'a Constraints,
    /// Storage a shared cell can retain between acquisitions.
    idle: BTreeMap<RootId, Phases>,
    published_cells: Vec<PublishedCell>,
    /// Publisher acquisitions known to exclude a worker on the same mutex.
    mutexes: BTreeSet<Interval>,
    /// Cache only the worker and shared-cell contribution. The publisher's own
    /// ledger and the allocations it still charges can differ at each point.
    peaks: BTreeMap<(Vec<WorkerId>, BTreeSet<RootId>, Held), Expr>,
}

impl<'a> FixedWorkers<'a> {
    pub(super) fn new(
        analysis: &Analysis<'_>,
        span: &Span,
        actor: Option<&Execution>,
        workers: &'a [(WorkerId, Phases)],
        constraints: &'a Constraints,
    ) -> Self {
        let idle = analysis
            .transitions
            .protected_histories
            .iter()
            .map(|(&root, history)| {
                let mut phases = Phases::default();
                phases.insert(Held::new(), contracts::literal(span, 0));
                phases.insert(
                    [(Class::Payload(root), 1)].into(),
                    history.idle_bytes(span).expect("a linked history has a publication"),
                );
                (root, phases)
            })
            .collect();
        let mut published_cells = Vec::new();
        for (id, _) in workers {
            let worker = &analysis.growth.worker_executions[id];
            for root in worker.versioned_roots().collect::<BTreeSet<_>>() {
                published_cells.push(PublishedCell {
                    completion: worker.completion,
                    root,
                    allocations: analysis.published_cell_slots(*id, root).collect(),
                });
            }
        }
        let effects = actor.map_or(&analysis.transitions, |execution| &execution.effects.ownership);
        let mutexes = effects.mutex_intervals(&analysis.transitions).collect();
        Self { workers, constraints, idle, published_cells, mutexes, peaks: BTreeMap::new() }
    }

    /// Return the simultaneous total, or leave the local footprint intact when
    /// neither a worker nor a published cell can contribute at this observation.
    pub(super) fn cost_at(&mut self, point: &Point, growth: &Growth) -> Option<Footprint> {
        let (extra, covered) = self.contribution(point, growth)?;
        Some(point.with_worker_cost(extra, &covered))
    }

    /// Worker-phase expressions use the top publisher's immutable parameters.
    /// Rebind only that contribution before adding the observing worker's local bytes.
    pub(super) fn worker_cost_at(
        &mut self,
        point: &Point,
        analysis: &Analysis<'_>,
        worker: &Execution,
        params: &HashSet<VarIdent>,
    ) -> Result<Option<Footprint>, VirErr> {
        let Some((extra, covered)) = self.contribution(point, &analysis.growth) else {
            return Ok(None);
        };
        let missing = || {
            crate::resource::memory::model::unsupported(
                &point.span,
                "a descendant byte bound without an immutable capture in the observing worker",
            )
        };
        let captures = worker.phase_inputs(analysis, params, &point.span).ok_or_else(missing)?;
        let mut local = HashMap::new();
        for (name, source) in captures {
            if let ExprX::Var(formal) = &source.x {
                local.insert(
                    formal.clone(),
                    SpannedTyped::new(&point.span, &source.typ, ExprX::Var(name)),
                );
            }
        }
        let names = crate::resource::memory::synchronization::versions::operands(&extra)
            .ok_or_else(missing)?;
        if !names.iter().all(|n| local.contains_key(n)) {
            return Err(missing());
        }
        Ok(Some(point.with_worker_cost(simplify::specialize(&extra, &local), &covered)))
    }

    fn contribution(&mut self, point: &Point, growth: &Growth) -> Option<(Expr, BTreeSet<u64>)> {
        let actors: Vec<_> = outstanding(point, self.workers, growth).collect();
        let mut roots = BTreeSet::new();
        let mut covered = BTreeSet::new();
        for cell in &self.published_cells {
            if point.values.contains(&cell.completion) {
                roots.insert(cell.root);
                covered.extend(&cell.allocations);
            }
        }
        if actors.is_empty() && roots.is_empty() {
            return None;
        }
        // A native guard held by the publisher also constrains workers while
        // the publisher runs a helper.
        let held: Held = point
            .condition
            .held
            .iter()
            .filter(|i| self.mutexes.contains(i))
            .map(|i| (Class::Mutex(i.instance), 1))
            .collect();
        let ids = actors.iter().map(|(id, _)| *id).collect();
        let extra = self.peaks.entry((ids, roots, held)).or_insert_with_key(|(_, roots, held)| {
            let active: Vec<_> = actors
                .iter()
                .map(|(_, phases)| *phases)
                .chain(roots.iter().map(|root| &self.idle[root]))
                .collect();
            let mut product = Phases::default();
            product.insert(held.clone(), contracts::literal(&point.span, 0));
            for (index, worker) in active.iter().enumerate() {
                let remaining = active[index + 1..]
                    .iter()
                    .flat_map(|peer| peer.0.keys().flat_map(|held| held.keys().copied()))
                    .collect();
                product = product.together(worker, &remaining, self.constraints, &point.span);
            }
            product.peak(&point.span).expect("unrestricted worker entry")
        });
        Some((extra.clone(), covered))
    }
}
