//! Compose the publisher's live storage and its fixed worker subtrees at one observation.

use super::*;
use crate::resource::memory::{shared::RootId, synchronization::local::Interval};

/// An outstanding publication can cover these allocations in the publisher's ledger.
struct PublishedCell {
    completion: u64,
    root: RootId,
    allocations: BTreeSet<u64>,
}

pub(super) struct FixedWorkers {
    workers: Vec<(WorkerId, Phases)>,
    constraints: Constraints,
    /// Storage a shared cell can retain between acquisitions.
    idle: BTreeMap<RootId, Phases>,
    published_cells: Vec<PublishedCell>,
    /// Publisher acquisitions known to exclude a worker on the same mutex.
    mutexes: BTreeSet<Interval>,
    /// Cache only the worker and shared-cell contribution. The publisher's own
    /// ledger and the allocations it still charges can differ at each point.
    peaks: BTreeMap<(Vec<WorkerId>, BTreeSet<RootId>, Held), Expr>,
}

impl FixedWorkers {
    pub(super) fn new(
        analysis: &Analysis<'_>,
        span: &Span,
        workers: Vec<(WorkerId, Phases)>,
        constraints: Constraints,
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
        for (id, _) in &workers {
            let worker = &analysis.growth.worker_executions[id];
            for root in worker.versioned_roots().collect::<BTreeSet<_>>() {
                published_cells.push(PublishedCell {
                    completion: worker.completion,
                    root,
                    allocations: analysis.published_cell_slots(*id, root).collect(),
                });
            }
        }
        let mutexes = analysis.transitions.mutex_intervals(&analysis.transitions).collect();
        Self { workers, constraints, idle, published_cells, mutexes, peaks: BTreeMap::new() }
    }

    /// Return the simultaneous total, or leave the local footprint intact when
    /// neither a worker nor a published cell can contribute at this observation.
    pub(super) fn cost_at(&mut self, point: &Point, growth: &Growth) -> Option<Footprint> {
        let actors: Vec<_> = outstanding(point, &self.workers, growth).collect();
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
                product = product.together(worker, &remaining, &self.constraints, &point.span);
            }
            product.peak(&point.span).expect("unrestricted worker entry")
        });
        Some(point.with_worker_cost(extra.clone(), &covered))
    }
}
