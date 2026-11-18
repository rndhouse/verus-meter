//! Compose a worker's observed strong handles with its publishing domain at a
//! source checkpoint. This is a view of a possible worker phase. Observing it
//! never runs the worker or releases storage on the publisher's continuation.

mod selections;

use super::{Backing, RootId, SharedRoots, StrongLink};
use crate::{
    ast::*,
    messages::Span,
    resource::memory::{
        accounting::{CheckKind, Obligation},
        analysis::Analysis,
        contracts,
        footprint::{Footprint, MemoryBudget},
        model::unsupported,
        workers::WorkerId,
    },
};
use std::collections::BTreeMap;

/// Replace only the references lent to this subtree. Strong references in
/// siblings, completed results, or retained publisher locals stay outstanding.
#[derive(Clone, Copy)]
pub(super) struct Handles {
    pub(super) entry: u64,
    pub(super) live: u64,
}

impl Handles {
    /// Replace a disjoint subtree's entry references by its current ones.
    /// This same relation applies at a checkpoint and at collection.
    pub(super) fn in_domain(self, total: u64) -> Option<u64> {
        total.checked_sub(self.entry)?.checked_add(self.live)
    }
}

#[derive(Clone)]
pub(in super::super) struct Checkpoint {
    site: Span,
    handles: BTreeMap<RootId, Handles>,
    selections: BTreeMap<u64, Handles>,
    /// Frame cost belongs to the checkpoint; backing costs belong to the
    /// publications where their canonical owners are in scope.
    frame: Expr,
    backing: Vec<BackingCost>,
    /// Necessary source path conditions expressible using immutable captures.
    publisher_guard: Option<Expr>,
    limit: u64,
}

#[derive(Clone)]
struct BackingCost {
    publication: Span,
    bytes: Expr,
    guard: Option<Expr>,
}

impl SharedRoots {
    fn imports_at_checkpoint(&self) -> BTreeMap<RootId, Handles> {
        self.roots
            .iter()
            .filter_map(|(id, root)| {
                if let Backing::Imported { entry } = root.storage {
                    Some((*id, Handles { entry, live: root.strong }))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Find the fixed ownership graph reachable from these imports, then
    /// propagate final drops through it. Two edges to one root are two
    /// strong references, but its control block and payload are charged once.
    fn at_worker_checkpoint(
        &self,
        checkpoint: &Checkpoint,
        indexed: impl Fn(RootId) -> bool,
    ) -> Result<BTreeMap<RootId, u64>, VirErr> {
        let span = &checkpoint.site;
        let mut counts = BTreeMap::new();
        let mut children = BTreeMap::new();
        let mut pending: Vec<_> = checkpoint.handles.keys().copied().collect();
        while let Some(id) = pending.pop() {
            if counts.contains_key(&id) {
                continue;
            }
            let root = self.roots.get(&id).ok_or_else(|| {
                unsupported(span, "a worker checkpoint outside its shared allocation domain")
            })?;
            let mut count = root.strong;
            if let Some(observed) = checkpoint.handles.get(&id) {
                count = observed.in_domain(count).ok_or_else(|| {
                    unsupported(span, "inconsistent checkpoint strong-reference counts")
                })?;
            }
            counts.insert(id, count);
            if let Backing::Owned(owner) = &root.storage {
                let mut edges = Vec::new();
                super::visit_strong_handles(owner, span, super::References::None, |link| {
                    let StrongLink::Known(child) = link else {
                        return Err(unsupported(
                            span,
                            "a selected alias inside a worker checkpoint backing",
                        ));
                    };
                    edges.push(child);
                    Ok(())
                })?;
                pending.extend(edges.iter().copied());
                children.insert(id, edges);
            }
        }
        let mut dead: Vec<_> =
            counts.iter().filter_map(|(id, count)| (*count == 0).then_some(*id)).collect();
        while let Some(id) = dead.pop() {
            // The outstanding symbolic count remains a separate retention
            // condition. Indexed backing currently has byte-only descendants.
            if indexed(id) {
                continue;
            }
            for child in children.remove(&id).into_iter().flatten() {
                let count = counts.get_mut(&child).unwrap();
                *count = count.checked_sub(1).ok_or_else(|| {
                    unsupported(span, "duplicate final destruction of a shared payload")
                })?;
                if *count == 0 {
                    dead.push(child);
                }
            }
        }
        Ok(counts)
    }
}

impl Analysis<'_> {
    /// Transfer a literal byte allowance into the worker only after the
    /// publisher proves it covers its actual immutable backing. This lets
    /// path-dependent worker costs stay at their original source checkpoint.
    fn checkpoint_backing(
        &self,
        span: &Span,
        owner: &super::Owner,
    ) -> Result<(Expr, Option<Stmt>), VirErr> {
        let total = |charges: BTreeMap<_, _>| {
            charges
                .into_values()
                .fold(contracts::literal(span, 0), |a, b| contracts::add(span, a, b))
        };
        let mut present = true;
        let mut stable = true;
        owner.visit(&mut |node| {
            present &= node.dynamic.is_none_or(|id| self.storage.contains_allocation(id))
                && node.elements.as_ref().is_none_or(|elements| {
                    elements
                        .states
                        .values()
                        .all(|id| self.storage.contains_allocation(self.growth.elements[*id].id))
                });
            stable &= node.vector.is_none_or(|id| !self.growth.vectors[id].backing.changed)
                && node.elements.as_ref().is_none_or(|e| e.zero_charge(&self.growth))
                && (node.dynamic.is_none() || node.vector.is_some() || node.extent.is_some());
        });
        if !present {
            return Err(unsupported(
                span,
                "a shared checkpoint outside its backing's charging scope",
            ));
        }
        let bytes = total(self.owner_charges(span, owner));
        if stable && contracts::constant(&bytes).is_none() {
            let upper = total(self.owner_upper(span, owner));
            if contracts::constant(&upper).is_some() {
                let check = Obligation {
                    span: span.clone(),
                    cost: Footprint::allowance(bytes),
                    bound: MemoryBudget::total(upper.clone()),
                    kind: CheckKind::WorkerState("for captured shared backing at publication"),
                };
                return Ok((upper, super::super::symbolic::obligation(&check)));
            }
        }
        Ok((bytes, None))
    }

    pub(in super::super) fn observe_shared_checkpoint(
        &mut self,
        span: &Span,
        frame: &Footprint,
        limit: u64,
    ) {
        if self.current_worker.is_none() {
            return;
        }
        let handles = self.heap.shared.imports_at_checkpoint();
        let selections: BTreeMap<_, _> = self
            .heap
            .shared
            .selections
            .iter()
            .filter_map(|(id, alias)| {
                Some((*id, Handles { entry: alias.imported?, live: alias.handles }))
            })
            .collect();
        if !handles.is_empty() || !selections.is_empty() {
            self.transitions.shared_checkpoints.push(Checkpoint {
                site: span.clone(),
                handles,
                selections,
                frame: frame.total(),
                backing: Vec::new(),
                publisher_guard: None,
                limit,
            });
        }
    }

    /// Hoist a condition only when its value is fixed by the captured operands.
    /// An unexportable condition leaves the publication check conservative.
    pub(in super::super) fn guard_shared_checkpoints(
        &mut self,
        cond: &Expr,
        start: usize,
        otherwise: usize,
    ) {
        if start == self.transitions.shared_checkpoints.len() {
            return;
        }
        let Some(condition) = self.captured_checkpoint_guard(cond) else {
            return;
        };
        for (i, point) in self.transitions.shared_checkpoints.iter_mut().enumerate().skip(start) {
            let guard = if i < otherwise {
                condition.clone()
            } else {
                SpannedTyped::new(
                    &cond.span,
                    &condition.typ,
                    ExprX::Unary(UnaryOp::Not, condition.clone()),
                )
            };
            point.publisher_guard = Some(match point.publisher_guard.take() {
                None => guard,
                Some(outer) => crate::ast_util::conjoin(&cond.span, &vec![guard, outer]),
            });
        }
    }

    pub(in super::super) fn compose_shared_checkpoints(
        &mut self,
        actor: WorkerId,
        publication: &Span,
    ) -> Result<(), VirErr> {
        let worker = self.growth.worker_executions[&actor].clone();
        for check in worker.shared_checkpoints() {
            let span = &check.site;
            let mut counts = self.heap.shared.at_worker_checkpoint(check, |id| {
                self.growth.indexed_shared.contains_key(&id)
                    || self.growth.occurrence_peers.contains_key(&id)
            })?;
            let (selected, selections) = self.heap.shared.project_selections(check)?;
            let mut imports = BTreeMap::new();
            let mut owned = Vec::new();
            // A candidate already reached through a fixed handle is observed
            // regardless of the selected result's identity.
            let fixed: std::collections::BTreeSet<_> = counts.keys().copied().collect();
            for id in selected.keys() {
                counts
                    .entry(*id)
                    .or_insert_with(|| self.heap.shared.roots.get(id).map_or(0, |r| r.strong));
            }
            for (id, live) in counts {
                if self.growth.peer_results.contains_key(&id) {
                    return Err(unsupported(
                        span,
                        "observing a returned peer backing from another actor",
                    ));
                }
                let claims = self.growth.indexed_shared.get(&id);
                let backing = match self.heap.shared.roots.get(&id).map(|r| &r.storage) {
                    Some(Backing::Imported { entry }) => {
                        imports.insert(id, Handles { entry: *entry, live });
                        continue;
                    }
                    Some(Backing::Owned(backing)) => backing,
                    None => {
                        &claims
                            .ok_or_else(|| {
                                unsupported(
                                    span,
                                    "a selected checkpoint without its canonical backing",
                                )
                            })?
                            .backing
                    }
                };
                let peers = self.growth.occurrence_peers.get(&id);
                if live == 0 && claims.is_none() && peers.is_none() {
                    continue;
                }
                let (mut bytes, proof) = self.checkpoint_backing(publication, backing)?;
                let proofs = self.growth.after.entry(publication.id).or_default();
                proofs.extend(proof);
                let candidates = selected.get(&id);
                if let Some(claims) = claims {
                    let remaining = match candidates.and_then(|s| s.released.clone()) {
                        Some(debit) => claims.population.after_release(
                            span,
                            debit,
                            "cannot reconcile the selected Arc's checkpoint reservation",
                            proofs,
                        ),
                        None => claims.population.pending.clone(),
                    };
                    if live == 0 {
                        let empty =
                            crate::ast_util::mk_eq(span, &remaining, &contracts::literal(span, 0));
                        bytes = super::super::growth::select(
                            span,
                            empty,
                            contracts::literal(span, 0),
                            bytes,
                        );
                    }
                }
                if live == 0
                    && let Some(peers) = peers
                {
                    let idle = crate::ast_util::mk_eq(
                        span,
                        &peers.population.pending,
                        &contracts::literal(span, 0),
                    );
                    bytes = super::super::growth::select(
                        span,
                        idle,
                        contracts::literal(span, 0),
                        bytes,
                    );
                }
                if !fixed.contains(&id) {
                    let matched = crate::ast_util::disjoin(span, &selected[&id].matches);
                    bytes = super::super::growth::select(
                        span,
                        matched,
                        bytes,
                        contracts::literal(span, 0),
                    );
                }
                owned.push(bytes);
            }
            let mut projected = check.clone();
            projected.handles = imports;
            projected.selections = selections;
            let guard = projected.publisher_guard.take();
            if !owned.is_empty() {
                let bytes = owned
                    .into_iter()
                    .fold(contracts::literal(span, 0), |a, b| contracts::add(span, a, b));
                projected.backing.push(BackingCost {
                    publication: publication.clone(),
                    bytes,
                    guard,
                });
            }
            if projected.handles.is_empty() && projected.selections.is_empty() {
                projected.emit(self)?;
            } else {
                self.transitions.shared_checkpoints.push(projected);
            }
        }
        Ok(())
    }
}

impl Checkpoint {
    /// Constants may be combined across scopes. A symbolic cost must be
    /// checked where its proof variables describe this particular execution.
    fn emit(self, analysis: &mut Analysis<'_>) -> Result<(), VirErr> {
        if self.backing.is_empty() {
            return Ok(());
        }
        let mut cost = self.frame;
        let mut publication = None;
        for BackingCost { publication: site, bytes, guard } in self.backing {
            if contracts::constant(&bytes).is_none() {
                if contracts::constant(&cost).is_none() {
                    return Err(unsupported(
                        &self.site,
                        "independently symbolic worker and publisher checkpoint costs",
                    ));
                }
                publication = Some((site, guard));
            }
            cost = contracts::add(&self.site, cost, bytes);
        }
        if let Some((_, Some(guard))) = &publication {
            cost = contracts::simplify(&super::super::growth::select(
                &self.site,
                guard.clone(),
                cost,
                contracts::literal(&self.site, 0),
            ));
        }
        let check = Obligation {
            span: self.site.clone(),
            cost: Footprint::allowance(cost),
            bound: MemoryBudget::total(contracts::literal(&self.site, self.limit)),
            kind: CheckKind::WorkerState("at a worker checkpoint with shared backing"),
        };
        if let Some(stmt) = super::super::symbolic::obligation(&check) {
            match publication {
                Some((site, _)) => analysis.growth.after.entry(site.id).or_default().push(stmt),
                None => analysis.growth.before.entry(self.site.id).or_default().push(stmt),
            }
        }
        Ok(())
    }
}
