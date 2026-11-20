//! Compose a worker's observed strong handles with its publishing domain at a
//! source checkpoint. This is a view of a possible worker phase. Observing it
//! never runs the worker or releases storage on the publisher's continuation.

mod reachability;
mod selections;
use reachability::Reachable;

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
use std::collections::{BTreeMap, BTreeSet};

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
    /// Canonical payloads reserved by this actor’s incoming handle collections.
    collections: BTreeSet<RootId>,
    selections: BTreeMap<u64, Handles>,
    /// Frame cost belongs to the checkpoint; backing costs belong to the
    /// publications where their canonical owners are in scope.
    frame: Expr,
    backing: Vec<BackingCost>,
    /// When a guard is open its actor frame already pays for the current
    /// contents. Only the Arc allocation itself is added by the publisher.
    open_payloads: BTreeSet<RootId>,
    /// Publication estimates used by this observation, excluding the Arc
    /// header and inline payload. After a peer write, only a type-invariant
    /// price can justify these estimates.
    publication_payloads: BTreeMap<RootId, Option<u64>>,
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
    ) -> Result<(), VirErr> {
        if self.growth.versioned_shared.iter().any(|(id, fixed)| {
            fixed.is_none()
                && self
                    .heap
                    .shared
                    .roots
                    .get(id)
                    .is_some_and(|r| matches!(r.storage, Backing::Owned(_)))
        }) {
            return Err(unsupported(
                span,
                "a checkpoint on owned shared backing before composing its worker updates",
            ));
        }
        if self.current_worker.is_none() {
            return Ok(());
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
        let collections: BTreeSet<_> = self.transitions.collection_claims.keys().copied().collect();
        if !handles.is_empty() || !selections.is_empty() || !collections.is_empty() {
            self.transitions.shared_checkpoints.push(Checkpoint {
                site: span.clone(),
                handles,
                selections,
                collections,
                frame: frame.total(),
                backing: Vec::new(),
                open_payloads: self.transitions.protected_versions.open_roots(&self.heap).collect(),
                publication_payloads: BTreeMap::new(),
                publisher_guard: None,
                limit,
            });
        }
        Ok(())
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
            let Reachable { fixed: mut counts, indexed_ancestors } =
                self.at_worker_checkpoint(check)?;
            let (selected, selections) = self.heap.shared.project_selections(check)?;
            let mut imports = BTreeMap::new();
            let mut owned = Vec::new();
            let mut projected = check.clone();
            // A known owner reaches its backing regardless of any separate
            // selected alias's identity. Charge it once through the union.
            let fixed: BTreeSet<_> = counts.keys().copied().collect();
            for id in selected.keys() {
                if self
                    .growth
                    .indexed_shared
                    .get(id)
                    .is_some_and(|claims| claims.backing.references() != super::References::None)
                {
                    return Err(unsupported(
                        span,
                        "a mixed selected worker checkpoint with nested shared or worker handles",
                    ));
                }
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
                        if live == 0 && indexed_ancestors.contains_key(&id) {
                            return Err(unsupported(
                                span,
                                "an indexed payload edge across two worker checkpoint scopes",
                            ));
                        }
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
                let ancestors = indexed_ancestors.get(&id);
                if live == 0 && claims.is_none() && peers.is_none() && ancestors.is_none() {
                    continue;
                }
                let mut holds_job = false;
                backing.visit(&mut |node| {
                    holds_job |= node.worker.is_some()
                        || node.selected_worker.is_some()
                        || node
                            .elements
                            .as_ref()
                            .is_some_and(|e| e.references == super::References::WorkerOccurrences);
                });
                if holds_job {
                    return Err(unsupported(
                        span,
                        "a worker checkpoint with outstanding jobs inside shared backing",
                    ));
                }
                let (mut bytes, proof) = projected.price_backing(self, publication, id, backing)?;
                let proofs = self.growth.after.entry(publication.id).or_default();
                proofs.extend(proof);
                let candidates = selected.get(&id);
                let mut dependencies = Vec::new();
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
                    dependencies.push(remaining);
                }
                if let Some(peers) = peers {
                    dependencies.push(peers.population.pending.clone());
                }
                // A conditional publisher count and a symbolic receiver frame
                // belong to separate proof scopes. A known full backing size
                // is a conservative allowance through the collector's join.
                let reserved_by_collector = check.collections.contains(&id)
                    || ancestors.is_some_and(|roots| !roots.is_disjoint(&check.collections));
                let full_allowance = reserved_by_collector
                    && contracts::constant(&check.frame).is_none()
                    && contracts::constant(&bytes).is_some();
                if live == 0 && !full_allowance {
                    for ancestor in ancestors.into_iter().flatten() {
                        if let Some(claims) = self.growth.indexed_shared.get(ancestor) {
                            dependencies.push(claims.population.pending.clone());
                        }
                        if let Some(peers) = self.growth.occurrence_peers.get(ancestor) {
                            dependencies.push(peers.population.pending.clone());
                        }
                    }
                    let zero = contracts::literal(span, 0);
                    let idle = dependencies
                        .iter()
                        .map(|count| crate::ast_util::mk_eq(span, count, &zero))
                        .collect();
                    bytes = super::super::growth::select(
                        span,
                        crate::ast_util::conjoin(span, &idle),
                        zero,
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
            projected.collections.clear();
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
                if projected.publication_payloads.is_empty() {
                    projected.emit(self)?;
                } else {
                    self.growth.protected_checkpoints.push(projected);
                }
            } else {
                self.transitions.shared_checkpoints.push(projected);
            }
        }
        Ok(())
    }
}

impl Checkpoint {
    /// The actor already pays for the payload held under its guard. For a
    /// closed view, remember which part of a publication estimate depends on
    /// the contents. Its validity may depend on a peer published later.
    fn price_backing(
        &mut self,
        analysis: &Analysis<'_>,
        publication: &Span,
        root: RootId,
        backing: &super::Owner,
    ) -> Result<(Expr, Option<Stmt>), VirErr> {
        let fixed_header = backing.dynamic.is_none() && backing.fixed_role.is_some();
        if self.open_payloads.contains(&root) {
            if !fixed_header {
                return Err(unsupported(
                    &self.site,
                    "an acquired payload without a separate canonical Arc allocation",
                ));
            }
            return Ok((contracts::literal(publication, backing.bytes), None));
        }
        let cost = analysis.checkpoint_backing(publication, backing)?;
        if backing.children.get(&super::OwnerSlot::Contents).is_some_and(|owner| {
            owner.mutex_instance().is_some()
                && owner.children.contains_key(&super::OwnerSlot::Contents)
        }) {
            let payload = contracts::constant(&cost.0)
                .filter(|_| fixed_header)
                .and_then(|bytes| bytes.checked_sub(backing.bytes));
            self.publication_payloads.insert(root, payload);
        }
        Ok(cost)
    }

    /// At this point the verifier has seen every worker. A publication-time
    /// price survives a peer update only when its value follows from the type.
    pub(in super::super) fn resolve_publication(
        self,
        analysis: &mut Analysis<'_>,
    ) -> Result<(), VirErr> {
        if self.publication_payloads.iter().any(|(root, estimate)| {
            analysis
                .growth
                .versioned_shared
                .get(root)
                .is_some_and(|fixed| fixed.is_none() || fixed != estimate)
        }) {
            return Err(unsupported(
                &self.site,
                "a worker checkpoint requiring the current shared payload after a peer update",
            ));
        }
        self.emit(analysis)
    }

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
