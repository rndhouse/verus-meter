//! Runtime collections of owning children, independent of container layout.
//!
//! A collection keeps one byte sum per memory kind and an erased allocation
//! forest for individually modeled children. Insertion, indexed loans and
//! extraction transfer complete subtrees. Opaque input allocations remain
//! caller-charged and retain their provenance.

use super::analysis::Analysis;
use super::contracts;
use super::footprint::MemoryKind;
use super::heap::{Owner, OwnerPath};
use super::model::unsupported;
use crate::ast::*;
use crate::ast_util::{int_typ, mk_ineq};
use crate::messages::Span;
use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

#[derive(Clone)]
pub(super) struct Elements {
    /// Whether records cover all allocations or only charges introduced in this frame.
    pub(super) view: super::metadata::View,
    /// Uniform reservation candidates, indexed by ownership class.
    pub(super) minima: super::metadata::reservations::Minima,
    /// Current collection value; a move rebinds this to its destination.
    pub(super) source: Option<(Typ, Expr)>,
    /// Allocation data indexed by child paths. A local view starts empty because
    /// every incoming allocation remains charged to the caller.
    pub(super) records: Expr,
    /// Pending forest snapshot committed after the executable operation.
    pub(super) next_records: Expr,
    /// Every allocation charge in this view has descriptors; opaque additions disable this.
    pub(super) precise: bool,
    /// Stable counter identities; the containing owner controls their lifetime.
    pub(super) states: BTreeMap<MemoryKind, usize>,
    /// Disjoint input nodes captured by element insertion.
    pub(super) inputs: HashSet<usize>,
}

#[derive(Clone)]
pub(super) struct ElementSummary {
    /// Inputs transferred into this collection, consumed exactly once at calls.
    pub(super) inputs: HashSet<usize>,
}

pub(super) struct ElementState {
    /// Forest whose local charge this state tracks, shared by its memory kinds.
    pub(super) records: Expr,
    /// Accounting identity of this sum.
    pub(super) id: u64,
    /// Memory kind preserved when a child is transferred.
    kind: MemoryKind,
    /// Bytes inherited when this state was introduced.
    initial: Expr,
    /// A compositional bound for straight-line additions; repeated updates are
    /// summarized by the checked function budget instead.
    extent: Option<Expr>,
    /// Erased current and next byte totals.
    pub(super) bytes: Expr,
    next_bytes: Expr,
    /// Number of locally modeled insertions, separate from incoming elements.
    count: Expr,
    next_count: Expr,
    /// Upper bound on each insertion's child footprint, proved at its operation.
    maximum: Expr,
    /// A direct insertion's logical collection length, used by loop proofs.
    length: Option<Expr>,
    /// Forest replacement and removal invalidate the direct insertion count.
    counted: bool,
    /// Whether local operations have added child allocations.
    pub(super) changed: bool,
    /// No positive local charge has existed in this state. Descriptor-only
    /// writes preserve this invariant; allocating writes invalidate it.
    uncharged: bool,
}

impl ElementState {
    pub(super) fn entry_upper(&self) -> Option<Expr> {
        self.extent.clone()
    }

    /// Cutting or reindexing an initially uncharged forest cannot add bytes.
    pub(super) fn unchanged_zero(&self) -> bool {
        self.uncharged
    }
}

impl Elements {
    pub(super) fn zero_charge(&self, growth: &super::growth::Growth) -> bool {
        self.states.values().all(|id| growth.elements[*id].unchanged_zero())
    }
}

impl ElementState {
    /// Removal invalidates the relationship between insertion count and length.
    pub(super) fn forget_length(&mut self) {
        self.counted = false;
        self.length = None;
    }

    fn upper(&self, _span: &Span, fallback: &Expr) -> Expr {
        self.extent.clone().unwrap_or_else(|| fallback.clone())
    }
}

/// Input ownership transferred into a runtime collection. Byte-only summaries
/// cannot be applied at calls; the corresponding forest template is required.
pub(super) fn summarize(elements: &Elements) -> ElementSummary {
    ElementSummary { inputs: elements.inputs.clone() }
}

pub(super) fn additions(
    owner: &Owner,
    growth: &super::growth::Growth,
) -> BTreeMap<OwnerPath, ElementSummary> {
    let mut effects = BTreeMap::new();
    owner.visit_paths(&mut vec![], &mut |path, node| {
        if let Some(effect) = addition(node, growth) {
            effects.insert(path.clone(), effect);
        }
    });
    effects
}

/// Additions belonging to one node, excluding its fixed children.
pub(super) fn addition(owner: &Owner, growth: &super::growth::Growth) -> Option<ElementSummary> {
    let elements = owner.elements.as_ref()?;
    (!elements.inputs.is_empty() || elements.states.values().any(|id| growth.elements[*id].changed))
        .then(|| summarize(elements))
}

impl Analysis<'_> {
    /// A helper's predicted forest updates the existing counters, so branch
    /// joins and reusable iterations continue to refer to the same states.
    pub(super) fn commit_transferred_elements(
        &mut self,
        span: &Span,
        old: &mut Elements,
        new: &Elements,
    ) {
        self.growth.after.entry(span.id).or_default().push(super::metadata::expr::assign(
            span,
            &old.records,
            new.records.clone(),
        ));
        for (kind, id) in &old.states {
            let uncharged = self.growth.elements[new.states[kind]].uncharged;
            let next = self.growth.elements[new.states[kind]].bytes.clone();
            let state = &mut self.growth.elements[*id];
            self.growth.after.entry(span.id).or_default().push(super::symbolic::assign(
                span,
                &state.bytes,
                next.clone(),
            ));
            self.growth.element_updates.entry(span.id).or_default().insert(*id, next);
            state.changed = true;
            state.uncharged &= uncharged;
            state.counted = false;
            state.length = None;
            state.extent = None;
        }
        old.precise = true;
        old.minima = new.minima.clone();
    }

    /// Commit the byte counters corresponding to a precise forest. Snapshot
    /// substitutions keep the peak check at the operation's original location.
    pub(super) fn set_element_records(&mut self, span: &Span, elements: &Elements, after: bool) {
        let proof = super::metadata::expr::lemma(
            span,
            "inspect",
            vec![elements.records.clone(), super::metadata::expr::path(span, [])],
        );
        if after {
            self.growth.after.entry(span.id).or_default().push(proof);
        } else {
            self.growth.before.entry(span.id).or_default().push(proof);
        }
        for (kind, id) in &elements.states {
            let amount = self.metadata_cost(span, elements.records.clone(), kind);
            let state = &self.growth.elements[*id];
            let assignment = super::symbolic::assign(span, &state.bytes, amount);
            if after {
                self.growth.after.entry(span.id).or_default().push(assignment);
            } else {
                self.growth.before.entry(span.id).or_default().push(assignment);
            }
        }
    }

    pub(super) fn return_element_loan(
        &mut self,
        span: &Span,
        elements: &mut Elements,
        original: Expr,
        path: Expr,
        child: Owner,
        changed: bool,
    ) -> Result<(), VirErr> {
        if !changed {
            // A checked read-only loan did not change any descriptor. Restore
            // its saved forest directly instead of rebuilding it through the
            // executable value, which would discard frame/count information
            // and multiply nested selection proofs at loop conditions.
            self.retire_element_loan(span, &child);
            self.release_owner_storage(child, span, false);
            self.growth.after.entry(span.id).or_default().push(super::metadata::expr::assign(
                span,
                &elements.records,
                original,
            ));
            self.set_element_records(span, elements, true);
            for id in elements.states.values() {
                let bytes = self.growth.elements[*id].bytes.clone();
                let next = self.growth.after_value(span, &bytes);
                self.growth.element_updates.entry(span.id).or_default().insert(*id, next);
            }
            return Ok(());
        }
        let uncharged = self.growth.owner_zero_charge(&child);
        self.merge_element_minima(span, elements, &child);
        let mut proofs = Vec::new();
        let child_records = self.owner_metadata(span, &child, &mut proofs);
        // Peak checks precede the executable operation. Instantiate the cost
        // algebra on its pending values; validity is checked after committing.
        let mut pending_proofs = Vec::new();
        for proof in &proofs {
            if let StmtX::Expr(value) = &proof.x {
                if let ExprX::Call { target: CallTarget::Fun(_, fun, _, _, _), .. } = &value.x {
                    if matches!(fun.path.segments.last(), Some(Segment::V(name, _)) if name.starts_with("cost_"))
                    {
                        pending_proofs.push(crate::def::Spanned::new(
                            span.clone(),
                            StmtX::Expr(self.growth.after_value(span, value)),
                        ));
                    }
                }
            }
        }
        let nested = super::metadata::expr::prefix(span, child_records.clone(), path.clone());
        pending_proofs.extend([
            super::metadata::expr::lemma(
                span,
                "cost_prefix",
                vec![
                    self.growth.after_value(span, &child_records),
                    path.clone(),
                    contracts::literal(span, 0),
                ],
            ),
            super::metadata::expr::lemma(
                span,
                "cost_add",
                vec![
                    elements.records.clone(),
                    self.growth.after_value(span, &nested),
                    contracts::literal(span, 0),
                ],
            ),
        ]);
        self.growth.before.entry(span.id).or_default().extend(pending_proofs);
        proofs.extend([
            super::metadata::expr::lemma(
                span,
                "well_formed_prefix",
                vec![child_records.clone(), path.clone()],
            ),
            super::metadata::expr::lemma(
                span,
                "well_formed_add",
                vec![elements.records.clone(), nested.clone()],
            ),
            super::metadata::expr::lemma(
                span,
                "cost_prefix",
                vec![child_records.clone(), path.clone(), contracts::literal(span, 0)],
            ),
            super::metadata::expr::lemma(
                span,
                "cost_add",
                vec![elements.records.clone(), nested.clone(), contracts::literal(span, 0)],
            ),
            super::metadata::expr::assign(
                span,
                &elements.records,
                super::metadata::operations::attach(
                    span,
                    elements.records.clone(),
                    path.clone(),
                    child_records.clone(),
                ),
            ),
        ]);
        self.growth.after.entry(span.id).or_default().extend(proofs);
        self.prove_element_frame(span, elements, original, path, child_records);
        self.retire_element_loan(span, &child);
        elements.inputs.extend(child.inputs());
        child.visit(&mut |node| {
            if !node.inputs().is_empty()
                || node.elements.as_ref().is_some_and(|e| !e.precise)
                || (!node.geometry_known && node.source.is_none())
            {
                elements.precise = false;
            }
        });
        self.release_owner_storage(child, span, false);
        self.set_element_records(span, elements, true);
        self.assert_element_minima(span, elements, true)?;
        for id in elements.states.values() {
            let state = &mut self.growth.elements[*id];
            state.changed |= changed;
            state.uncharged &= uncharged;
            state.counted = false;
            state.length = None;
            state.extent = None;
            let bytes = state.bytes.clone();
            let next = self.growth.after_value(span, &bytes);
            self.growth.element_updates.entry(span.id).or_default().insert(*id, next);
        }
        Ok(())
    }

    /// Loan-local child counters must not commit after their temporary owner
    /// has been retired, independently of whether the loan changed ownership.
    fn retire_element_loan(&mut self, span: &Span, child: &Owner) {
        child.visit(&mut |node| {
            if let Some(elements) = &node.elements {
                for id in elements.states.values() {
                    if let Some(updates) = self.growth.element_updates.get_mut(&span.id) {
                        updates.remove(id);
                    }
                }
            }
        });
    }

    pub(super) fn new_elements(&mut self, span: &Span) -> Elements {
        // The currently supported allocation adapters all allocate host heap
        // storage. Adoption uses the summary's kinds; the sum machinery is generic.
        self.elements_from_bytes(
            span,
            [(MemoryKind::host_heap(), contracts::literal(span, 0))].into(),
        )
    }

    pub(super) fn elements_from_bytes(
        &mut self,
        span: &Span,
        charges: BTreeMap<MemoryKind, Expr>,
    ) -> Elements {
        let precise = charges.values().all(|amount| contracts::constant(amount) == Some(0));
        let records = self.metadata_local(
            span,
            "elements",
            super::metadata::expr::empty(span, super::metadata::expr::record_type()),
        );
        let next_records = self.metadata_local(
            span,
            "next_elements",
            super::metadata::expr::empty(span, super::metadata::expr::record_type()),
        );
        let mut states = BTreeMap::new();
        for (kind, initial) in charges {
            let allocation = super::accounting::Accounting::fresh_allocation();
            let mut variable = |suffix: &str| {
                let name = VarIdent(
                    Arc::new(format!("$memory_elements_{suffix}")),
                    VarIdentDisambiguate::VirTemp(allocation),
                );
                let (value, declaration) = super::symbolic::integer_local(span, name);
                self.growth.declarations.push(declaration);
                value
            };
            let bytes = variable("bytes");
            let next_bytes = variable("next_bytes");
            let count = variable("count");
            let next_count = variable("next_count");
            let zero = contracts::literal(span, 0);
            self.growth.before.entry(span.id).or_default().extend([
                super::symbolic::assign(span, &bytes, initial.clone()),
                super::symbolic::assign(span, &count, zero.clone()),
            ]);
            self.storage.set_allocation(allocation, kind.clone(), bytes.clone());
            let id = self.growth.elements.len();
            self.growth.elements.push(ElementState {
                records: records.clone(),
                uncharged: contracts::constant(&initial) == Some(0),
                id: allocation,
                kind: kind.clone(),
                extent: Some(initial.clone()),
                initial,
                bytes,
                next_bytes,
                count,
                next_count,
                maximum: zero,
                length: None,
                counted: true,
                changed: false,
            });
            states.insert(kind, id);
        }
        Elements {
            view: Default::default(),
            minima: Default::default(),
            source: None,
            records,
            next_records,
            precise,
            states,
            inputs: HashSet::new(),
        }
    }

    /// All owned allocation charges, including nested runtime sums. Inline
    /// handles are excluded because their destination already accounts for them.
    pub(super) fn owner_charges(&self, span: &Span, owner: &Owner) -> BTreeMap<MemoryKind, Expr> {
        let mut charges = BTreeMap::new();
        owner.visit(&mut |node| {
            let mut amount = contracts::literal(span, node.bytes);
            if let Some(id) = node.dynamic {
                amount = contracts::add(span, amount, self.storage.dynamic_cost(span, id));
            }
            add(span, &mut charges, node.kind.clone(), amount);
            if let Some(elements) = &node.elements {
                for (kind, id) in &elements.states {
                    add(span, &mut charges, kind.clone(), self.growth.elements[*id].bytes.clone());
                }
            }
        });
        charges
    }

    fn owner_upper(&self, span: &Span, owner: &Owner) -> BTreeMap<MemoryKind, Expr> {
        let mut charges = BTreeMap::new();
        owner.visit(&mut |node| {
            let amount = if let Some(id) = node.vector {
                let state = &self.growth.vectors[id];
                if state.pushes == 0 {
                    contracts::maximum(
                        span,
                        state.backing.initial_bytes.clone(),
                        state.backing.floor.clone(),
                    )
                } else {
                    self.bound.clone()
                }
            } else {
                node.extent.clone().unwrap_or_else(|| contracts::literal(span, node.bytes))
            };
            add(span, &mut charges, node.kind.clone(), amount);
            if let Some(elements) = &node.elements {
                for (kind, id) in &elements.states {
                    add(
                        span,
                        &mut charges,
                        kind.clone(),
                        self.growth.elements[*id].upper(span, &self.bound),
                    );
                }
            }
        });
        charges
    }

    /// Add bytes rather than taking a maximum: all inserted children remain live.
    fn add_element_bytes(
        &mut self,
        span: &Span,
        elements: &Elements,
        amounts: BTreeMap<MemoryKind, Expr>,
        upper: &BTreeMap<MemoryKind, Expr>,
        length: Option<Expr>,
    ) -> Result<(), VirErr> {
        for (kind, amount) in amounts {
            if contracts::constant(&amount) == Some(0) {
                continue;
            }
            let id = *elements.states.get(&kind).ok_or_else(|| {
                unsupported(span, "an element allocation kind absent from the collection layout")
            })?;
            if self.growth.protected_elements.contains(&id) {
                return Err(unsupported(
                    span,
                    "adding owning children to an enclosing collection inside a memory section",
                ));
            }
            let state = &mut self.growth.elements[id];
            let limit = &upper[&kind];
            self.checks.push((span.clone(), mk_ineq(span, &amount, limit, InequalityOp::Le)));
            self.growth
                .element_updates
                .entry(span.id)
                .or_default()
                .insert(id, contracts::add(span, state.bytes.clone(), amount.clone()));
            self.growth.updates.entry(span.id).or_default().extend([
                super::symbolic::assign(
                    span,
                    &state.next_bytes,
                    contracts::add(span, state.bytes.clone(), amount),
                ),
                super::symbolic::assign(
                    span,
                    &state.next_count,
                    contracts::add(span, state.count.clone(), contracts::literal(span, 1)),
                ),
            ]);
            self.growth.after.entry(span.id).or_default().extend([
                super::symbolic::assign(span, &state.bytes, state.next_bytes.clone()),
                super::symbolic::assign(span, &state.count, state.next_count.clone()),
            ]);
            state.extent =
                state.extent.take().map(|extent| contracts::add(span, extent, limit.clone()));
            state.maximum = contracts::maximum(span, state.maximum.clone(), limit.clone());
            state.counted &= length.is_some();
            state.length = if state.counted { length.clone() } else { None };
            state.changed = true;
            state.uncharged = false;
        }
        Ok(())
    }

    pub(super) fn insert_child(
        &mut self,
        span: &Span,
        elements: &mut Elements,
        child: Owner,
        length: Expr,
    ) -> Result<(), VirErr> {
        self.merge_element_minima(span, elements, &child);
        let mut complete = child.inputs().is_empty();
        child.visit(&mut |node| {
            complete &= node.elements.as_ref().is_none_or(|e| e.precise);
            complete &= node.geometry_known || node.source.is_some();
        });
        elements.precise &= complete;
        if elements.precise {
            let records = self.snapshot_owner_metadata(span, &child);
            let path = self.metadata_path(span, length.clone())?;
            let nested = super::metadata::expr::prefix(span, records.clone(), path.clone());
            self.growth.before.entry(span.id).or_default().extend([
                super::metadata::expr::lemma(
                    span,
                    "well_formed_prefix",
                    vec![records.clone(), path.clone()],
                ),
                super::metadata::expr::lemma(
                    span,
                    "well_formed_add",
                    vec![elements.records.clone(), nested.clone()],
                ),
                super::metadata::expr::lemma(
                    span,
                    "cost_prefix",
                    vec![records.clone(), path.clone(), contracts::literal(span, 0)],
                ),
                super::metadata::expr::lemma(
                    span,
                    "cost_add",
                    vec![elements.records.clone(), nested.clone(), contracts::literal(span, 0)],
                ),
            ]);
            self.growth.updates.entry(span.id).or_default().push(super::metadata::expr::assign(
                span,
                &elements.next_records,
                super::metadata::expr::add(span, elements.records.clone(), nested),
            ));
            self.growth.after.entry(span.id).or_default().push(super::metadata::expr::assign(
                span,
                &elements.records,
                elements.next_records.clone(),
            ));
        }
        let charges = self.owner_charges(span, &child);
        let upper = self.owner_upper(span, &child);
        elements.inputs.extend(child.inputs());
        self.release_owner_storage(child, span, false);
        self.add_element_bytes(span, elements, charges, &upper, Some(length))?;
        self.assert_element_minima(span, elements, true)
    }

    /// Check the complete post-operation charge using pre-operation expressions,
    /// then resume accounting with the ghost sums committed after execution.
    pub(super) fn record_element_updates(&mut self, span: &Span) -> Result<(), VirErr> {
        let updates = self.growth.element_updates.get(&span.id).cloned().unwrap_or_default();
        for (id, amount) in &updates {
            let state = &self.growth.elements[*id];
            self.storage.set_allocation(state.id, state.kind.clone(), amount.clone());
        }
        let result = self.storage.record_live(span);
        for id in updates.keys() {
            let state = &self.growth.elements[*id];
            self.storage.set_allocation(state.id, state.kind.clone(), state.bytes.clone());
        }
        result
    }
}

fn add(span: &Span, charges: &mut BTreeMap<MemoryKind, Expr>, kind: MemoryKind, amount: Expr) {
    let total = charges
        .remove(&kind)
        .map_or_else(|| amount.clone(), |old| contracts::add(span, old, amount.clone()));
    charges.insert(kind, total);
}

impl super::growth::Growth {
    /// An iteration can start after earlier iterations have inserted children.
    /// Retire first-visit zero shortcuts; exact forests and inductive byte
    /// invariants describe the charges at every subsequent loop head.
    pub(super) fn begin_element_iteration(&mut self, ids: &[usize]) {
        for id in ids {
            self.elements[*id].extent = None;
            self.elements[*id].uncharged = false;
        }
    }

    pub(super) fn element_nonnegative(&self, span: &Span, ids: &[usize]) -> Vec<Expr> {
        let mut result = Vec::new();
        for id in ids {
            let state = &self.elements[*id];
            let zero = contracts::literal(span, 0);
            result.push(mk_ineq(span, &zero, &state.bytes, InequalityOp::Le));
            result.push(mk_ineq(span, &zero, &state.count, InequalityOp::Le));
        }
        result
    }

    pub(super) fn repeat_elements(&mut self, ids: &[usize]) {
        for id in ids {
            self.elements[*id].extent = None;
        }
    }

    pub(super) fn forget_element_places(&mut self, owner: &Owner) {
        owner.visit(&mut |node| {
            if let Some(id) = node.vector {
                self.vectors[id].sequence_length = None;
            }
            if let Some(elements) = &node.elements {
                for id in elements.states.values() {
                    self.elements[*id].length = None;
                }
            }
        });
    }

    /// Direct appends tie an insertion count to logical length. Other supported
    /// effects use the checked byte bound without inventing a logical count.
    pub(super) fn element_invariants(
        &self,
        span: &Span,
        ids: &[usize],
        allowed: &HashSet<VarIdent>,
        fallback: &Expr,
    ) -> Vec<Expr> {
        self.element_invariants_at(span, ids, allowed, fallback, None)
    }

    pub(super) fn element_sources(&self, ids: &[usize]) -> std::collections::HashMap<usize, Expr> {
        ids.iter()
            .filter_map(|id| self.elements[*id].length.clone().map(|source| (*id, source)))
            .collect()
    }

    /// Reuse the enclosing iteration's completed charge policy while retaining
    /// the executable length expression valid at this nested loop's location.
    pub(super) fn element_invariants_at(
        &self,
        span: &Span,
        ids: &[usize],
        allowed: &HashSet<VarIdent>,
        fallback: &Expr,
        sources: Option<&std::collections::HashMap<usize, Expr>>,
    ) -> Vec<Expr> {
        let mut result = Vec::new();
        for id in ids {
            let state = &self.elements[*id];
            let zero = contracts::literal(span, 0);
            result.push(mk_ineq(span, &zero, &state.bytes, InequalityOp::Le));
            result.push(mk_ineq(span, &zero, &state.count, InequalityOp::Le));
            let mut in_scope = true;
            let _: Result<(), VirErr> =
                crate::ast_visitor::expr_visitor_check(&state.maximum, &mut |_, expr| {
                    if let ExprX::Var(name) = &expr.x {
                        in_scope &= allowed.contains(name);
                    }
                    Ok(())
                });
            let maximum = if in_scope { state.maximum.clone() } else { fallback.clone() };
            let upper = if state.uncharged {
                // Descriptor-only cuts and transfers cannot create local bytes.
                // Prove this invariant at entry and on every back edge rather
                // than losing the fact when the loop query havocs its counters.
                zero.clone()
            } else if let Some(length) = if state.counted {
                sources.map_or(state.length.as_ref(), |sources| sources.get(id))
            } else {
                None
            } {
                let length = SpannedTyped::new(&length.span, &int_typ(), length.x.clone());
                result.push(mk_ineq(span, &state.count, &length, InequalityOp::Le));
                contracts::add(
                    span,
                    state.initial.clone(),
                    contracts::multiply(span, state.count.clone(), maximum),
                )
            } else {
                fallback.clone()
            };
            result.push(mk_ineq(span, &state.bytes, &upper, InequalityOp::Le));
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn child_footprints_add_within_each_memory_kind() {
        let span = Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "elements".into(),
        };
        let ram = MemoryKind::host_heap();
        let vram = MemoryKind::new("device.0.vram");
        let mut sums = BTreeMap::new();
        add(&span, &mut sums, ram.clone(), contracts::literal(&span, 16));
        add(&span, &mut sums, vram.clone(), contracts::literal(&span, 64));
        add(&span, &mut sums, ram.clone(), contracts::literal(&span, 32));
        add(&span, &mut sums, vram.clone(), contracts::literal(&span, 128));
        assert_eq!(contracts::constant(&sums[&ram]), Some(48));
        assert_eq!(contracts::constant(&sums[&vram]), Some(192));
        assert_eq!(sums.len(), 2);
    }
}
