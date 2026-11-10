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
    /// Uniform reservation candidates, indexed by ownership class.
    pub(super) minima: super::metadata::reservations::Minima,
    /// Current collection value; a move rebinds this to its destination.
    pub(super) source: Option<(Typ, Expr)>,
    /// Dependencies from opaque extracted children, independent of true moves.
    pub(super) captures: HashSet<super::allocations::Capture>,
    /// Allocation data for individually modeled children. Opaque call effects
    /// retain their conservative sums until they acquire a richer summary.
    pub(super) records: Expr,
    /// Pending forest snapshot committed after the executable operation.
    pub(super) next_records: Expr,
    /// Every live child has modeled descriptors; opaque additions disable this.
    pub(super) precise: bool,
    /// Stable counter identities; the containing owner controls their lifetime.
    pub(super) states: BTreeMap<MemoryKind, usize>,
    /// Disjoint input nodes captured by element insertion.
    pub(super) inputs: HashSet<usize>,
}

#[derive(Clone)]
pub(super) struct ElementSummary {
    /// Opaque dependencies whose charges must survive independently of moves.
    pub(super) captures: HashSet<super::allocations::Capture>,
    /// Newly retained child bytes, excluding original input allocations.
    pub(super) bytes: BTreeMap<MemoryKind, Expr>,
    /// Inputs transferred into this collection, consumed exactly once at calls.
    pub(super) inputs: HashSet<usize>,
}

pub(super) struct ElementState {
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
    /// Byte-only helper effects do not expose a precise insertion count.
    counted: bool,
    /// Whether local operations have added child allocations.
    pub(super) changed: bool,
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

/// Summaries describe additions for incoming collections and all child bytes for
/// fresh collections. A checked function budget bounds each locally charged sum.
pub(super) fn summarize(
    elements: &Elements,
    growth: &super::growth::Growth,
    bound: &Expr,
    function: &Function,
) -> ElementSummary {
    ElementSummary {
        captures: elements.captures.clone(),
        bytes: elements
            .states
            .iter()
            .map(|(kind, id)| {
                let mut amount = growth.elements[*id].upper(&bound.span, bound);
                let allowed = contracts::inputs(function);
                let mut in_scope = true;
                let _: Result<(), VirErr> =
                    crate::ast_visitor::expr_visitor_check(&amount, &mut |_, expr| {
                        if let ExprX::Var(name) = &expr.x {
                            in_scope &= allowed.contains(name);
                        }
                        Ok(())
                    });
                if !in_scope {
                    amount = bound.clone();
                }
                (kind.clone(), amount)
            })
            .collect(),
        inputs: elements.inputs.clone(),
    }
}

pub(super) fn additions(
    owner: &Owner,
    growth: &super::growth::Growth,
    bound: &Expr,
    function: &Function,
) -> BTreeMap<OwnerPath, ElementSummary> {
    let mut effects = BTreeMap::new();
    owner.visit_paths(&mut vec![], &mut |path, node| {
        if let Some(effect) = addition(node, growth, bound, function) {
            effects.insert(path.clone(), effect);
        }
    });
    effects
}

/// Additions belonging to one node, excluding its fixed children.
pub(super) fn addition(
    owner: &Owner,
    growth: &super::growth::Growth,
    bound: &Expr,
    function: &Function,
) -> Option<ElementSummary> {
    let elements = owner.elements.as_ref()?;
    (!elements.inputs.is_empty()
        || !elements.captures.is_empty()
        || elements.states.values().any(|id| growth.elements[*id].changed))
    .then(|| summarize(elements, growth, bound, function))
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
            let next = self.growth.elements[new.states[kind]].bytes.clone();
            let state = &mut self.growth.elements[*id];
            self.growth.after.entry(span.id).or_default().push(super::symbolic::assign(
                span,
                &state.bytes,
                next.clone(),
            ));
            self.growth.element_updates.entry(span.id).or_default().insert(*id, next);
            state.changed = true;
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
    ) -> Result<(), VirErr> {
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
                super::metadata::expr::add(span, elements.records.clone(), nested),
            ),
        ]);
        self.growth.after.entry(span.id).or_default().extend(proofs);
        self.prove_element_frame(span, elements, original, path, child_records);
        child.visit(&mut |node| {
            if let Some(elements) = &node.elements {
                for id in elements.states.values() {
                    if let Some(updates) = self.growth.element_updates.get_mut(&span.id) {
                        updates.remove(id);
                    }
                }
            }
        });
        elements.inputs.extend(child.owned_inputs());
        elements.captures.extend(child.captured_inputs());
        elements.precise &= elements.captures.is_empty();
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
            state.changed = true;
            state.counted = false;
            state.length = None;
            state.extent = None;
            let bytes = state.bytes.clone();
            let next = self.growth.after_value(span, &bytes);
            self.growth.element_updates.entry(span.id).or_default().insert(*id, next);
        }
        Ok(())
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
            minima: Default::default(),
            source: None,
            captures: HashSet::new(),
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
        let mut complete = child.inputs().is_empty() && child.captured_inputs().is_empty();
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
        elements.inputs.extend(child.owned_inputs());
        elements.captures.extend(child.captured_inputs());
        self.release_owner_storage(child, span, false);
        self.add_element_bytes(span, elements, charges, &upper, Some(length))?;
        self.assert_element_minima(span, elements, true)
    }

    /// Original allocations remain in the enclosing sum. Only allocations
    /// acquired during this borrow are transferred back into that sum.
    pub(super) fn merge_projected_child(
        &mut self,
        span: &Span,
        elements: &mut Elements,
        child: Owner,
    ) -> Result<(), VirErr> {
        let charges = self.owner_charges(span, &child);
        let upper = self.owner_upper(span, &child);
        elements.inputs.extend(child.owned_inputs());
        elements.captures.extend(child.captured_inputs());
        // These states move into the parent's sum. Pending peak checks must
        // not reintroduce their retired allocation identities as extra charges.
        child.visit(&mut |node| {
            if let Some(elements) = &node.elements {
                for id in elements.states.values() {
                    if let Some(updates) = self.growth.element_updates.get_mut(&span.id) {
                        updates.remove(id);
                    }
                }
            }
        });
        self.release_owner_storage(child, span, false);
        for (kind, amount) in charges {
            if contracts::constant(&amount) == Some(0) {
                continue;
            }
            let id = *elements.states.get(&kind).ok_or_else(|| {
                unsupported(span, "an element allocation kind absent from the collection layout")
            })?;
            if self.growth.protected_elements.contains(&id) {
                return Err(unsupported(
                    span,
                    "changing owning children of an enclosing collection inside a memory section",
                ));
            }
            let amount_after = self.growth.after_value(span, &amount);
            self.checks.push((
                span.clone(),
                mk_ineq(span, &amount_after, &upper[&kind], InequalityOp::Le),
            ));
            let state = &mut self.growth.elements[id];
            // Commit after the child's own snapshots. Keeping the RHS in
            // current variables lets nested projections compose in order,
            // without substituting a child's addition more than once.
            self.growth.after.entry(span.id).or_default().push(super::symbolic::assign(
                span,
                &state.bytes,
                contracts::add(span, state.bytes.clone(), amount),
            ));
            state.extent = state
                .extent
                .take()
                .map(|extent| contracts::add(span, extent, upper[&kind].clone()));
            state.counted = false;
            state.length = None;
            state.changed = true;
            let bytes = state.bytes.clone();
            let next = self.growth.after_value(span, &bytes);
            self.growth.element_updates.entry(span.id).or_default().insert(id, next);
        }
        Ok(())
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

    pub(super) fn apply_collection_call_effects(
        &mut self,
        expr: &Expr,
        callee: &Function,
        args: &Exprs,
        transferred: &mut [Option<Owner>],
    ) -> Result<(), VirErr> {
        let effects = self.summaries[&callee.x.name].allocations.collections.clone();
        for ((index, child), summary) in effects {
            let (name, mut path) = super::paths::expr(&args[index], &callee.x.params[index].x.typ)
                .ok_or_else(|| unsupported(&expr.span, "an aliased collection argument"))?;
            path.extend(child);
            let mut elements = self
                .heap
                .root_mut(&name)
                .and_then(|owner| owner.at_mut(&path))
                .and_then(|owner| owner.elements.take())
                .ok_or_else(|| unsupported(&expr.span, "an untracked collection argument"))?;
            self.apply_element_summary(
                &expr.span,
                &mut elements,
                &summary,
                callee,
                args,
                transferred,
            )?;
            self.heap.root_mut(&name).unwrap().at_mut(&path).unwrap().elements = Some(elements);
        }
        Ok(())
    }

    pub(super) fn adopt_elements(
        &mut self,
        span: &Span,
        summary: &ElementSummary,
        callee: &Function,
        args: &Exprs,
        transferred: &mut [Option<Owner>],
    ) -> Result<Elements, VirErr> {
        let (charges, inputs, captures) =
            self.element_summary_bytes(span, summary, callee, args, transferred)?;
        let mut elements = self.elements_from_bytes(span, charges);
        elements.precise = false;
        elements.inputs = inputs;
        elements.captures = captures;
        Ok(elements)
    }

    fn element_summary_bytes(
        &mut self,
        span: &Span,
        summary: &ElementSummary,
        callee: &Function,
        args: &Exprs,
        transferred: &mut [Option<Owner>],
    ) -> Result<
        (BTreeMap<MemoryKind, Expr>, HashSet<usize>, HashSet<super::allocations::Capture>),
        VirErr,
    > {
        let mut charges = BTreeMap::new();
        let mut inputs = HashSet::new();
        let (captured_bytes, mut captures) = self.captured_sources(span, &summary.captures);
        if !summary.captures.is_empty() {
            add(span, &mut charges, MemoryKind::host_heap(), captured_bytes);
        }
        for (kind, amount) in &summary.bytes {
            add(
                span,
                &mut charges,
                kind.clone(),
                contracts::substitute(amount, callee, args, &self.stable_scalars)?,
            );
        }
        for index in &summary.inputs {
            let child = transferred[*index].take().ok_or_else(|| {
                unsupported(span, "a collected input without transferred ownership")
            })?;
            for (kind, amount) in self.owner_charges(span, &child) {
                add(span, &mut charges, kind, amount);
            }
            inputs.extend(child.owned_inputs());
            captures.extend(child.captured_inputs());
            self.release_owner_storage(child, span, false);
        }
        Ok((charges, inputs, captures))
    }

    /// Instantiate one checked addition and absorb all transferred input owners
    /// in one update, so multiple children cannot overwrite each other's sum.
    pub(super) fn apply_element_summary(
        &mut self,
        span: &Span,
        elements: &mut Elements,
        summary: &ElementSummary,
        callee: &Function,
        args: &Exprs,
        transferred: &mut [Option<Owner>],
    ) -> Result<(), VirErr> {
        let (charges, inputs, captures) =
            self.element_summary_bytes(span, summary, callee, args, transferred)?;
        elements.inputs.extend(inputs);
        elements.captures.extend(captures);
        if !summary.inputs.is_empty() || !summary.captures.is_empty() {
            elements.precise = false;
        }
        if charges.values().all(|amount| contracts::constant(amount) == Some(0)) {
            return Ok(());
        }
        elements.precise = false;
        let upper = charges.clone();
        self.add_element_bytes(span, elements, charges, &upper, None)
    }
}

fn add(span: &Span, charges: &mut BTreeMap<MemoryKind, Expr>, kind: MemoryKind, amount: Expr) {
    let total = charges
        .remove(&kind)
        .map_or_else(|| amount.clone(), |old| contracts::add(span, old, amount.clone()));
    charges.insert(kind, total);
}

impl super::growth::Growth {
    pub(super) fn capture_elements(&mut self, span: &Span, id: usize, amount: Expr, after: bool) {
        let state = &mut self.elements[id];
        let assignment = super::symbolic::assign(
            span,
            &state.bytes,
            contracts::add(span, state.bytes.clone(), amount.clone()),
        );
        state.initial = contracts::add(span, state.initial.clone(), amount.clone());
        state.extent = state.extent.take().map(|extent| contracts::add(span, extent, amount));
        if after {
            self.after.entry(span.id).or_default().push(assignment);
        } else {
            self.before.entry(span.id).or_default().push(assignment);
        }
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

    /// Inductive sums use an insertion count tied to logical length for direct
    /// appends. Calls with only byte summaries retain a conservative budget bound.
    pub(super) fn element_invariants(
        &self,
        span: &Span,
        ids: &[usize],
        allowed: &HashSet<VarIdent>,
        fallback: &Expr,
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
            let upper = if let Some(length) = &state.length {
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
