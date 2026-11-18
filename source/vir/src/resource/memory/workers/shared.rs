//! Reconcile indexed capture claims with the coordinator's canonical Arc backing.
//! Workers run independently. Until collection their checked entry claims reserve
//! backing, including when a completed worker keeps the handle in its result.

use super::super::{
    accounting::{Accounting, SharedBackingCharges},
    analysis::Analysis,
    contracts,
    growth::select,
    heap::Owner,
    metadata::expr,
    model::unsupported,
};
use super::{WorkerId, populations::Occurrence};
use crate::{ast::*, messages::Span};
use std::collections::BTreeMap;

/// Strong aliases published in retained workers and not yet reconciled by a
/// coordinator join. An outstanding claim keeps the backing charged once even
/// if the worker may already have run its last destructor.
pub(in super::super) struct Claims {
    /// Sum of unreconciled entry aliases, independent of which workers have finished.
    pub(in super::super) pending: Expr,
    /// The same ownership tree moves between fixed and conditional accounting.
    pub(in super::super) backing: Owner,
    /// Fixed and symbolic charges reached by this immutable payload.
    charges: SharedBackingCharges,
    /// Number of handles actually moved into one occurrence of this family.
    weights: BTreeMap<WorkerId, u64>,
}

impl Claims {
    /// A final directly tracked drop can make the backing conditional only if
    /// this accounting domain still has every charge of the payload.
    pub(in super::super) fn defer_backing(
        &self,
        storage: &mut Accounting,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        let empty = crate::ast_util::mk_eq(span, &self.pending, &expr::integer(span, 0));
        if !self.charges.defer(storage, empty, span) {
            proofs.push(expr::check(
                span,
                crate::ast_util::mk_bool(span, false),
                "cannot locate the shared payload's live backing charges",
            ));
        }
    }

    /// A collection length describes strong claims only if all of its possible
    /// publications capture the same multiplicity of this particular root.
    pub(in super::super) fn uniform_weight<'a>(
        &self,
        families: impl Iterator<Item = &'a WorkerId>,
    ) -> Option<u64> {
        let mut weights = families.map(|id| self.weights.get(id).copied().unwrap_or(0));
        let first = weights.next()?;
        weights.all(|w| w == first).then_some(first)
    }

    /// Use the selected publication identity for mixed families. A uniform
    /// weight already follows from the checked membership of the occurrence.
    fn selected_weight(&self, span: &Span, occurrence: &Occurrence) -> Option<Expr> {
        if let Some(weight) = self.uniform_weight(occurrence.templates.iter()) {
            return (weight != 0).then(|| contracts::literal(span, weight));
        }
        let weight = occurrence
            .templates
            .iter()
            .filter_map(|id| Some((id, self.weights.get(id)?)))
            .fold(expr::integer(span, 0), |others, (id, count)| {
                let matched = expr::operation(
                    span,
                    "worker_matches",
                    vec![occurrence.record.clone(), expr::path(span, id.descriptor())],
                    crate::ast_util::bool_typ(),
                );
                select(span, matched, contracts::literal(span, *count), others)
            });
        Some(weight)
    }
}

impl Analysis<'_> {
    /// An accounting domain may return a collected Arc, but every indexed
    /// entry claim must have a matching source join on each normal exit.
    pub(in super::super) fn check_indexed_exits(&mut self, body: &Span) {
        if self.growth.indexed_shared.is_empty() {
            return;
        }
        let exits = self
            .flow
            .exits
            .iter()
            .map(|edge| &edge.span)
            .chain(self.flow.reachable.then_some(body));
        for span in exits {
            for claims in self.growth.indexed_shared.values() {
                self.growth.after.entry(span.id).or_default().push(expr::check(
                    span,
                    crate::ast_util::mk_eq(span, &claims.pending, &expr::integer(span, 0)),
                    "outstanding shared worker claims at accounting scope exit",
                ));
            }
        }
    }

    pub(super) fn index_worker_claims(
        &mut self,
        actor: WorkerId,
        span: &Span,
    ) -> Result<(), VirErr> {
        let worker = &self.heap.workers.records[&actor];
        let execution = worker.execution.as_ref().unwrap();
        let returned = execution.result.owner.as_ref().and_then(|owner| owner.shared);
        if (!execution.shared.is_empty()
            && !returned.is_some_and(|id| worker.entry_shared.has_strong(id)))
            || (self.current_worker.is_some() && !worker.entry_shared.is_empty())
        {
            return Err(unsupported(
                span,
                "retained worker shared-reference populations without their conservation relation",
            ));
        }
        for (root, count, backing) in self.heap.shared.index_imports(&worker.entry_shared, span)? {
            if !self.transitions.owns_fixed_root(root) {
                return Err(unsupported(
                    span,
                    "indexed aliases of a repeated or imported allocation",
                ));
            }
            let claims = match self.growth.indexed_shared.entry(root) {
                std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::btree_map::Entry::Vacant(entry) => {
                    let charges = SharedBackingCharges::new(&backing, &self.growth.elements, span)?;
                    let zero = expr::integer(span, 0);
                    let (pending, decl) =
                        expr::local(span, "outstanding_strong", zero.typ.clone(), zero, Mode::Spec);
                    self.growth.declarations.push(decl);
                    entry.insert(Claims { pending, backing, charges, weights: BTreeMap::new() })
                }
            };
            claims.weights.insert(actor, count);
            let next =
                contracts::add(span, claims.pending.clone(), contracts::literal(span, count));
            self.growth.after.entry(span.id).or_default().push(expr::assign(
                span,
                &claims.pending,
                next,
            ));
        }
        Ok(())
    }

    pub(super) fn receive_indexed_alias(
        &mut self,
        span: &Span,
        occurrence: &Occurrence,
        result: Expr,
    ) -> Result<Owner, VirErr> {
        let mut roots = occurrence.templates.iter().map(|id| {
            self.growth.worker_executions[id].result.owner.as_ref().and_then(|owner| owner.shared)
        });
        let root =
            roots.next().flatten().filter(|id| roots.all(|r| r == Some(*id))).ok_or_else(|| {
                unsupported(span, "an indexed Arc result without a common proven backing identity")
            })?;
        let claims = self.growth.indexed_shared.get(&root).ok_or_else(|| {
            unsupported(span, "an indexed Arc result outside its canonical domain")
        })?;
        let path = expr::path(span, []);
        let actual = expr::lookup(span, result, path.clone());
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            crate::ast_util::mk_eq(span, &actual, &root.record(span, path)),
            "cannot establish the selected result's canonical shared allocation",
        ));
        if !self.heap.shared.has_strong(root) {
            claims.charges.receive(&mut self.storage, span)?;
        }
        self.heap.shared.receive_indexed(root, &claims.backing, span)
    }

    pub(super) fn collect_indexed_claims(
        &mut self,
        span: &Span,
        occurrence: &Occurrence,
    ) -> Result<(), VirErr> {
        for claims in self.growth.indexed_shared.values() {
            let Some(weight) = claims.selected_weight(span, occurrence) else { continue };
            if self.current_worker.is_some() {
                return Err(unsupported(
                    span,
                    "collection of indexed shared claims outside their publishing coordinator",
                ));
            }
            let next = contracts::subtract(span, claims.pending.clone(), weight);
            let statements = self.growth.after.entry(span.id).or_default();
            statements.push(expr::check(
                span,
                crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &next, InequalityOp::Le),
                "cannot reconcile the selected worker's outstanding strong references",
            ));
            statements.push(expr::assign(span, &claims.pending, next));
        }
        Ok(())
    }
}
