//! Count the reservations carried by actual worker families in occupied handle slots.
use super::*;

/// Source-backed reservations reconciled when the relevant worker or returned alias ends.
pub(in crate::resource::memory) struct Population {
    /// Unreconciled reservations, including those held by returned aliases.
    pub(in crate::resource::memory) pending: Expr,
    /// Number of handles actually moved into one occurrence of this family.
    pub(super) weights: BTreeMap<WorkerId, u64>,
}

impl Population {
    pub(super) fn new(span: &Span, declarations: &mut Vec<Stmt>) -> Self {
        let zero = expr::integer(span, 0);
        let (pending, declaration) =
            expr::local(span, "outstanding_strong", zero.typ.clone(), zero, Mode::Spec);
        declarations.push(declaration);
        Self { pending, weights: BTreeMap::new() }
    }

    pub(super) fn publish(
        &mut self,
        actor: WorkerId,
        count: u64,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        self.weights.insert(actor, count);
        let next = contracts::add(span, self.pending.clone(), contracts::literal(span, count));
        proofs.push(expr::assign(span, &self.pending, next));
    }

    /// Check conservation both for a hypothetical worker phase and for a source join.
    pub(in crate::resource::memory) fn after_release(
        &self,
        span: &Span,
        count: Expr,
        message: &str,
        proofs: &mut Vec<Stmt>,
    ) -> Expr {
        let remaining = contracts::subtract(span, self.pending.clone(), count);
        proofs.push(expr::check(
            span,
            crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &remaining, InequalityOp::Le),
            message,
        ));
        remaining
    }

    pub(super) fn release(&self, span: &Span, count: Expr, message: &str, proofs: &mut Vec<Stmt>) {
        let remaining = self.after_release(span, count, message, proofs);
        proofs.push(expr::assign(span, &self.pending, remaining));
    }

    /// A collection length describes strong claims only if all of its possible
    /// publications capture the same multiplicity of this particular root.
    fn uniform_weight<'a>(&self, families: impl Iterator<Item = &'a WorkerId>) -> Option<u64> {
        let mut weights = families.map(|id| self.weights.get(id).copied().unwrap_or(0));
        let first = weights.next()?;
        weights.all(|w| w == first).then_some(first)
    }

    /// Sum this root's entry aliases over the actual occupied handle slots.
    /// The common uniform case needs only the checked vector length.
    pub(in crate::resource::memory) fn collection_count<'a>(
        &self,
        span: &Span,
        families: impl Iterator<Item = &'a WorkerId> + Clone,
        records: &Expr,
        length: &Expr,
    ) -> Option<(Expr, bool)> {
        if let Some(weight) = self.uniform_weight(families.clone()) {
            return (weight != 0).then(|| {
                (contracts::multiply(span, contracts::literal(span, weight), length.clone()), false)
            });
        }
        let count = families
            .filter_map(|id| {
                let weight = *self.weights.get(id)?;
                let count = expr::operation(
                    span,
                    "worker_family_count",
                    vec![records.clone(), length.clone(), expr::path(span, id.descriptor())],
                    std::sync::Arc::new(TypX::Int(IntRange::Nat)),
                );
                Some(contracts::multiply(span, contracts::literal(span, weight), count))
            })
            .reduce(|a, b| contracts::add(span, a, b))?;
        Some((count, true))
    }

    /// Use the selected publication identity for mixed families. A uniform
    /// weight already follows from the checked membership of the occurrence.
    pub(super) fn selected_weight(&self, span: &Span, occurrence: &Occurrence) -> Option<Expr> {
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
