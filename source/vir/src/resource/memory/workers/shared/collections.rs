//! A collecting worker owns the handles moved in its captured vectors. The
//! publisher retains their shared backings until it joins the collector.
use super::*;
use crate::resource::memory::{
    elements::References,
    workers::{Input, body::Entry},
};

impl Analysis<'_> {
    /// Count only the concrete captured vector slots. Zero-length vectors and
    /// other outstanding workers of the same family contribute independently.
    pub(in crate::resource::memory::workers) fn capture_collection_claims(
        &mut self,
        span: &Span,
        entry: &Entry,
        inputs: &[Input],
    ) -> BTreeMap<RootId, Expr> {
        let mut counts = BTreeMap::new();
        let mut membership = Vec::new();
        if self.growth.indexed_shared.is_empty() {
            return counts;
        }
        for input in inputs {
            let field = &input.typ;
            let Some(vector) =
                entry.storage.owner.as_ref().and_then(|o| o.children.get(&input.slot))
            else {
                continue;
            };
            let Some(elements) = &vector.elements else { continue };
            if !self.layouts.vector(field)
                || elements.view != crate::resource::memory::metadata::View::Complete
                || !elements.precise
                || !vector.geometry_known
                || elements.references != References::WorkerOccurrences
            {
                continue;
            }
            let TypX::Datatype(_, types, _) = &**field else { continue };
            let Some((payload, _)) = types.first().and_then(|t| self.layouts.join_handle(t)) else {
                continue;
            };

            let Some(length) = &vector.geometry else { continue };
            for (root, claims) in &self.growth.indexed_shared {
                let families = self.retained_families(payload);
                let Some(amount) = claims.population.count_records(
                    span,
                    families.clone(),
                    &elements.records,
                    length,
                ) else {
                    continue;
                };
                for record in self.transitions.loops.values() {
                    if let Some(len) = record.forest_length(&elements.records)
                        && let Some(fact) = claims.population.homogeneous_coverage(
                            &record.span,
                            families.clone(),
                            &elements.records,
                            len,
                        )
                    {
                        membership.push((record.span.clone(), record.body.span.clone(), fact));
                    }
                }
                let previous = counts.remove(root).unwrap_or_else(|| expr::integer(span, 0));
                counts.insert(*root, contracts::add(span, previous, amount));
            }
        }
        for (head, body, fact) in membership {
            self.growth.prove_family_counts(&head, &body);
            self.growth.loops.entry(head.id).or_default().push(fact);
        }
        // The executable closure operand establishes the capture snapshots.
        // Freeze these amounts once, before the publisher continues.
        if counts.is_empty() {
            return counts;
        }
        let start = self.growth.before.get(&span.id).map_or(0, Vec::len);
        self.growth
            .after
            .entry(span.id)
            .or_default()
            .extend(crate::resource::memory::loops::populations::family_count_laws(span));
        for amount in counts.values_mut() {
            *amount = self.metadata_local(span, "captured_claims", amount.clone());
        }
        if let Some(before) = self.growth.before.get_mut(&span.id) {
            let observations = before.split_off(start);
            self.growth.after.entry(span.id).or_default().extend(observations);
        }
        counts
    }

    /// Finish payload destruction at a fixed join. A full drain keeps the
    /// publisher's share live through the wait and result handoff. The worker's
    /// checked exits and inline result establish that the entire share can end.
    pub(in crate::resource::memory::workers) fn finish_joined_payloads(
        &mut self,
        span: &Span,
        execution: &Execution,
        before_join: &mut Vec<Stmt>,
    ) -> Result<(), VirErr> {
        let captured = &execution.effects.ownership.collection_claims;
        if captured.is_empty() {
            self.finish_indexed_payloads(span, before_join);
            return Ok(());
        }
        self.require_indexed_claim_owner(span)?;
        let mut after_join = Vec::new();
        for (root, count) in captured {
            self.growth.indexed_shared[root].population.release(
                span,
                count.clone(),
                "cannot reconcile this collector's captured shared references",
                &mut after_join,
            );
        }
        self.finish_indexed_payloads(span, &mut after_join);
        self.growth.after.entry(span.id).or_default().extend(after_join);
        Ok(())
    }
}
