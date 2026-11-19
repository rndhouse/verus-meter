//! A collecting worker owns the handles moved in its captured vectors. The
//! publisher retains their shared backings until it joins the collector.
use super::*;
use crate::resource::memory::{
    elements::References,
    workers::{Input, body::Entry},
};

impl Analysis<'_> {
    /// The checked worker result type stored in each slot of a handle vector.
    pub(in crate::resource::memory::workers) fn collection_worker_payload<'a>(
        &self,
        typ: &'a Typ,
    ) -> Option<&'a Typ> {
        if !self.layouts.vector(typ) {
            return None;
        }
        let TypX::Datatype(_, args, _) = &**typ else { return None };
        self.layouts.join_handle(args.first()?).map(|(payload, _)| payload)
    }

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
            if elements.view != crate::resource::memory::metadata::View::Complete
                || !elements.precise
                || !vector.geometry_known
                || elements.references != References::WorkerOccurrences
            {
                continue;
            }
            let Some(payload) = self.collection_worker_payload(field) else { continue };

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

    /// Transfer the single surviving local reservation to the publisher. Imported
    /// aliases already have a publisher identity and use the ordinary fixed join.
    pub(in crate::resource::memory::workers) fn receive_collector_selection(
        &mut self,
        span: &Span,
        execution: &Execution,
        handle: &super::super::FixedHandle,
        shared: &mut crate::resource::memory::shared::SharedRoots,
        output: Option<&mut Owner>,
    ) -> Result<Option<u64>, VirErr> {
        let Some(output) = output else { return Ok(None) };
        let Some(StrongLink::Selected(id)) = output.shared else { return Ok(None) };
        if shared.selection(id).collector != Some(execution.actor) {
            return Ok(None);
        }
        let selection = shared.release_selection(id).ok_or_else(|| {
            unsupported(span, "a collector returning an alias with unresolved references")
        })?;
        if !selection
            .roots
            .iter()
            .all(|root| execution.effects.ownership.collection_claims.contains_key(root))
        {
            return Err(unsupported(
                span,
                "a collector's selected result outside its captured reservations",
            ));
        }
        *output = self.reserve_arc_result(span, handle.result_memory(span)?, selection.roots);
        let Some(StrongLink::Selected(id)) = output.shared else { unreachable!() };
        Ok(Some(id))
    }

    /// At collection, replace the share frozen at spawn with just the claims
    /// carried by the actual result. Other vectors and aliases keep their share.
    pub(in crate::resource::memory::workers) fn finish_joined_payloads(
        &mut self,
        span: &Span,
        execution: &Execution,
        output: Option<&Owner>,
        returned_selection: Option<u64>,
        before_join: &mut Vec<Stmt>,
    ) -> Result<(), VirErr> {
        let captured = &execution.effects.ownership.collection_claims;
        if captured.is_empty() {
            self.finish_indexed_payloads(span, before_join);
            return Ok(());
        }
        self.require_indexed_claim_owner(span)?;
        let mut after_join = Vec::new();
        let vector = self.collection_worker_payload(&execution.result.typ);
        let slots = if let Some(payload) = vector {
            let owner = output
                .ok_or_else(|| unsupported(span, "a collector result without its vector owner"))?;
            let elements = owner
                .elements
                .as_ref()
                .ok_or_else(|| unsupported(span, "a collector result without slot records"))?;
            let length = owner.geometry.as_ref().ok_or_else(|| {
                unsupported(span, "a collector result without its checked length")
            })?;
            if !elements.precise
                || elements.view != crate::resource::memory::metadata::View::Complete
            {
                return Err(unsupported(span, "a partial view of a returned worker collection"));
            }
            // Unfold one step of the family count at the actual boundary. Its
            // last slot must come from the same ordered publication forest.
            let index = contracts::subtract(span, length.clone(), expr::integer(span, 1));
            let path = expr::push(span, expr::path(span, []), index);
            after_join.push(expr::lemma(
                span,
                "request_path",
                vec![elements.records.clone(), path.clone()],
            ));
            after_join.push(expr::lemma(
                span,
                "lookup_subtree",
                vec![elements.records.clone(), path, expr::path(span, [])],
            ));
            after_join.push(crate::def::Spanned::new(
                span.clone(),
                StmtX::Expr(SpannedTyped::new(
                    span,
                    &crate::ast_util::unit_typ(),
                    ExprX::Fuel(expr::function("worker_family_count"), 2, false),
                )),
            ));
            Some((payload, &elements.records, length))
        } else {
            None
        };
        for (root, count) in captured {
            let population = &self.growth.indexed_shared[root].population;
            let retained = if let Some((payload, records, length)) = slots {
                population.count_records(span, self.retained_families(payload), records, length)
            } else {
                returned_selection.map(|id| self.heap.shared.selection(id).reservation(span, *root))
            };
            let remaining = population.after_release(
                span,
                count.clone(),
                "cannot reconcile this collector's captured shared references",
                &mut after_join,
            );
            let next = retained.map_or_else(
                || remaining.clone(),
                |live| contracts::add(span, remaining.clone(), live),
            );
            after_join.push(expr::assign(span, &population.pending, next));
        }
        // A returned ownership forest is still in transit until its binding
        // is installed. Its normal destructor checks the final payload release.
        if vector.is_none() && returned_selection.is_none() {
            self.finish_indexed_payloads(span, &mut after_join);
        }
        self.growth.after.entry(span.id).or_default().extend(after_join);
        Ok(())
    }
}
