//! A retained outer Arc can own the sole right to join an independent worker.
//! Pack its tag once and recover its immutable publication from the selected slot.
use super::*;
use crate::resource::memory::{heap::OwnerSlot, metadata::View};

impl Analysis<'_> {
    pub(super) fn pack_payload_job(
        &mut self,
        span: &Span,
        actor: WorkerId,
        outer: RootId,
        backing: &mut Owner,
        forest: &Expr,
    ) -> Result<(), VirErr> {
        if let Some(job) = backing.children.get_mut(&OwnerSlot::Contents)
            && let Some(handle) = &job.worker
        {
            if self.growth.payload_jobs.get(&actor) != Some(&handle.actor)
                || !self
                    .heap
                    .workers
                    .records
                    .get(&handle.actor)
                    .is_some_and(|w| w.entry_shared.is_empty())
                || self.growth.occurrence_peers.contains_key(&outer)
            {
                return Err(unsupported(
                    span,
                    "a transported job without its unique returned allocation and published inputs",
                ));
            }
            if self.index_worker_handle(job, span, forest)?.is_some() {
                return Err(unsupported(span, "embedding a worker carrying shared backing"));
            }
            // Only the immutable observation moves into the outer worker's
            // input record. Its completion tag travels in the charged extent.
            job.selected_worker = None;
        }
        Ok(())
    }

    pub(super) fn restore_payload_job(
        &mut self,
        span: &Span,
        occurrence: &Occurrence,
        has_peers: bool,
        bytes: Expr,
    ) -> Result<(Owner, Expr), VirErr> {
        let mut backing = Owner::default();
        let mut bytes = bytes;
        if let Some(inner) =
            occurrence.templates.iter().find_map(|id| self.growth.payload_jobs.get(id)).copied()
        {
            if has_peers
                || !occurrence
                    .templates
                    .iter()
                    .all(|id| self.growth.payload_jobs.get(id) == Some(&inner))
            {
                return Err(unsupported(span, "mixed worker results with different embedded jobs"));
            }
            self.require_indexed_claim_owner(span)?;
            let outer =
                &self.growth.worker_executions[occurrence.templates.first().unwrap()].result.typ;
            let TypX::Decorate(TypDecoration::Arc, _, typ) = &**outer else { unreachable!() };
            let typ = typ.clone();
            let (outer_bytes, tag) = super::occurrences::split_carried_charge(
                span,
                bytes,
                self.growth.before.entry(span.id).or_default(),
            );
            bytes = outer_bytes;
            let memory = expr::push(
                span,
                expr::payload_job(span, occurrence.record.clone()),
                expr::worker_charge(span, tag),
            );
            let job = self.worker_from_metadata(
                span,
                &typ,
                memory,
                View::Complete,
                false,
                Some([inner].into()),
            )?;
            backing.children.insert(OwnerSlot::Contents, job);
        }
        Ok((backing, bytes))
    }
}
