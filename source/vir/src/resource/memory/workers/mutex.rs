//! Bind an owned mutex result to the producer selected by a native indexed join.
use super::{SourceVisit, WorkerId, populations::Occurrence};
use crate::{
    ast::{Expr, Typ, VirErr},
    messages::AstId,
    resource::memory::{
        analysis::Analysis,
        growth::Growth,
        heap::{Owner, OwnerSlot},
        metadata::expr,
        model::unsupported,
        synchronization::{Instance, local::Owned},
    },
};
use std::collections::{BTreeMap, BTreeSet};

/// Source binding of a by-value mutex moved out of the selected completion.
/// The producer record selects the returning instance, even across loop iterations.
#[derive(Clone)]
pub(in super::super) struct MutexReceipt {
    /// Receiving actor and enclosing executable loop coordinates.
    visit: SourceVisit<AstId>,
    /// Immutable identity and ownership of the selected completion.
    record: Expr,
    /// Returned mutex binder within each possible producer.
    sources: BTreeMap<WorkerId, Instance>,
}

impl MutexReceipt {
    fn instance(&self) -> Instance {
        Instance::Joined(self.visit.site)
    }

    /// Check this summary against the lifetime analysis of the actual native join.
    pub(super) fn matches_join(
        &self,
        families: &BTreeSet<WorkerId>,
        record: Option<&Expr>,
        growth: &Growth,
    ) -> bool {
        record.is_some_and(|r| std::sync::Arc::ptr_eq(r, &self.record))
            && self.sources.keys().eq(families)
            && self.sources.iter().all(|(id, instance)| {
                growth
                    .worker_executions
                    .get(id)
                    .and_then(|e| e.result.owner.as_ref())
                    .and_then(Owner::mutex_instance)
                    == Some(*instance)
            })
    }

    pub(in super::super) fn valid_for(&self, site: AstId, actor: Option<WorkerId>) -> bool {
        self.visit.site == site
            && self.visit.valid_for(actor)
            && !self.sources.is_empty()
            && crate::ast_util::types_equal(&self.record.typ, &expr::record_type())
    }
}

impl Analysis<'_> {
    /// A by-value mutex moves with all its contents. Rust's borrow rules
    /// exclude a surviving borrowed guard at the transfer.
    pub(super) fn bind_received_mutex(
        &mut self,
        source: &Expr,
        payload: &Typ,
        occurrence: &Occurrence,
        received: &mut Owner,
    ) -> Result<Option<Box<MutexReceipt>>, VirErr> {
        if !self
            .layouts
            .mutex_payload(payload)
            .is_some_and(|typ| self.layouts.plain_protected_payload(typ))
        {
            return Ok(None);
        }
        let sources = occurrence
            .templates
            .iter()
            .map(|id| {
                let instance =
                    self.growth.worker_executions[id].result.owner.as_ref()?.mutex_instance()?;
                Some((*id, instance))
            })
            .collect::<Option<_>>()
            .ok_or_else(|| {
                unsupported(&source.span, "a joined mutex without its returned ownership")
            })?;
        let receipt = MutexReceipt {
            visit: self.source_visit(source.span.id, self.local_occurrences(&source.span)?),
            record: occurrence.record.clone(),
            sources,
        };
        received.synchronization = Some(Owned::Mutex(receipt.instance()));
        if let Some(child) = received.children.get_mut(&OwnerSlot::Contents) {
            self.protect_vector_length(source, child);
        }
        Ok(Some(Box::new(receipt)))
    }
}
