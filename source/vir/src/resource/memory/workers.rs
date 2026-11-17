//! Worker-owned storage outlives publication and the caller's join-handle slot.
//!
//! This is ownership state, not a sum of independent worker peaks. Publication,
//! body execution/cleanup, completion and join remain separate effects; later
//! composition must consider every permitted interleaving of their phase graphs.

use super::{
    analysis::Analysis,
    heap::Owner,
    lifetime::{Storage, Value},
    model::unsupported,
};
use crate::{ast::*, messages::Span};
use std::collections::BTreeMap;

mod body;
mod captures;
mod identity;

pub(super) use identity::{Families, WorkerId};

#[derive(Clone)]
enum Stage {
    /// Captures remain live even if the worker has not been scheduled.
    Published(Storage),
    /// The checked body owns the capture fields, including while blocked.
    Running,
    /// Result storage remains owned by the completion record until join.
    Completed(Storage),
}

#[derive(Clone)]
struct Worker {
    parent: Option<WorkerId>,
    /// Actual executable body retained across publication and source moves.
    definition: Expr,
    /// Source/body paths refer to fields of the retained environment charge.
    captures: captures::Captures,
    /// The completion tag is one distinct allocation, independent of the
    /// parent's inline handle and the result eventually stored behind it.
    completion: u64,
    result: Typ,
    stage: Stage,
    /// A wait consumes the source handle but retains its inline call argument.
    waiter: Option<Value>,
    /// Dropping a handle detaches execution; it does not destroy the worker.
    detached: Option<Span>,
    publication: Span,
}

/// Outstanding execution and completion records for one closed accounting domain.
/// Cloning an analysis branch is not publication of another executable worker.
#[derive(Clone, Default)]
pub(super) struct Workers {
    records: BTreeMap<WorkerId, Worker>,
}

impl Workers {
    fn publish(
        &mut self,
        id: WorkerId,
        span: &Span,
        parent: Option<WorkerId>,
        completion: u64,
        entry: body::Entry,
    ) -> Result<(), VirErr> {
        if let Some(parent) = parent
            && !self
                .records
                .get(&parent)
                .is_some_and(|parent| matches!(parent.stage, Stage::Running))
        {
            return Err(unsupported(span, "publication outside a live parent worker"));
        }
        if self.records.contains_key(&id) {
            return Err(unsupported(span, "republishing an existing worker occurrence"));
        }
        let TypX::AnonymousClosure(_, result, _, _) = &*entry.definition.typ else {
            return Err(unsupported(span, "publication without an executable worker definition"));
        };
        self.records.insert(
            id,
            Worker {
                parent,
                definition: entry.definition.clone(),
                captures: entry.captures,
                completion,
                result: result.clone(),
                stage: Stage::Published(entry.storage),
                waiter: None,
                detached: None,
                publication: span.clone(),
            },
        );
        Ok(())
    }

    // The checked body-summary adapter in TODO 05 consumes entry and completion.
    // Until then these transitions cannot discharge a source worker proof.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "worker body-summary entry is connected in TODO 05")
    )]
    pub(super) fn enter(&mut self, id: WorkerId, span: &Span) -> Result<body::Entry, VirErr> {
        let worker =
            self.records.get_mut(&id).ok_or_else(|| unsupported(span, "an unknown worker"))?;
        if !matches!(worker.stage, Stage::Published(_)) {
            return Err(unsupported(span, "entering a worker more than once"));
        }
        let Stage::Published(captures) = std::mem::replace(&mut worker.stage, Stage::Running)
        else {
            unreachable!()
        };
        Ok(body::Entry {
            definition: worker.definition.clone(),
            captures: worker.captures.clone(),
            storage: captures,
        })
    }

    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "worker body-summary return is connected in TODO 05")
    )]
    pub(super) fn complete(
        &mut self,
        id: WorkerId,
        span: &Span,
        result: Storage,
    ) -> Result<(), VirErr> {
        if self.records.values().any(|worker| worker.parent == Some(id)) {
            return Err(unsupported(span, "worker completion with an unjoined descendant"));
        }
        let worker =
            self.records.get_mut(&id).ok_or_else(|| unsupported(span, "an unknown worker"))?;
        if !matches!(worker.stage, Stage::Running) {
            return Err(unsupported(span, "worker completion without checked body execution"));
        }
        if !crate::ast_util::types_equal(&worker.result, &result.typ) {
            return Err(unsupported(span, "a worker result with inconsistent ownership types"));
        }
        worker.stage = Stage::Completed(result);
        Ok(())
    }

    fn wait(&mut self, id: WorkerId, span: &Span, handle: Value) -> Result<(), VirErr> {
        let worker = self
            .records
            .get_mut(&id)
            .ok_or_else(|| unsupported(span, "joining an unknown worker"))?;
        if worker.detached.is_some() || worker.waiter.is_some() {
            return Err(unsupported(span, "a detached or already consumed join handle"));
        }
        worker.waiter = Some(handle);
        Ok(())
    }

    /// Remove only a completed record. The adapter transfers its result and
    /// releases the separate tag/handle charges after waiting has finished.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "completed-result transfer is consumed by the TODO 05 join adapter"
        )
    )]
    fn take_result(&mut self, id: WorkerId, span: &Span) -> Result<(Storage, Value, u64), VirErr> {
        let worker =
            self.records.get(&id).ok_or_else(|| unsupported(span, "joining an unknown worker"))?;
        if worker.detached.is_some()
            || worker.waiter.is_none()
            || !matches!(worker.stage, Stage::Completed(_))
        {
            return Err(unsupported(span, "join requires checked worker completion effects"));
        }
        let worker = self.records.remove(&id).unwrap();
        let Stage::Completed(result) = worker.stage else { unreachable!() };
        Ok((result, worker.waiter.unwrap(), worker.completion))
    }

    pub(super) fn detach(&mut self, id: WorkerId, span: &Span) {
        let worker =
            self.records.get_mut(&id).expect("a live join handle names an outstanding worker");
        worker.detached = Some(span.clone());
    }

    pub(super) fn check_closed(&self, span: &Span) -> Result<(), VirErr> {
        if let Some(worker) = self.records.values().next() {
            return Err(unsupported(
                worker.detached.as_ref().unwrap_or(span),
                if worker.detached.is_some() {
                    "detached workers in a memory accounting scope"
                } else {
                    "an accounting scope returning with unjoined workers or retained results"
                },
            )
            .secondary_span(&worker.publication));
        }
        Ok(())
    }

    pub(super) fn compatible(&self, other: &Self) -> bool {
        self.records.len() == other.records.len()
            && self.records.iter().all(|(id, a)| {
                other.records.get(id).is_some_and(|b| {
                    a.parent == b.parent
                        && a.definition.span.id == b.definition.span.id
                        && a.captures.compatible(&b.captures)
                        && a.completion == b.completion
                        && crate::ast_util::types_equal(&a.result, &b.result)
                        && a.detached.as_ref().map(|s| s.id) == b.detached.as_ref().map(|s| s.id)
                        && match (&a.waiter, &b.waiter) {
                            (None, None) => true,
                            (Some(a), Some(b)) => a.bytes == b.bytes && a.ids == b.ids,
                            _ => false,
                        }
                        && match (&a.stage, &b.stage) {
                            (Stage::Published(a), Stage::Published(b))
                            | (Stage::Completed(a), Stage::Completed(b)) => a.compatible(b),
                            (Stage::Running, Stage::Running) => true,
                            _ => false,
                        }
                })
            })
    }
}

impl Analysis<'_> {
    /// Collect the completed payload without copying or freeing its allocations.
    /// This does not build a native Result or prove that a native join succeeds;
    /// that adapter must consume checked body/domain effects in TODO 05.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "the TODO 05 join adapter consumes the completed payload")
    )]
    pub(super) fn collect_worker_result(
        &mut self,
        id: WorkerId,
        span: &Span,
    ) -> Result<Storage, VirErr> {
        let (result, handle, completion) = self.heap.workers.take_result(id, span)?;
        if self.layouts.size(&result.typ, span)? != result.value.bytes
            || self.layouts.owner(&result.typ) != result.owner.is_some()
        {
            return Err(unsupported(span, "incomplete worker result storage or ownership"));
        }
        self.release_value(handle, span);
        self.storage.release_values(&[completion].into());
        self.storage.event(span, "joined completion tag".into());
        Ok(result)
    }

    /// Publication transfers an existing closure value, retaining its storage.
    /// The child may run before this call returns; no body peak is added here.
    pub(super) fn spawn_owner(&mut self, expr: &Expr) -> Result<Option<Owner>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(_, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(None);
        };
        let Some(ResourceIntrinsic::Concurrency(operation)) = attrs.resource_intrinsic else {
            return Ok(None);
        };
        if !operation.spawns() {
            return Ok(None);
        }
        let [closure] = args.as_slice() else {
            return Err(unsupported(&expr.span, "this spawn signature"));
        };
        let TypX::AnonymousClosure(_, result, _, definition) = &*closure.typ else {
            return Err(unsupported(&closure.span, "spawning without a concrete closure"));
        };
        let info = self.concurrency.closures.get(definition).ok_or_else(|| {
            unsupported(&closure.span, "spawning without executable capture evidence")
        })?;
        if !info.by_move {
            return Err(unsupported(&closure.span, "scoped or non-move worker captures"));
        }
        let Some((handle_result, native)) = self.layouts.join_handle(&expr.typ) else {
            return Err(unsupported(&expr.span, "publication without a reviewed join-handle type"));
        };
        if native != (operation == super::concurrency::Operation::StdSpawn)
            || !crate::ast_util::types_equal(handle_result, result)
        {
            return Err(unsupported(
                &expr.span,
                "publication with inconsistent worker/result identities",
            ));
        }
        let definition_body = body::definition(
            closure,
            self.concurrency,
            self.functions.values().filter_map(|function| function.x.body.as_ref()),
        )?;
        let value = self.produce(closure)?;
        let owner = self.result_owner.take();
        let completion = self.storage.reserve_value(
            &expr.span,
            super::footprint::MemoryKind::host_heap(),
            verus_meter_model::completion_bytes(0).unwrap(),
        )?;
        self.storage.event(&expr.span, "publish worker completion tag".into());
        let id =
            self.growth.worker_families.publication(expr.span.id, *definition, self.current_worker);
        self.heap.workers.publish(
            id,
            &expr.span,
            self.current_worker,
            completion,
            body::Entry::checked(
                definition_body,
                Storage { typ: closure.typ.clone(), value, owner },
                self.concurrency,
                self.layouts,
            )?,
        )?;
        Ok(Some(Owner { worker: Some(id), ..Default::default() }))
    }

    /// A native join is a waiting boundary. Its source handle moves into the
    /// retained call frame, not into free storage. The result adapter needs a
    /// checked body summary and panic-free-domain proof before claiming success.
    pub(super) fn wait_for_worker(&mut self, expr: &Expr) -> Result<(), VirErr> {
        let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &expr.x else {
            return Ok(());
        };
        let Some(ResourceIntrinsic::Concurrency(operation)) = attrs.resource_intrinsic else {
            return Ok(());
        };
        if !operation.joins() {
            return Ok(());
        }
        let [argument] = args.as_slice() else {
            return Err(unsupported(&expr.span, "this join signature"));
        };
        let value = self.produce(argument)?;
        let owner = self
            .result_owner
            .take()
            .ok_or_else(|| unsupported(&argument.span, "joining without an owned handle"))?;
        let id = owner
            .worker
            .ok_or_else(|| unsupported(&argument.span, "joining without worker provenance"))?;
        self.heap.workers.wait(id, &expr.span, value)?;
        Err(unsupported(
            &expr.span,
            "join result ownership requires checked worker-body and completion effects",
        ))
    }
}

#[cfg(test)]
mod tests;
