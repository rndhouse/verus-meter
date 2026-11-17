//! Worker-owned storage outlives publication and the caller's join-handle slot.
//!
//! This is ownership state, not a sum of independent worker peaks. Publication,
//! body execution/cleanup, completion and join remain separate effects; later
//! composition must consider every permitted interleaving of their phase graphs.

use super::{analysis::Analysis, heap::Owner, lifetime::Storage, model::unsupported};
use crate::{ast::*, messages::Span};
use std::collections::BTreeMap;

mod body;
mod captures;
pub(super) mod execution;
mod identity;
mod inputs;
mod outputs;
mod results;
mod waits;

pub(super) use identity::{Families, WorkerId};
pub(super) use inputs::restore_proof_bindings;
pub(crate) use results::generated_join_move;
pub(super) use results::resolve_join;

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
    /// Independent checked execution, including its retained result. Analysis of
    /// this graph does not assert that the child already ran at publication.
    execution: Option<std::sync::Arc<execution::Execution>>,
    parent: Option<WorkerId>,
    /// Actual executable body retained across publication and source moves.
    definition: Expr,
    /// Construction-epoch inputs survive capture consumption during execution.
    environment: super::closures::observations::EnvironmentId,
    /// Source receiver convention and responsibility for environment cleanup.
    invocation: super::concurrency::invocation::Invocation,
    /// Imported entry references are requirements, not a sampled global count.
    entry_shared: super::shared::SharedRoots,
    /// Source/body paths refer to fields of the retained environment charge.
    captures: captures::Captures,
    /// The completion tag is one distinct allocation, independent of the
    /// parent's inline handle and the result eventually stored behind it.
    completion: u64,
    result: Typ,
    stage: Stage,
    /// A wait consumes the source handle but retains its inline call argument.
    waiter: Option<waits::Waiter>,
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
        if self.blocked(parent) {
            return Err(unsupported(
                span,
                "worker publication while the spawning thread is waiting",
            ));
        }
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
                execution: None,
                parent,
                definition: entry.definition.clone(),
                environment: entry.storage.value.environment.expect("checked worker inputs"),
                invocation: entry.invocation,
                entry_shared: entry.shared,
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
            invocation: worker.invocation,
            shared: worker.entry_shared.clone(),
        })
    }

    /// Production completion takes its result only from the checked execution.
    /// Callers cannot supply an alternate owner tree or result charge.
    fn complete(&mut self, id: WorkerId, span: &Span) -> Result<(), VirErr> {
        let execution =
            self.records.get(&id).and_then(|worker| worker.execution.as_ref()).ok_or_else(
                || unsupported(span, "worker completion without checked executable effects"),
            )?;
        if execution.actor != id {
            return Err(unsupported(span, "worker completion with a foreign execution"));
        }
        self.transition_completion(id, span, execution.result.clone())
    }

    fn transition_completion(
        &mut self,
        id: WorkerId,
        span: &Span,
        result: Storage,
    ) -> Result<(), VirErr> {
        if self.blocked(Some(id)) {
            return Err(unsupported(
                span,
                "worker completion before its pending join has returned",
            ));
        }
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
                        && a.environment == b.environment
                        && a.invocation == b.invocation
                        && a.entry_shared.compatible(&b.entry_shared)
                        && a.captures.compatible(&b.captures)
                        && a.completion == b.completion
                        && crate::ast_util::types_equal(&a.result, &b.result)
                        && a.detached.as_ref().map(|s| s.id) == b.detached.as_ref().map(|s| s.id)
                        && a.waiter == b.waiter
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
    /// the result adapter retains these proof dependencies at collection.
    pub(super) fn collect_worker_result(
        &mut self,
        id: WorkerId,
        span: &Span,
    ) -> Result<Storage, VirErr> {
        let (result, handle, completion) =
            self.heap.workers.take_result(id, self.current_worker, span)?;
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
        if (self.current_worker.is_some() || self.growth.loop_depth != 0)
            && matches!(&expr.x, ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. }
                if matches!(attrs.resource_intrinsic, Some(ResourceIntrinsic::Concurrency(op)) if op.spawns()))
        {
            return Err(unsupported(
                &expr.span,
                "symbolic or nested worker populations before concurrent lifetime accounting is available",
            ));
        }
        let Some(owner) = self.publish_owner(expr)? else { return Ok(None) };
        self.analyze_worker(owner.worker.expect("published actor"), &expr.span)?;
        Ok(Some(owner))
    }

    /// Publication is a separate transition from body analysis. Keeping this
    /// boundary explicit also permits testing invalid lifecycle transitions
    /// without inventing checked executable summaries.
    fn publish_owner(&mut self, expr: &Expr) -> Result<Option<Owner>, VirErr> {
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
                &self.growth.environments,
                &self.heap.shared,
            )?,
        )?;
        Ok(Some(Owner { worker: Some(id), ..Default::default() }))
    }

    /// A native join is a waiting boundary. Its source handle moves into the
    /// retained call frame, not into free storage. The result adapter needs a
    /// checked body summary and panic-free-domain proof before claiming success.
    pub(super) fn join_worker(
        &mut self,
        expr: &Expr,
    ) -> Result<Option<super::lifetime::Value>, VirErr> {
        let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &expr.x else {
            return Ok(None);
        };
        let Some(ResourceIntrinsic::Concurrency(operation)) = attrs.resource_intrinsic else {
            return Ok(None);
        };
        if !operation.joins() {
            return Ok(None);
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
        self.heap.workers.wait(id, self.current_worker, &expr.span, value)?;
        let execution = self.heap.workers.records[&id].execution.clone().ok_or_else(|| {
            unsupported(&expr.span, "join without checked executable worker effects")
        })?;
        let worker = &self.heap.workers.records[&id];
        if execution.actor != id
            || !matches!(&*worker.definition.typ, TypX::AnonymousClosure(_, _, _, definition) if *definition == execution.definition)
        {
            return Err(unsupported(&expr.span, "wrong worker actor or definition at join"));
        }
        let Some((success, failure)) = self.layouts.result_payloads(&expr.typ) else {
            return Err(unsupported(&expr.span, "join without its primitive-specific Result type"));
        };
        if !crate::ast_util::types_equal(success, &execution.result.typ)
            || (operation == super::concurrency::Operation::VstdJoin
                && !super::model::unit(failure))
        {
            return Err(unsupported(&expr.span, "inconsistent primitive join result payloads"));
        }
        self.heap.workers.complete(id, &expr.span)?;
        let mut retained = execution.retained.clone();
        let mut result_owner = execution.result.owner.clone();
        if let Some(owner) = &mut result_owner {
            self.rebind_worker_output(owner, &mut retained, &execution, &expr.span, true)?;
        }
        let mut shared = execution.shared.clone();
        shared.map_owned(|owner| {
            self.rebind_worker_output(owner, &mut retained, &execution, &expr.span, false)
        })?;
        self.storage.receive_storage(retained, &expr.span)?;
        for backing in self.heap.shared.receive_worker(&shared, &expr.span)? {
            self.release_owner(backing, &expr.span);
        }
        let mut result = self.collect_worker_result(id, &expr.span)?;
        result.owner = result_owner;
        self.growth.worker_joins.insert(expr.span.id, id);
        let bytes = self.layouts.size(&expr.typ, &expr.span)?;
        let extra = bytes
            .checked_sub(result.value.bytes)
            .ok_or_else(|| unsupported(&expr.span, "a join result smaller than its payload"))?;
        let tag = self.storage.reserve_value(
            &expr.span,
            super::footprint::MemoryKind::host_local(),
            extra,
        )?;
        let packed = self
            .storage
            .pack_values(&[(&result.value.ids, result.value.bytes), (&[tag].into(), extra)], bytes);
        let mut origins = result.value.origins;
        origins.insert(packed);
        self.result_owner = Some(Owner {
            joined: Some(id),
            children: result
                .owner
                .into_iter()
                .map(|owner| (super::heap::OwnerSlot::Contents, owner))
                .collect(),
            ..Default::default()
        });
        Ok(Some(super::lifetime::Value {
            bytes,
            ids: [packed].into(),
            origins,
            parameter: None,
            environment: None,
        }))
    }
}

#[cfg(test)]
mod tests;
