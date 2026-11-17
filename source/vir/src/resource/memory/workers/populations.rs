//! Runtime forests carry immutable occurrence observations alongside handles.
//! Transport never completes a worker. The body graph retains its allocation
//! and completion states for global composition; the coordinator materializes
//! received result ownership at the checked join.

use super::super::{analysis::Analysis, heap::Owner, metadata::expr, model::unsupported};
use super::{Stage, WorkerId};
use crate::{ast::*, messages::Span};

#[derive(Clone)]
pub(in super::super) struct Occurrence {
    /// Checked body template; the record below distinguishes its runtime visits.
    pub(in super::super) template: WorkerId,
    /// Selected immutable descriptor, including identity and construction inputs.
    pub(in super::super) record: Expr,
}

impl super::Workers {
    pub(in super::super) fn detach_occurrence(&mut self, span: &Span) {
        self.detached_occurrence = Some(span.clone());
    }
}

impl Analysis<'_> {
    pub(super) fn join_occurrence(
        &mut self,
        source: &Expr,
        argument: &Expr,
        handle: super::super::lifetime::Value,
        mut owner: Owner,
    ) -> Result<super::super::lifetime::Value, VirErr> {
        let occurrence = owner.worker_occurrence.take().unwrap();
        if self.heap.workers.blocked(self.current_worker) {
            return Err(unsupported(&source.span, "collection while the caller is waiting"));
        }
        let execution = self.growth.worker_executions[&occurrence.template].clone();
        let (payload, _) = self
            .layouts
            .result_payloads(&source.typ)
            .ok_or_else(|| unsupported(&source.span, "population join without a native result"))?;
        let payload = payload.clone();
        if !crate::ast_util::types_equal(&payload, &execution.result.typ) {
            return Err(unsupported(&source.span, "population join with a foreign result type"));
        }
        let memory = expr::operation(
            &source.span,
            "worker_result",
            vec![occurrence.record.clone()],
            expr::memory_type(),
        );
        let result_owner = if self.layouts.owner(&payload) {
            Some(self.owner_from_metadata(
                &source.span,
                &payload,
                memory,
                super::super::metadata::View::Complete,
                false,
            )?)
        } else {
            None
        };
        let bytes = self.layouts.size(&payload, &source.span)?;
        let id = self.storage.reserve_value(
            &source.span,
            super::super::footprint::MemoryKind::host_local(),
            bytes,
        )?;
        let value = super::super::lifetime::Value {
            bytes,
            ids: [id].into(),
            origins: [id].into(),
            ..super::super::lifetime::Value::unit()
        };
        self.release_owner(owner, &source.span);
        self.release_value(handle, &source.span);
        self.growth.worker_join_occurrences.insert(source.span.id, occurrence.record);
        self.transitions.operation(
            &source.span,
            super::super::transfer::checked::Operation::WorkerJoin { source: argument.clone() },
        );
        self.pack_worker_result(
            source,
            occurrence.template,
            super::super::lifetime::Storage { typ: payload, value, owner: result_owner },
        )
    }

    /// Restore the one source-selected occurrence, retaining the immutable
    /// record rather than consulting the last analyzed publication's captures.
    pub(in super::super) fn worker_from_metadata(
        &mut self,
        span: &Span,
        typ: &Typ,
        memory: Expr,
        view: super::super::metadata::View,
        zero_charge: bool,
    ) -> Result<Owner, VirErr> {
        let (result, _) = self.layouts.join_handle(typ).unwrap();
        let mut candidates = self.growth.retained_worker_families.iter().filter(|id| {
            crate::ast_util::types_equal(&self.growth.worker_executions[id].result.typ, result)
        });
        let actor = *candidates
            .next()
            .ok_or_else(|| unsupported(span, "a worker selection without a checked body family"))?;
        if candidates.next().is_some() {
            return Err(unsupported(
                span,
                "selection from multiple worker families without a conditional body interface",
            ));
        }
        let memory = self.metadata_local(span, "selected_worker", memory);
        let record = expr::lookup(span, memory.clone(), expr::path(span, []));
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            expr::operation(
                span,
                "worker_matches",
                vec![record.clone(), expr::path(span, actor.descriptor())],
                crate::ast_util::bool_typ(),
            ),
            "cannot establish the selected worker's family and result description",
        ));
        let bytes =
            if zero_charge { expr::integer(span, 0) } else { self.metadata_sum(span, memory) };
        let allocation = super::super::accounting::Accounting::fresh_allocation();
        self.storage.set_allocation(
            allocation,
            super::super::footprint::MemoryKind::host_heap(),
            bytes.clone(),
        );
        Ok(Owner {
            worker_occurrence: Some(Occurrence { template: actor, record }),
            view,
            dynamic: Some(allocation),
            extent: Some(bytes),
            ..Default::default()
        })
    }

    /// Keep observations at publication, after the executable closure operand
    /// has established its construction snapshots. They are ordinary erased
    /// assignments, never assumptions about a later worker state.
    pub(super) fn observe_worker_publication(
        &mut self,
        actor: WorkerId,
        source: &Expr,
    ) -> Result<(), VirErr> {
        let execution = self.growth.worker_executions[&actor].clone();
        if execution.transfer.is_none() {
            return Ok(());
        }
        let span = &source.span;
        let ExprX::Call { args, .. } = &source.x else { unreachable!() };
        self.transitions.operation(
            span,
            super::super::transfer::checked::Operation::WorkerPublish {
                source: args[0].clone(),
                identity: self.worker_identity(span, actor),
                inputs: execution
                    .inputs
                    .iter()
                    .map(|input| (input.typ.clone(), input.slot.clone()))
                    .collect(),
                result: execution.transfer.clone().unwrap(),
            },
        );
        let first = self.growth.before.get(&span.id).map_or(0, Vec::len);
        let result = self
            .worker_result_memory(&execution, span)?
            .unwrap_or_else(|| expr::empty(span, expr::record_type()));
        let mut inputs = expr::empty(span, expr::record_type());
        for input in &execution.inputs {
            let path = expr::path(span, [self.layouts.metadata_slot(&input.slot)]);
            if let Some(value) = &input.scalar {
                inputs = expr::push(
                    span,
                    inputs,
                    expr::scalar_observation(span, path.clone(), value.clone()),
                );
            }
            for (fields, value) in &input.projections {
                let field_path = fields.iter().fold(path.clone(), |path, field| {
                    expr::push(
                        span,
                        path,
                        expr::integer(
                            span,
                            self.layouts.metadata_slot(&super::super::heap::OwnerSlot::Field(
                                field.clone(),
                            )),
                        ),
                    )
                });
                inputs = expr::push(
                    span,
                    inputs,
                    expr::scalar_observation(span, field_path, value.clone()),
                );
            }
            if let Some(owner) = execution
                .entry
                .storage
                .owner
                .as_ref()
                .and_then(|owner| owner.children.get(&input.slot))
            {
                let previous = std::mem::replace(&mut self.storage, execution.initial.clone());
                let mut proofs = Vec::new();
                let memory = self.call_metadata(span, owner, &mut proofs);
                self.storage = previous;
                self.growth.before.entry(span.id).or_default().extend(proofs);
                inputs = expr::add(span, inputs, expr::prefix(span, memory?, path));
            }
        }
        let record = expr::operation(
            span,
            "worker_observation",
            vec![expr::path(span, []), self.worker_identity(span, actor), inputs, result],
            expr::record_type(),
        );
        let memory = expr::push(span, expr::empty(span, expr::record_type()), record);
        let memory = self.metadata_local(span, "worker_observation", memory);
        let statements = self.growth.before.entry(span.id).or_default().split_off(first);
        self.growth.after.entry(span.id).or_default().extend(statements);
        self.growth.worker_observations.insert(actor, memory);
        Ok(())
    }

    /// Move responsibility for a completion tag into its collection's byte
    /// forest. Its identity and body remain in the descriptor, not a single
    /// mutable worker record reused for every iteration.
    pub(in super::super) fn retain_worker_in_forest(
        &mut self,
        owner: &mut Owner,
        span: &Span,
    ) -> Result<(), VirErr> {
        for child in owner.children.values_mut() {
            self.retain_worker_in_forest(child, span)?;
        }
        let Some(actor) = owner.worker else { return Ok(()) };
        let memory = self.growth.worker_observations.get(&actor).cloned().ok_or_else(|| {
            unsupported(span, "a retained worker without its checked occurrence description")
        })?;
        let worker =
            self.heap.workers.records.get(&actor).ok_or_else(|| {
                unsupported(span, "a retained worker outside its publishing domain")
            })?;
        if !matches!(worker.stage, Stage::Running)
            || worker.waiter.is_some()
            || worker.detached.is_some()
        {
            return Err(unsupported(span, "transport of a consumed worker occurrence"));
        }
        if !worker.entry_shared.is_empty() || !worker.execution.as_ref().unwrap().shared.is_empty()
        {
            return Err(unsupported(
                span,
                "retained worker shared-reference populations without their conservation relation",
            ));
        }
        let worker = self.heap.workers.records.remove(&actor).unwrap();
        self.storage.release_values(&[worker.completion].into());
        let tag =
            super::super::contracts::literal(span, verus_meter_model::completion_bytes(0).unwrap());
        self.storage.set_allocation(worker.completion, owner.kind.clone(), tag.clone());
        owner.worker = None;
        owner.dynamic = Some(worker.completion);
        owner.extent = Some(tag);
        owner.worker_occurrence = Some(Occurrence {
            template: actor,
            record: expr::lookup(span, memory, expr::path(span, [])),
        });
        self.growth.retained_worker_families.insert(actor);
        // Later selections need the inverse indexed view of the symbolic
        // collection, just as selections from a helper-produced forest do.
        self.growth.transferred_views = true;
        self.transitions.retained_workers = true;
        Ok(())
    }
}
