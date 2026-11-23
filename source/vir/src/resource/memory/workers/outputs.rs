//! Rebind surviving allocation facts at collection. Worker-local proof variables
//! cannot escape their closure. Unchanged allocations retain exact constructor
//! expressions when they close over construction inputs; other extents use the
//! body's proved local bound, as ordinary ownership summaries do.

use super::super::{
    accounting::Accounting,
    analysis::Analysis,
    contracts,
    elements::References,
    footprint::Charge,
    heap::Owner,
    metadata::{expr, runtime_shape_proof},
    model::unsupported,
};
use super::{execution::Execution, inputs::Input};
use crate::{ast::*, messages::Span};
use std::collections::{HashMap, HashSet};

fn close(value: &Expr, inputs: &[Input], allowed: &HashSet<VarIdent>) -> Option<Expr> {
    let value = crate::ast_visitor::map_expr_visitor(value, &|value| {
        if let Some((name, path)) = super::super::paths::expr(value, &value.typ)
            && let Some(input) = inputs.iter().find(|input| input.name == name)
            && !path.is_empty()
        {
            let fields: Option<Vec<_>> = path
                .iter()
                .map(|slot| match slot {
                    super::super::heap::OwnerSlot::Field(field) => Some(field.clone()),
                    _ => None,
                })
                .collect();
            if let Some(fields) = fields
                && let Some((_, observed)) =
                    input.projections.iter().find(|(path, _)| *path == fields)
            {
                return Ok(observed.clone());
            }
        }
        if let ExprX::Var(name) = &value.x
            && let Some(input) = inputs.iter().find(|input| input.name == *name)
            && let Some(scalar) = &input.scalar
        {
            return Ok(scalar.clone());
        }
        Ok(value.clone())
    })
    .ok()?;
    crate::ast_visitor::expr_visitor_check(&value, &mut |_, value| {
        if let ExprX::Var(name) = &value.x
            && !allowed.contains(name)
        {
            return Err(());
        }
        Ok(())
    })
    .ok()?;
    Some(value)
}

impl super::FixedHandle {
    /// Read the result from this handle's frozen publication in the joining frame.
    pub(super) fn result_memory(&self, span: &Span) -> Result<Expr, VirErr> {
        let observation = self.publication.as_ref().ok_or_else(|| {
            unsupported(span, "a worker population result without its handle's checked publication")
        })?;
        let record = expr::lookup(span, observation.clone(), expr::path(span, []));
        Ok(expr::operation(span, "worker_result", vec![record], expr::memory_type()))
    }
}

impl Analysis<'_> {
    /// Instantiate the same parameter-relative transformation used by ordinary
    /// helpers. Entry owners and their charge state are immutable observations;
    /// no body-local proof variable is allowed to escape through this interface.
    pub(super) fn worker_result_memory(
        &mut self,
        execution: &Execution,
        span: &Span,
    ) -> Result<Option<Expr>, VirErr> {
        use super::super::transfer::Input as Symbol;
        let Some(template) = &execution.transfer else { return Ok(None) };
        let owner = |index: usize| {
            execution
                .entry
                .storage
                .owner
                .as_ref()
                .and_then(|owner| owner.children.get(&execution.inputs[index].slot))
                .ok_or_else(|| {
                    unsupported(span, "a worker result template without its captured owner")
                })
        };
        let mut values = HashMap::new();
        for symbol in &template.symbols {
            let value = match &symbol.input {
                Symbol::LockTest => {
                    return Err(unsupported(
                        span,
                        "a worker result depending on an internal lock outcome",
                    ));
                }
                Symbol::Complete => crate::ast_util::mk_bool(
                    span,
                    execution.entry.storage.owner.as_ref().is_none_or(Owner::complete),
                ),
                Symbol::Scalar(index) => {
                    execution.inputs[*index].scalar.clone().ok_or_else(|| {
                        unsupported(span, "a worker result template without a scalar observation")
                    })?
                }
                Symbol::SliceLength(_) => {
                    return Err(unsupported(
                        span,
                        "a worker result that depends on a slice length",
                    ));
                }
                Symbol::Forest(index) => {
                    // Serialization reads the saved accounting view; it neither
                    // transfers storage nor records a new memory event.
                    let captured = owner(*index)?;
                    let current = std::mem::replace(&mut self.storage, execution.initial.clone());
                    let mut proofs = Vec::new();
                    if let Some(elements) = &captured.elements
                        && elements.references == References::WorkerOccurrences
                    {
                        // Indexed handle records cannot shadow the vector's root
                        // descriptor when the template reads its length and backing.
                        proofs.push(runtime_shape_proof(span, elements.records.clone()));
                        proofs.push(expr::lemma(
                            span,
                            "cost_runtime_partition",
                            vec![elements.records.clone(), expr::integer(span, 0)],
                        ));
                        proofs.push(expr::lemma(
                            span,
                            "runtime_class",
                            vec![elements.records.clone()],
                        ));
                    }
                    let memory = self.call_metadata(span, captured, &mut proofs);
                    self.storage = current;
                    self.growth.before.entry(span.id).or_default().extend(proofs);
                    memory?
                }
                Symbol::Property(index, path, field) => {
                    let owner = owner(*index)?.at(path).ok_or_else(|| {
                        unsupported(
                            span,
                            "a worker result template with a different input ownership path",
                        )
                    })?;
                    match *field {
                        "length" => self.owner_length(span, owner),
                        "capacity" => owner
                            .vector
                            .map(|id| self.growth.vectors[id].capacity.clone())
                            .or_else(|| owner.capacity.clone())
                            .unwrap_or_else(|| contracts::literal(span, 0)),
                        "bytes" => {
                            let fixed = contracts::literal(span, owner.bytes);
                            owner.dynamic.map_or(fixed.clone(), |id| {
                                contracts::add(
                                    span,
                                    fixed,
                                    execution.initial.dynamic_cost(span, id),
                                )
                            })
                        }
                        _ => return Err(unsupported(span, "an unknown worker ownership property")),
                    }
                }
                Symbol::Minimum(index, path) => {
                    let mut minima = Default::default();
                    self.owner_minima(owner(*index)?, &mut vec![], &mut minima);
                    minima
                        .get(path)
                        .map(|floor| floor.capacity.clone())
                        .unwrap_or_else(|| contracts::literal(span, 0))
                }
            };
            values.insert(symbol.name.clone(), value);
        }
        Ok(self.specialize_worker_result(span, template, &values)?.map(|node| node.memory))
    }

    /// A worker mutates its own erased allocation state. Capturing an owned
    /// vector must not make generated assignments write into the parent's
    /// proof locals, even though the physical allocation keeps the same ID.
    pub(super) fn enter_worker_owner(
        &mut self,
        owner: &mut Owner,
        span: &Span,
    ) -> Result<(), VirErr> {
        if let Some(id) = owner.vector {
            let old = self.growth.vectors[id].clone();
            let state = self.growth.new_vector(
                span,
                old.capacity.clone(),
                Charge { kind: old.backing.kind.clone(), amount: old.backing.bytes.clone() },
                old.element,
                old.backing.input_bytes,
                old.backing.id,
            );
            self.storage.set_allocation(
                old.backing.id,
                old.backing.kind,
                self.growth.vectors[state].backing.bytes.clone(),
            );
            if let Some(length) = old.protected_length {
                let length = self.allocation_snapshot(span, length);
                let next = &mut self.growth.vectors[state];
                next.protected_length = Some(length.clone());
                next.local_constructor = old.local_constructor;
                next.minimum = old.minimum;
                owner.geometry = Some(length);
            }
            owner.vector = Some(state);
            owner.capacity = Some(old.capacity);
        }
        if let Some(old) = owner.elements.take() {
            owner.elements = Some(self.fork_elements(old, span));
        }
        for child in owner.children.values_mut() {
            self.enter_worker_owner(child, span)?;
        }
        Ok(())
    }

    /// Preserve the transferred allocation IDs while giving the collecting
    /// actor its own proof state. No result bytes are allocated a second time.
    pub(super) fn rebind_worker_output(
        &mut self,
        owner: &mut Owner,
        retained: &mut Accounting,
        execution: &Execution,
        span: &Span,
        result: Option<&super::FixedHandle>,
    ) -> Result<(), VirErr> {
        let mut allowed = self.stable_scalars.clone();
        for declaration in &self.growth.declarations {
            if let StmtX::Decl { pattern, .. } = &declaration.x
                && let PatternX::Var(binding) = &pattern.x
            {
                allowed.insert(binding.name.clone());
            }
        }
        let mut needs_template = false;
        let mut population = false;
        owner.visit(&mut |node| {
            population |= node
                .elements
                .as_ref()
                .is_some_and(|elements| elements.references == References::WorkerOccurrences);
            if result.is_none() || execution.transfer.is_none() || needs_template {
                return;
            }
            // A selected worker result can have unchanged backing whose size
            // references a proof local in the collecting actor. Its checked
            // template closes that observation over the captured handle.
            needs_template |= node.vector.is_some_and(|id| {
                let backing = &self.growth.vectors[id].backing;
                backing.changed
                    || close(&backing.initial_bytes, &execution.inputs, &allowed).is_none()
            }) || node
                .elements
                .as_ref()
                .is_some_and(|elements| !elements.zero_charge(&self.growth));
        });
        let memory = if let Some(handle) = result
            && population
        {
            Some(handle.result_memory(span)?)
        } else if needs_template {
            self.worker_result_memory(execution, span)?
        } else {
            None
        };
        self.rebind_worker_node(owner, retained, execution, span, &allowed, memory)
    }

    fn rebind_worker_node(
        &mut self,
        owner: &mut Owner,
        retained: &mut Accounting,
        execution: &Execution,
        span: &Span,
        allowed: &HashSet<VarIdent>,
        memory: Option<Expr>,
    ) -> Result<(), VirErr> {
        if let Some(elements) = owner.elements.take() {
            let records = memory.as_ref().map(|memory| {
                super::super::metadata::expr::operation(
                    span,
                    "runtime",
                    vec![memory.clone()],
                    super::super::metadata::expr::memory_type(),
                )
            });
            owner.elements = Some(self.collect_worker_elements(elements, records, retained, span)?);
        }
        if let Some(id) = owner.vector {
            let previous = &self.growth.vectors[id];
            let bytes = memory
                .as_ref()
                .map(|memory| super::super::transfer::property(span, memory.clone(), "bytes"))
                .or_else(|| {
                    if previous.backing.changed {
                        None
                    } else {
                        close(&previous.backing.initial_bytes, &execution.inputs, allowed)
                    }
                })
                .unwrap_or_else(|| self.bound.clone());
            let capacity = memory
                .as_ref()
                .map(|memory| super::super::transfer::property(span, memory.clone(), "capacity"))
                .or_else(|| {
                    if previous.backing.changed {
                        None
                    } else {
                        owner
                            .capacity
                            .as_ref()
                            .and_then(|capacity| close(capacity, &execution.inputs, allowed))
                    }
                })
                .unwrap_or_else(|| contracts::literal(span, 0));
            let kind = previous.backing.kind.clone();
            let allocation = previous.backing.id;
            let element = previous.element;
            let state = self.growth.new_vector(
                span,
                capacity.clone(),
                Charge { kind: kind.clone(), amount: bytes.clone() },
                element,
                (owner.view == super::super::metadata::View::Local).then_some(0),
                allocation,
            );
            retained.set_allocation(
                allocation,
                kind,
                self.growth.vectors[state].backing.bytes.clone(),
            );
            owner.vector = Some(state);
            owner.capacity = Some(capacity);
            owner.extent = Some(bytes);
        } else if let Some(id) = owner.dynamic {
            let bytes = owner
                .extent
                .as_ref()
                .and_then(|extent| close(extent, &execution.inputs, allowed))
                .unwrap_or_else(|| self.bound.clone());
            retained.set_allocation(id, owner.kind.clone(), bytes.clone());
            owner.extent = Some(bytes);
        }
        // A collected binding will supply the logical value again. Keeping an
        // inaccessible body-local source here would permit stale length facts.
        owner.source = None;
        owner.geometry = memory
            .as_ref()
            .map(|memory| super::super::transfer::property(span, memory.clone(), "length"))
            .or_else(|| {
                owner.geometry.as_ref().and_then(|value| close(value, &execution.inputs, allowed))
            });
        for (slot, child) in &mut owner.children {
            let selected = memory.as_ref().map(|memory| {
                super::super::metadata::expr::subtree(
                    span,
                    memory.clone(),
                    super::super::metadata::expr::path(span, [self.layouts.metadata_slot(slot)]),
                )
            });
            self.rebind_worker_node(child, retained, execution, span, allowed, selected)?;
        }
        Ok(())
    }
}
