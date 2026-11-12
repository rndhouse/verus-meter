//! Container operation adapters for finite ownership transformations.

use super::*;
use crate::resource::memory::metadata::operations::Removal;

impl Trace<'_> {
    pub(super) fn operation(
        &mut self,
        value: &Expr,
        operation: checked::Operation,
    ) -> Option<Value> {
        let span = &value.span;
        use checked::Operation;
        match operation {
            Operation::Evaluate { args } => {
                for argument in args.iter() {
                    self.value(argument)?;
                }
                Some(Value::Unknown)
            }
            Operation::Vector { capacity, element } => {
                let actual =
                    contracts::multiply(span, capacity.clone(), contracts::literal(span, element));
                let capacity = self.scalar(&capacity)?;
                if self.loop_tokens.is_some() {
                    self.loop_allocations.push((
                        span.clone(),
                        actual,
                        contracts::multiply(
                            span,
                            capacity.clone(),
                            contracts::literal(span, element),
                        ),
                    ));
                }
                let memory = expr::push(
                    span,
                    expr::empty(span, expr::record_type()),
                    allocated(
                        span,
                        contracts::multiply(
                            span,
                            capacity.clone(),
                            contracts::literal(span, element),
                        ),
                        capacity.clone(),
                        expr::integer(span, 0),
                    ),
                );
                Some(Value::Owner(Node {
                    origin: None,
                    typ: value.typ.clone(),
                    memory,
                    minima: [(vec![], Floor { capacity, element })].into(),
                }))
            }
            Operation::Box { payload, bytes } => {
                let child = self.value(&payload)?;
                if self.loop_tokens.is_some() {
                    let amount = contracts::literal(span, bytes);
                    self.loop_allocations.push((span.clone(), amount.clone(), amount));
                }
                let mut memory = expr::push(
                    span,
                    expr::empty(span, expr::record_type()),
                    allocated(
                        span,
                        contracts::literal(span, bytes),
                        expr::integer(span, 0),
                        expr::integer(span, 0),
                    ),
                );
                let mut minima = Minima::new();
                if let Value::Owner(child) = child {
                    memory = expr::add(
                        span,
                        memory,
                        expr::prefix(
                            span,
                            child.memory,
                            expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
                        ),
                    );
                    minima.extend(child.minima.into_iter().map(|(path, floor)| {
                        (
                            std::iter::once(Step::Fixed(OwnerSlot::Contents)).chain(path).collect(),
                            floor,
                        )
                    }));
                }
                Some(Value::Owner(Node { origin: None, typ: value.typ.clone(), memory, minima }))
            }
            Operation::Length { receiver } => {
                let location = self.checked_location(&receiver)?;
                let node = self.get(span, &location, &receiver.typ)?;
                self.effects.push(Effect::Read(location.0));
                Some(Value::Scalar(property(span, node.memory, "length")))
            }
            Operation::Push { receiver, child, element, grow, allocation, input } => {
                let location = self.checked_location(&receiver)?;
                let mut node = self.get(span, &location, &receiver.typ)?;
                node.origin = None;
                let child = self.value(&child)?;
                if self.loop_tokens.is_some()
                    && self.loop_roots.as_ref().is_some_and(|roots| !roots.contains(&location.0))
                {
                    if let Some(actual) = allocation {
                        let candidate = contracts::multiply(
                            span,
                            contracts::literal(span, element),
                            growth::grown_capacity(
                                span,
                                contracts::literal(span, self.loop_size_ceiling),
                                element,
                            ),
                        );
                        self.loop_allocations.push((span.clone(), actual, candidate));
                    }
                }
                let appended = child.clone();
                let length = property(span, node.memory.clone(), "length");
                let capacity = property(span, node.memory.clone(), "capacity");
                let bytes = property(span, node.memory.clone(), "bytes");
                let original = if let Some(input) = input {
                    let original = self.original_child(span, &input)?;
                    self.join_region(span, &location, length.clone(), &input)?;
                    original
                } else {
                    expr::empty(span, expr::record_type())
                };
                let (capacity, bytes) = if grow {
                    let complete = self.complete_for(span, std::slice::from_ref(&bytes));
                    let (lower, _, _) = growth::push_transition(
                        span,
                        capacity.clone(),
                        bytes.clone(),
                        length.clone(),
                        element,
                        false,
                    );
                    let (capacity, bytes, _) = growth::push_transition(
                        span,
                        capacity,
                        bytes,
                        length.clone(),
                        element,
                        true,
                    );
                    (choice(span, complete, capacity, lower), bytes)
                } else {
                    (capacity, bytes)
                };
                if let Value::Owner(child) = child {
                    let path = expr::push(span, expr::path(span, []), length.clone());
                    node.memory =
                        expr::add(span, node.memory, expr::prefix(span, child.memory, path));
                    let children = child
                        .minima
                        .into_iter()
                        .map(|(path, floor)| {
                            (std::iter::once(Step::Repeated).chain(path).collect(), floor)
                        })
                        .collect();
                    join_minima(span, &mut node.minima, &children);
                }
                node.memory = with_root(
                    span,
                    node.memory,
                    bytes,
                    capacity,
                    contracts::add(span, length, expr::integer(span, 1)),
                    self.layouts.owning_elements(&node.typ),
                );
                let typ = node.typ.clone();
                self.set(span, &location, node)?;
                if self.branch_depth == 0 {
                    self.effects.pop();
                    self.effects.push(Effect::Append {
                        location,
                        typ,
                        child: appended,
                        original,
                        element,
                        grow,
                    });
                }
                Some(Value::Unit)
            }
            Operation::Remove { receiver, index, input } => {
                let optional = index.is_none();
                let location = self.checked_location(&receiver)?;
                let mut node = self.get(span, &location, &receiver.typ)?;
                node.origin = None;
                let length = property(span, node.memory.clone(), "length");
                let removal = if optional {
                    Removal::pop(span, length)
                } else {
                    Removal::remove(span, length, self.scalar(index.as_ref()?)?)
                };
                let partition = removal.partition(span, node.memory.clone());
                let token = if optional
                    && self.branch_depth == 0
                    && self.loop_tokens.is_some()
                    && self.loop_roots.as_ref().is_some_and(|roots| roots.contains(&location.0))
                    && self.layouts.owner(&value.typ)
                {
                    let name = VarIdent(
                        Arc::new("$memory_iteration_child".into()),
                        VarIdentDisambiguate::VirTemp(span.id),
                    );
                    self.loop_tokens.as_mut()?.insert(name.clone());
                    Some(name)
                } else {
                    None
                };
                let original = if let Some(input) = input {
                    let name = token.as_ref().map(|_| {
                        VarIdent(
                            Arc::new("$memory_iteration_original".into()),
                            VarIdentDisambiguate::VirTemp(span.id),
                        )
                    });
                    let selected = name.as_ref().map(|name| {
                        SpannedTyped::new(span, &expr::memory_type(), ExprX::Var(name.clone()))
                    });
                    let witness = self.partition_region_selected(
                        span,
                        &location,
                        &input,
                        |memory| removal.partition(span, memory),
                        selected,
                    )?;
                    name.map(|name| (name, witness))
                } else {
                    None
                };
                let tag = if let Some(token) = &token {
                    let name = VarIdent(
                        Arc::new("$memory_iteration_presence".into()),
                        VarIdentDisambiguate::VirTemp(span.id),
                    );
                    self.loop_tokens.as_mut()?.insert(name.clone());
                    self.loop_inputs.insert(
                        token.clone(),
                        Selection {
                            memory: partition.selected.clone(),
                            original,
                            presence: (name.clone(), removal.tag.clone()?),
                        },
                    );
                    Some(SpannedTyped::new(span, &int_typ(), ExprX::Var(name)))
                } else {
                    removal.tag.clone()
                };
                let next = with_root(
                    span,
                    partition.remaining,
                    property(span, node.memory.clone(), "bytes"),
                    property(span, node.memory.clone(), "capacity"),
                    removal.length,
                    self.layouts.owning_elements(&node.typ),
                );
                let mut minima: Minima = node
                    .minima
                    .iter()
                    .filter_map(|(path, floor)| {
                        path.strip_prefix(&[Step::Repeated])
                            .map(|rest| (rest.to_vec(), floor.clone()))
                    })
                    .collect();
                node.memory = next;
                let typ = node.typ.clone();
                self.set(span, &location, node)?;
                if optional && self.branch_depth == 0 {
                    self.effects.pop();
                    self.effects.push(Effect::Pop { location, typ, token: token.clone() });
                }
                if !self.layouts.owner(&value.typ) {
                    return Some(Value::Unknown);
                }
                let selected = if let Some(name) = token {
                    SpannedTyped::new(span, &expr::memory_type(), ExprX::Var(name))
                } else {
                    partition.selected
                };
                let memory = if optional {
                    minima = minima
                        .into_iter()
                        .map(|(path, floor)| {
                            (
                                std::iter::once(Step::Fixed(OwnerSlot::Contents))
                                    .chain(path)
                                    .collect(),
                                floor,
                            )
                        })
                        .collect();
                    let tag = tag.expect("pop result tag");
                    expr::add(
                        span,
                        expr::push(
                            span,
                            expr::empty(span, expr::record_type()),
                            allocated(span, expr::integer(span, 0), expr::integer(span, 0), tag),
                        ),
                        expr::prefix(
                            span,
                            selected,
                            expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
                        ),
                    )
                } else {
                    selected
                };
                Some(Value::Owner(Node { origin: None, typ: value.typ.clone(), memory, minima }))
            }
            Operation::Unwrap { source } => {
                let Value::Owner(node) = self.value(&source)? else {
                    return Some(Value::Unknown);
                };
                let minima = node
                    .minima
                    .into_iter()
                    .filter_map(|(path, floor)| {
                        path.strip_prefix(&[Step::Fixed(OwnerSlot::Contents)])
                            .map(|rest| (rest.to_vec(), floor))
                    })
                    .collect();
                Some(Value::Owner(Node {
                    origin: None,
                    typ: value.typ.clone(),
                    memory: expr::subtree(
                        span,
                        node.memory,
                        expr::path(span, [self.layouts.metadata_slot(&OwnerSlot::Contents)]),
                    ),
                    minima,
                }))
            }
            Operation::Predicate { receiver, present } => {
                let location = self.checked_location(&receiver)?;
                let node = self.get(span, &location, &receiver.typ)?;
                let some =
                    mk_eq(span, &property(span, node.memory, "length"), &expr::integer(span, 1));
                let condition = if present {
                    some
                } else {
                    SpannedTyped::new(span, &bool_typ(), ExprX::Unary(UnaryOp::Not, some))
                };
                Some(Value::Scalar(condition))
            }
            Operation::IntoSlice { source, element, allocation } => {
                let Value::Owner(mut node) = self.value(&source)? else {
                    return None;
                };
                node.origin = None;
                let length = property(span, node.memory.clone(), "length");
                if self.loop_tokens.is_some() {
                    let candidate = contracts::multiply(
                        span,
                        contracts::literal(span, element),
                        contracts::literal(span, self.loop_size_ceiling),
                    );
                    self.loop_allocations.push((span.clone(), allocation, candidate));
                }
                node.memory = with_root(
                    span,
                    node.memory,
                    contracts::multiply(span, length.clone(), contracts::literal(span, element)),
                    expr::integer(span, 0),
                    length,
                    self.layouts.owning_elements(&node.typ),
                );
                node.minima.remove(&vec![]);
                node.typ = value.typ.clone();
                Some(Value::Owner(node))
            }
            Operation::Drop { source } => {
                self.value(&source)?;
                Some(Value::Unit)
            }
            Operation::Aggregate { fields, tag } => self.construct(value, fields, tag),
            Operation::Call {
                target, budget, args, borrowed, replaced_inputs, origins, ..
            } => {
                if self.loop_tokens.is_some() {
                    let candidate = self.scalar(&budget).unwrap_or_else(|| budget.clone());
                    self.loop_calls.push((span.clone(), budget.clone(), candidate.clone()));
                    if allocates(&self.summaries.get(&target)?.allocations) {
                        self.loop_allocations.push((span.clone(), budget, candidate));
                    }
                }
                for replacement in replaced_inputs {
                    if let Some(input) = &replacement.input {
                        let location = self.checked_location(&replacement.destination)?;
                        self.replace_region(span, &location, input)?;
                    }
                }
                self.checked_call(value, &target, &args, &borrowed, &origins)
            }
        }
    }

    fn checked_call(
        &mut self,
        value: &Expr,
        target: &Fun,
        args: &Exprs,
        borrowed: &HashMap<usize, checked::Place>,
        origins: &checked::CallOrigins,
    ) -> Option<Value> {
        let function = self.functions.get(target)?;
        let template = self.summaries.get(target)?.transfer.as_ref()?;
        let mut values = HashMap::new();
        let mut locations = HashMap::new();
        for (index, (arg, parameter)) in args.iter().zip(function.x.params.iter()).enumerate() {
            if parameter.x.mode != Mode::Exec {
                continue;
            }
            let actual = if let Some(place) = borrowed.get(&index) {
                let location = self.checked_location(place)?;
                let node = self.get(&arg.span, &location, &place.typ)?;
                locations.insert(index, location);
                Value::Owner(node)
            } else {
                self.value(arg)?
            };
            values.insert(index, actual);
        }
        let mut replacements = HashMap::new();
        for symbol in &template.symbols {
            if matches!(symbol.input, Input::Complete) {
                let forests: Vec<_> = values
                    .values()
                    .filter_map(|value| match value {
                        Value::Owner(node) => Some(node.memory.clone()),
                        _ => None,
                    })
                    .collect();
                let complete = self.complete_for(&value.span, &forests);
                replacements.insert(symbol.name.clone(), complete);
                continue;
            }
            let replacement = match (
                &symbol.input,
                values.get(&match &symbol.input {
                    Input::Complete => unreachable!(),
                    Input::Scalar(i)
                    | Input::Forest(i)
                    | Input::Property(i, _, _)
                    | Input::Minimum(i, _) => *i,
                })?,
            ) {
                (Input::Scalar(_), Value::Scalar(value)) => value.clone(),
                (Input::Forest(_), Value::Owner(node)) => node.memory.clone(),
                (Input::Property(_, path, field), Value::Owner(node)) => {
                    let selected = expr::subtree(
                        &value.span,
                        node.memory.clone(),
                        expr::path(
                            &value.span,
                            path.iter().map(|slot| self.layouts.metadata_slot(slot)),
                        ),
                    );
                    property(&value.span, selected, field)
                }
                (Input::Minimum(_, path), Value::Owner(node)) => node
                    .minima
                    .get(path)
                    .map(|f| f.capacity.clone())
                    .unwrap_or_else(|| expr::integer(&value.span, 0)),
                _ => return None,
            };
            replacements.insert(symbol.name.clone(), replacement);
        }
        self.compose_call_origins(value, function, template, &replacements, origins)?;
        let first_effect = self.effects.len();
        for (index, node) in &template.borrowed {
            self.set(&value.span, &locations[index], instantiate_node(node, &replacements))?;
        }
        if self.branch_depth == 0 {
            if let Some(effects) = &template.effects {
                self.effects.truncate(first_effect);
                let mut guards = HashMap::new();
                for (index, effect) in effects {
                    self.effects.push(effect.instantiate(
                        locations.get(index)?,
                        &replacements,
                        &values,
                        &mut guards,
                    ));
                }
            }
        }
        if let Value::Owner(Node { origin: Some(index), .. }) = &template.result {
            return values.get(index).cloned();
        }
        Some(instantiate_value(&template.result, &replacements))
    }
}

/// Helper allowances bound only allocations introduced in that helper. Input
/// forests remain separate, including when an input is forwarded or replaced.
fn allocates(summary: &crate::resource::memory::allocations::AllocationSummary) -> bool {
    use crate::resource::memory::allocations::ReturnedOwner;
    fn fresh(owner: &ReturnedOwner) -> bool {
        match owner {
            ReturnedOwner::Input { children, replacement, addition, .. } => {
                replacement.is_some() || addition.is_some() || children.values().any(fresh)
            }
            ReturnedOwner::Node { allocation, children, elements } => {
                allocation
                    .as_ref()
                    .is_some_and(|allocation| contracts::constant(&allocation.amount) != Some(0))
                    || elements.is_some()
                    || children.values().any(fresh)
            }
            ReturnedOwner::Replaced { .. } => true,
        }
    }
    !summary.retained.is_empty()
        || !summary.children.is_empty()
        || !summary.collections.is_empty()
        || summary.returned.as_ref().is_some_and(fresh)
}
