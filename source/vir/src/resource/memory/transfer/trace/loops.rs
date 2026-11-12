//! Compose one checked iteration over disjoint persistent ownership roles.
//! Building, consumption, and transfer use the same region transitions.
//! Unsupported dependencies reject the summary rather than inventing footprints.

use super::*;
use crate::resource::memory::loops::Loop;

mod composition;
mod guards;

/// One iteration's disjoint roles and whole-child transfer edges. Applying this
/// graph to physical forests or original-input regions uses the same trip count.
struct Iteration {
    /// Checked transition and entry forest for each persistent collection.
    roles: Vec<(Effect, Node)>,
    /// Append role to pop role; each extracted child is consumed at most once.
    transfers: HashMap<usize, usize>,
    /// Nonnegative number of completed iterations.
    count: Expr,
    /// Counter observation at the beginning of this interval.
    start: Expr,
}

fn independent(value: &Expr, name: &VarIdent) -> bool {
    let mut found = false;
    let _ = crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
        found |= matches!(&value.x, ExprX::Var(var) if var == name);
        Ok::<(), VirErr>(())
    });
    !found
}

impl Trace<'_> {
    pub(super) fn loop_value(&mut self, span: &Span) -> Option<Value> {
        let record = self.checked.loops.get(&span.id)?.clone();
        let before = self.state.clone();
        let used = self.used.clone();
        let regions = self.regions.clone();
        let tokens = self.loop_tokens.clone();
        let roots = self.loop_roots.clone();
        let inputs = self.loop_inputs.clone();
        let allocations = self.loop_allocations.clone();
        let calls = self.loop_calls.clone();
        let scratch = self.loop_scratch.clone();
        let size_ceiling = self.loop_size_ceiling;
        let checks = self.allocation_checks.len();
        let loop_transfers = self.loop_transfers.clone();
        let loop_growth = self.loop_growth.clone();
        let effects = self.effects.len();
        let depth = self.branch_depth;
        if let Some(value) = self.collection_loop(&record) {
            return Some(value);
        }
        self.state = before;
        self.regions = regions;
        self.loop_tokens = tokens;
        self.loop_roots = roots;
        self.loop_inputs = inputs;
        self.loop_allocations = allocations;
        self.loop_calls = calls;
        self.loop_scratch = scratch;
        self.loop_size_ceiling = size_ceiling;
        self.allocation_checks.truncate(checks);
        self.loop_transfers = loop_transfers;
        self.loop_growth = loop_growth;
        self.used = used;
        self.effects.truncate(effects);
        self.branch_depth = depth;
        // Read-only eligibility was classified with the body proof's record.
        if !record.read_only() {
            return None;
        }
        for value in self.state.values.values_mut() {
            if matches!(value, Value::Scalar(_)) {
                *value = Value::Unknown;
            }
        }
        self.used.insert((checked::Kind::Loop, span.id));
        Some(Value::Unit)
    }

    fn collection_loop(&mut self, record: &Loop) -> Option<Value> {
        let span = &record.span;
        let control = record.control.as_ref()?;
        let (left, right) = control.bounds();
        let counter = control.counter().cloned();
        let counted = counter.is_some();
        let before = self.state.clone();
        let start = self.scalar(left)?;
        if record.writes().any(|name| {
            before.values.contains_key(name)
                && !matches!(before.values[name], Value::Owner(_))
                && Some(name) != counter.as_ref()
        }) {
            return None;
        }
        let binder = VarIdent(
            Arc::new("$memory_transfer_iteration".into()),
            VarIdentDisambiguate::VirTemp(span.id),
        );
        if let Some(counter) = &counter {
            self.state.values.insert(
                counter.clone(),
                Value::Scalar(SpannedTyped::new(span, &left.typ, ExprX::Var(binder.clone()))),
            );
        }
        let bound_start = self.effects.len();
        let end = self.scalar(right)?;
        let bound_effects = self.effects.split_off(bound_start);
        if !independent(&end, &binder) {
            return None;
        }
        let count = contracts::maximum(
            span,
            expr::integer(span, 0),
            contracts::subtract(
                span,
                if counted { end.clone() } else { start.clone() },
                if counted { start.clone() } else { end.clone() },
            ),
        );
        let effect_start = self.effects.len();
        let depth = self.branch_depth;
        self.branch_depth = 0;
        let outer_inputs = std::mem::take(&mut self.loop_inputs);
        let outer_allocations = std::mem::take(&mut self.loop_allocations);
        let outer_calls = std::mem::take(&mut self.loop_calls);
        let outer_ceiling =
            std::mem::replace(&mut self.loop_size_ceiling, record.size_ceiling.unwrap_or(0));
        let outer_tokens = self.loop_tokens.replace(HashSet::new());
        let outer_roots = self.loop_roots.replace(before.values.keys().cloned().collect());
        self.value(&record.body)?;
        let tokens = std::mem::replace(&mut self.loop_tokens, outer_tokens).unwrap();
        self.loop_roots = outer_roots;
        self.branch_depth = depth;
        let effects = self.effects.split_off(effect_start);
        let persistent: Vec<_> = effects
            .into_iter()
            .filter(|effect| before.values.contains_key(effect.root()))
            .collect();
        if counted {
            let Value::Scalar(next) = self.state.values.get(counter.as_ref()?)? else {
                return None;
            };
            let ExprX::Binary(BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow)), a, b) =
                &next.x
            else {
                return None;
            };
            if !matches!(&a.x, ExprX::Var(name) if *name == binder)
                || contracts::constant(b) != Some(1)
            {
                return None;
            }
        }
        let programs = guards::partition(
            span,
            &persistent,
            &binder,
            if counted { start.clone() } else { expr::integer(span, 0) },
            count,
            &self.proof_values,
        )?;
        let mut blocks = Vec::new();
        for interval in programs {
            let mut phase = Vec::new();
            for program in interval {
                let effects = composition::compose(program.effects);
                let effects =
                    composition::blocks(span, effects.clone(), &tokens, &binder, self.layouts)
                        .filter(|effects| transfer_edges(effects).is_some())
                        .or_else(|| {
                            composition::generators(
                                span,
                                effects,
                                &tokens,
                                &binder,
                                self.layouts,
                                &self.loop_inputs,
                            )
                        })?;
                if bound_effects.iter().any(|effect| {
                    !matches!(effect, Effect::Read(name)
                    if effects.iter().all(|effect| effect.root() != name))
                }) {
                    return None;
                }
                if !counted {
                    let checked::Operation::Length { receiver } =
                        self.checked.operations.get(&left.span.id)?.clone()
                    else {
                        return None;
                    };
                    let tested = self.checked_location(&receiver)?;
                    let progresses = effects.iter().any(|effect| match effect {
                        Effect::PopBlock { location, amount, .. } => {
                            location.0 == tested.0
                                && location.1 == tested.1
                                && contracts::constant(amount) == Some(1)
                        }
                        _ => false,
                    });
                    if !progresses {
                        return None;
                    }
                }
                phase.push((effects, program.count, program.start, program.condition));
            }
            blocks.push(phase);
        }
        // An identity frame bound is valid only if every selected program leaves
        // that role unchanged. Alternative transfers share conservation groups.
        for (effects, _, _, _) in blocks.iter().flatten() {
            for effect in effects {
                if let Effect::Identity { location, .. } = effect {
                    if blocks.iter().flatten().flat_map(|(effects, _, _, _)| effects).all(|other| {
                        matches!(other, Effect::Identity { .. })
                            || other
                                .location()
                                .is_none_or(|other| other.0 != location.0 || other.1 != location.1)
                    }) {
                        let role = (location.0.clone(), location.1.clone());
                        if let Some(transfer) = record.transfer(&role, &role) {
                            self.loop_transfers.entry(span.id).or_default().push(transfer);
                        }
                    }
                }
            }
        }
        self.state = before;
        let mut original = record
            .regions
            .iter()
            .map(|region| {
                let memory = match region.entry {
                    Some(id) => self.regions.get(&id)?.clone(),
                    None => expr::empty(span, expr::record_type()),
                };
                Some((region.location.clone(), memory))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        for phase in blocks {
            let entry = self.state.clone();
            let entry_original = original.clone();
            let mut joined = entry.clone();
            let mut joined_original = entry_original.clone();
            let mut completed = Vec::new();
            for (effects, count, interval_start, condition) in phase {
                self.state = entry.clone();
                let mut selected_original = entry_original.clone();
                let first_effect = self.effects.len();
                self.apply_program(record, effects, count, interval_start, &mut selected_original)?;
                let effects = self.effects.split_off(first_effect);
                completed.extend(effects.into_iter().map(|effect| {
                    if matches!(condition.x, ExprX::Const(Constant::Bool(true))) {
                        effect
                    } else {
                        Effect::Guarded {
                            condition: condition.clone(),
                            selected: true,
                            effect: Box::new(effect),
                        }
                    }
                }));
                joined = Self::join_state(span, condition.clone(), self.state.clone(), joined)?;
                for (role, memory) in selected_original {
                    joined_original.insert(
                        role.clone(),
                        choice(span, condition.clone(), memory, joined_original[&role].clone()),
                    );
                }
            }
            self.state = joined;
            original = joined_original;
            self.effects.extend(completed);
        }
        // Intermediate identities are first-iteration peak witnesses, just as
        // for unconditional loops. Their total original storage cannot increase
        // on later visits. Loop exits instead retain the complete interval map.
        let mut replacements = HashMap::from([(binder.clone(), start.clone())]);
        for (token, selection) in &self.loop_inputs {
            replacements.insert(token.clone(), selection.memory.clone());
            replacements.insert(selection.presence.0.clone(), selection.presence.1.clone());
            if let Some((token, witness)) = &selection.original {
                replacements.insert(token.clone(), witness.clone());
            }
        }
        // A nested extraction witness can refer to earlier tokens. Resolve them
        // in order until each first-iteration region is closed over caller inputs.
        for _ in 0..replacements.len() {
            let previous = replacements.clone();
            for witness in replacements.values_mut() {
                *witness = substitute(witness, &previous);
            }
        }
        for memory in self.regions.values_mut() {
            *memory = substitute(memory, &replacements);
        }
        for region in &record.regions {
            self.regions.insert(region.exit, original.get(&region.location)?.clone());
        }
        self.loop_inputs = outer_inputs;
        self.loop_allocations = outer_allocations;
        self.loop_calls = outer_calls;
        self.loop_size_ceiling = outer_ceiling;
        self.used.insert((checked::Kind::Loop, span.id));
        if let Some(counter) = counter {
            self.state.values.insert(counter, Value::Scalar(contracts::maximum(span, start, end)));
        }
        // A containing iteration must see observations used by this loop's
        // count; it cannot repeat a count that depends on another changing role.
        self.effects.extend(bound_effects);
        Some(Value::Unit)
    }

    /// Apply one branch-selected interval using the same forest graph for full
    /// storage and original lifetimes. Later intervals start from these results.
    fn apply_program(
        &mut self,
        record: &Loop,
        effects: Vec<Effect>,
        count: Expr,
        start: Expr,
        original: &mut BTreeMap<crate::resource::memory::paths::LocalPath, Expr>,
    ) -> Option<()> {
        let span = &record.span;
        let mut roles = Vec::new();
        for effect in effects {
            let location = effect.location()?;
            if location.1.iter().any(|slot| matches!(slot, OwnerSlot::Element(_))) {
                return None;
            }
            if roles.iter().any(|(other, _): &(Effect, Node)| {
                let other = other.location().unwrap();
                other.0 == location.0
                    && (other.1.starts_with(&location.1) || location.1.starts_with(&other.1))
            }) {
                return None;
            }
            let typ = match &effect {
                Effect::TransferBlock { typ, .. }
                | Effect::AppendBlock { typ, .. }
                | Effect::GenerateBlock { typ, .. }
                | Effect::PopBlock { typ, .. }
                | Effect::Identity { typ, .. } => typ,
                _ => return None,
            };
            let node = self.get(span, location, typ)?;
            roles.push((effect, node));
        }
        let entry_original = original.clone();
        let transfers =
            transfer_edges(&roles.iter().map(|(effect, _)| effect.clone()).collect::<Vec<_>>())?;
        let iteration = Iteration { roles, transfers, count, start };
        let Iteration { roles, transfers, count, start } = &iteration;
        // Return structural relationships. The shared record resolves endpoints,
        // and the body proof layer constructs conservation inequalities later.
        for (target, source) in transfers {
            let source = roles[*source].0.location()?;
            let target = roles[*target].0.location()?;
            let transfer = record.transfer(
                &(source.0.clone(), source.1.clone()),
                &(target.0.clone(), target.1.clone()),
            )?;
            self.loop_transfers.entry(span.id).or_default().push(transfer);
        }
        for (effect, _) in roles {
            if let Effect::GenerateBlock { location, inputs, .. } = effect {
                for (_, source, _) in inputs {
                    let mut transfer = record.transfer(
                        &(source.0.clone(), source.1.clone()),
                        &(location.0.clone(), location.1.clone()),
                    )?;
                    if let Effect::GenerateBlock { binder, .. } = effect {
                        let mut additional = expr::integer(span, 0);
                        for (site, actual, candidate) in &self.loop_allocations {
                            let bound =
                                self.extent_bound(candidate, binder, record, start, count)?;
                            self.allocation_checks.push((
                                site.clone(),
                                mk_ineq(site, actual, &bound, InequalityOp::Le),
                            ));
                            additional = contracts::add(span, additional, bound);
                        }
                        for (site, actual, candidate) in &self.loop_calls {
                            let bound =
                                self.extent_bound(candidate, binder, record, start, count)?;
                            self.allocation_checks.push((
                                site.clone(),
                                mk_ineq(site, actual, &bound, InequalityOp::Le),
                            ));
                            self.loop_scratch
                                .entry(span.id)
                                .and_modify(|old| {
                                    *old = contracts::maximum(span, old.clone(), bound.clone());
                                })
                                .or_insert(bound);
                        }
                        transfer.additional = Some(simplify::simplify(&additional));
                    }
                    self.loop_transfers.entry(span.id).or_default().push(transfer);
                }
            }
        }
        for (effect, _) in roles {
            let envelope = match effect {
                Effect::AppendBlock { location, memory, .. } => Some((location, memory.clone())),
                Effect::GenerateBlock { location, memory, binder, inputs, .. }
                    if inputs.is_empty() =>
                {
                    Some((
                        location,
                        substitute(
                            memory,
                            &HashMap::from([(
                                binder.clone(),
                                record
                                    .size_ceiling
                                    .map(|n| contracts::literal(span, n))
                                    .unwrap_or_else(|| {
                                        contracts::add(span, start.clone(), count.clone())
                                    }),
                            )]),
                        ),
                    ))
                }
                _ => None,
            };
            if let Some((location, memory)) = envelope {
                let mut valid = true;
                let _ = crate::ast_visitor::expr_visitor_check(&memory, &mut |scope, value| {
                    if let ExprX::Var(name) = &value.x {
                        if scope.contains_key(name) {
                            return Ok::<(), VirErr>(());
                        }
                        valid &= self.proof_values.contains_key(name);
                    }
                    Ok::<(), VirErr>(())
                });
                if !valid {
                    return None;
                }
                let amount = simplify::simplify(&substitute(
                    &expr::cost(span, memory.clone(), expr::integer(span, 0)),
                    &self.proof_values,
                ));
                self.loop_growth
                    .entry(span.id)
                    .or_default()
                    .push(((location.0.clone(), location.1.clone()), amount));
            }
        }
        let flows: HashMap<_, _> = transfers
            .values()
            .map(|source| {
                (
                    *source,
                    VarIdent(
                        Arc::new("$memory_iteration_range".into()),
                        VarIdentDisambiguate::VirTemp(
                            crate::resource::memory::accounting::Accounting::fresh_allocation(),
                        ),
                    ),
                )
            })
            .collect();
        for (index, (effect, initial)) in roles.iter().enumerate() {
            let location = effect.location()?;
            let length = property(span, initial.memory.clone(), "length");
            let capacity = property(span, initial.memory.clone(), "capacity");
            let bytes = property(span, initial.memory.clone(), "bytes");
            let mut node = initial.clone();
            if !matches!(effect, Effect::Identity { .. }) {
                node.origin = None;
            }
            match effect {
                Effect::Identity { .. } => {}
                Effect::PopBlock { amount, .. } => {
                    let removed = contracts::multiply(span, count.clone(), amount.clone());
                    let final_length = contracts::maximum(
                        span,
                        expr::integer(span, 0),
                        contracts::subtract(span, length, removed),
                    );
                    node.memory = with_root(
                        span,
                        take(span, node.memory, final_length.clone()),
                        bytes,
                        capacity,
                        final_length,
                        self.layouts.owning_elements(&node.typ),
                    );
                }
                Effect::AppendBlock { memory, length: width, minima, element, grow, .. }
                | Effect::GenerateBlock { memory, length: width, minima, element, grow, .. } => {
                    let added = if matches!(effect, Effect::GenerateBlock { .. }) {
                        self.generated(
                            span,
                            effect,
                            &iteration,
                            &entry_original,
                            false,
                            length.clone(),
                        )?
                    } else {
                        composition::tile(
                            span,
                            memory.clone(),
                            width.clone(),
                            count.clone(),
                            length.clone(),
                        )
                    };
                    node.memory = expr::add(span, node.memory, added);
                    let floors = minima
                        .iter()
                        .map(|(path, floor)| {
                            (
                                std::iter::once(Step::Repeated)
                                    .chain(path.iter().cloned())
                                    .collect(),
                                floor.clone(),
                            )
                        })
                        .collect();
                    join_minima(span, &mut node.minima, &floors);
                    let final_length = contracts::add(
                        span,
                        length,
                        contracts::multiply(span, width.clone(), count.clone()),
                    );
                    node.memory = append_root(
                        span,
                        node.memory,
                        capacity,
                        bytes,
                        final_length,
                        *element,
                        *grow,
                        self.layouts.owning_elements(&node.typ),
                    );
                }
                Effect::TransferBlock { amount, minima, element, grow, .. } => {
                    let source = &roles[*transfers.get(&index)?].1;
                    let moved = contracts::multiply(span, amount.clone(), count.clone());
                    let added = reverse_range(
                        span,
                        source.memory.clone(),
                        property(span, source.memory.clone(), "length"),
                        moved.clone(),
                        length.clone(),
                    );
                    node.memory = expr::add(span, node.memory, added);
                    let floors = minima
                        .iter()
                        .map(|(path, floor)| {
                            (
                                std::iter::once(Step::Repeated)
                                    .chain(path.iter().cloned())
                                    .collect(),
                                floor.clone(),
                            )
                        })
                        .collect();
                    join_minima(span, &mut node.minima, &floors);
                    let final_length = contracts::add(span, length, moved);
                    node.memory = append_root(
                        span,
                        node.memory,
                        capacity,
                        bytes,
                        final_length,
                        *element,
                        *grow,
                        self.layouts.owning_elements(&node.typ),
                    );
                }
                _ => return None,
            }
            self.set(span, location, node)?;
            if self.branch_depth == 0 {
                let completed = match effect {
                    Effect::Identity { .. } => Some(effect.clone()),
                    Effect::PopBlock { amount, .. } => Some(Effect::PopBlock {
                        location: location.clone(),
                        typ: initial.typ.clone(),
                        amount: simplify::simplify(&contracts::multiply(
                            span,
                            amount.clone(),
                            count.clone(),
                        )),
                        flows: flows.get(&index).map(|flow| vec![flow.clone()]),
                    }),
                    Effect::TransferBlock { source, amount, minima, element, grow, .. } => {
                        Some(Effect::TransferBlock {
                            location: location.clone(),
                            source: source.clone(),
                            typ: initial.typ.clone(),
                            amount: simplify::simplify(&contracts::multiply(
                                span,
                                amount.clone(),
                                count.clone(),
                            )),
                            flows: vec![flows[transfers.get(&index)?].clone()],
                            minima: minima.clone(),
                            element: *element,
                            grow: *grow,
                        })
                    }
                    Effect::AppendBlock { memory, length, minima, element, grow, .. }
                    | Effect::GenerateBlock { memory, length, minima, element, grow, .. } => {
                        Some(Effect::AppendBlock {
                            location: location.clone(),
                            typ: initial.typ.clone(),
                            memory: if matches!(effect, Effect::GenerateBlock { .. }) {
                                self.generated(
                                    span,
                                    effect,
                                    &iteration,
                                    &entry_original,
                                    false,
                                    expr::integer(span, 0),
                                )?
                            } else {
                                composition::tile(
                                    span,
                                    memory.clone(),
                                    length.clone(),
                                    count.clone(),
                                    expr::integer(span, 0),
                                )
                            },
                            length: simplify::simplify(&contracts::multiply(
                                span,
                                length.clone(),
                                count.clone(),
                            )),
                            minima: minima.clone(),
                            element: *element,
                            grow: *grow,
                        })
                    }
                    _ => None,
                };
                if let Some(completed) = completed {
                    self.effects.pop();
                    self.effects.push(completed);
                }
            }
            if let std::collections::btree_map::Entry::Occupied(mut entry) =
                original.entry((location.0.clone(), location.1.clone()))
            {
                let remaining = self.loop_region(span, index, &iteration, &entry_original)?;
                entry.insert(remaining);
            }
        }
        Some(())
    }

    /// Close a proof ceiling over immutable body observations. Actual allocation
    /// and call extents must prove this bound at their executable operation.
    fn extent_bound(
        &self,
        candidate: &Expr,
        binder: &VarIdent,
        record: &Loop,
        start: &Expr,
        count: &Expr,
    ) -> Option<Expr> {
        let mut values = self.proof_values.clone();
        values.insert(
            binder.clone(),
            record
                .size_ceiling
                .map(|n| contracts::literal(&record.span, n))
                .unwrap_or_else(|| contracts::add(&record.span, start.clone(), count.clone())),
        );
        let candidate = simplify::allocation_bound(
            candidate,
            &self.loop_inputs.keys().cloned().collect(),
            record.size_ceiling.unwrap_or(0),
        );
        let bound = substitute(&candidate, &values);
        crate::ast_visitor::expr_visitor_check(&bound, &mut |scope, value| {
            if matches!(&value.x, ExprX::Var(name) if !scope.contains_key(name)
                && !self.proof_values.values().any(|value| matches!(&value.x, ExprX::Var(var) if var == name))) { Err(()) } else { Ok(()) }
        }).ok()?;
        Some(bound)
    }

    /// Close the iteration body over each selected source child. The physical
    /// source supplies geometry even when its original-input region is empty.
    fn generated(
        &self,
        span: &Span,
        effect: &Effect,
        iteration: &Iteration,
        regions: &BTreeMap<crate::resource::memory::paths::LocalPath, Expr>,
        original: bool,
        base: Expr,
    ) -> Option<Expr> {
        let Effect::GenerateBlock {
            memory, original: input_memory, length, binder, inputs, ..
        } = effect
        else {
            return None;
        };
        let name = VarIdent(
            Arc::new("$memory_generated_index".into()),
            VarIdentDisambiguate::VirTemp(
                crate::resource::memory::accounting::Accounting::fresh_allocation(),
            ),
        );
        let index = SpannedTyped::new(span, &int_typ(), ExprX::Var(name.clone()));
        let mut replacements = HashMap::from([(
            binder.clone(),
            contracts::add(span, iteration.start.clone(), index.clone()),
        )]);
        for (token, source, offset) in inputs {
            let (effect, initial) = iteration.roles.iter().find(|(effect, _)| {
                effect
                    .location()
                    .is_some_and(|location| location.0 == source.0 && location.1 == source.1)
            })?;
            let Effect::PopBlock { amount, .. } = effect else {
                return None;
            };
            let selected = contracts::subtract(
                span,
                contracts::subtract(
                    span,
                    property(span, initial.memory.clone(), "length"),
                    contracts::multiply(span, amount.clone(), index.clone()),
                ),
                contracts::add(span, offset.clone(), expr::integer(span, 1)),
            );
            let path = expr::push(span, expr::path(span, []), selected.clone());
            replacements
                .insert(token.clone(), expr::subtree(span, initial.memory.clone(), path.clone()));
            if let Some(selection) = self.loop_inputs.get(token) {
                replacements.insert(
                    selection.presence.0.clone(),
                    choice(
                        span,
                        mk_ineq(span, &expr::integer(span, 0), &selected, InequalityOp::Le),
                        expr::integer(span, 1),
                        expr::integer(span, 0),
                    ),
                );
            }
            if let Some(Selection { original: Some((original_token, _)), .. }) =
                self.loop_inputs.get(token)
            {
                let source_original = regions
                    .get(&(source.0.clone(), source.1.clone()))
                    .cloned()
                    .unwrap_or_else(|| expr::empty(span, expr::record_type()));
                replacements
                    .insert(original_token.clone(), expr::subtree(span, source_original, path));
            }
        }
        let body = substitute(if original { input_memory } else { memory }, &replacements);
        let builder = SpannedTyped::new(
            span,
            &Arc::new(TypX::SpecFn(Arc::new(vec![int_typ()]), expr::memory_type())),
            ExprX::Closure(Arc::new(vec![Arc::new(VarBinderX { name, a: int_typ() })]), body),
        );
        Some(simplify::simplify(&expr::operation(
            span,
            "generate_children",
            vec![builder, length.clone(), iteration.count.clone(), base],
            expr::memory_type(),
        )))
    }

    /// Original lifetime regions exclude all allocations created in this frame.
    /// Apply the same graph and index map used for complete physical forests.
    fn loop_region(
        &self,
        span: &Span,
        index: usize,
        iteration: &Iteration,
        regions: &BTreeMap<crate::resource::memory::paths::LocalPath, Expr>,
    ) -> Option<Expr> {
        let Iteration { roles, transfers, count, .. } = iteration;
        let (effect, initial) = &roles[index];
        let location = effect.location()?;
        let original = regions.get(&(location.0.clone(), location.1.clone()))?.clone();
        let remaining = match effect {
            Effect::Identity { .. } | Effect::AppendBlock { .. } => original.clone(),
            Effect::GenerateBlock { .. } => expr::add(
                span,
                original.clone(),
                self.generated(
                    span,
                    effect,
                    iteration,
                    regions,
                    true,
                    property(span, initial.memory.clone(), "length"),
                )?,
            ),
            Effect::PopBlock { amount, .. } => {
                let removed = contracts::multiply(span, count.clone(), amount.clone());
                let length = contracts::maximum(
                    span,
                    expr::integer(span, 0),
                    contracts::subtract(
                        span,
                        property(span, initial.memory.clone(), "length"),
                        removed,
                    ),
                );
                expr::add(
                    span,
                    expr::operation(
                        span,
                        "nonruntime",
                        vec![original.clone()],
                        expr::memory_type(),
                    ),
                    take(span, original.clone(), length),
                )
            }
            Effect::TransferBlock { amount, .. } => {
                let moved = contracts::multiply(span, amount.clone(), count.clone());
                let source = transfers.get(&index)?;
                let source_location = roles[*source].0.location()?;
                let source_memory = regions
                    .get(&(source_location.0.clone(), source_location.1.clone()))
                    .cloned()
                    .unwrap_or_else(|| expr::empty(span, expr::record_type()));
                expr::add(
                    span,
                    original.clone(),
                    reverse_range(
                        span,
                        source_memory,
                        property(span, roles[*source].1.memory.clone(), "length"),
                        moved,
                        property(span, initial.memory.clone(), "length"),
                    ),
                )
            }
            _ => return None,
        };
        Some(simplify::simplify(&remaining))
    }
}

fn take(span: &Span, memory: Expr, length: Expr) -> Expr {
    expr::operation(span, "take_children", vec![memory, length], expr::memory_type())
}

fn reverse_range(span: &Span, memory: Expr, end: Expr, count: Expr, base: Expr) -> Expr {
    expr::operation(
        span,
        "reverse_children",
        vec![memory, contracts::subtract(span, end.clone(), count), end, base],
        expr::memory_type(),
    )
}

/// An extraction range has one destination and preserves extraction order.
/// Flow identities are created together with matching source/destination counts;
/// equality of their ordered lists proves that no child is dropped, duplicated
/// or routed through a different range when batching operations or inner loops.
fn transfer_edges(roles: &[Effect]) -> Option<HashMap<usize, usize>> {
    let mut transfers = HashMap::new();
    let mut consumed = HashSet::new();
    for (index, effect) in roles.iter().enumerate() {
        if let Effect::TransferBlock { source, flows, .. } = effect {
            let source = roles.iter().position(|effect| {
                matches!(effect,
                Effect::PopBlock { location, flows: Some(taken), .. }
                    if location.0 == source.0 && location.1 == source.1 && taken == flows)
            })?;
            if !consumed.insert(source) {
                return None;
            }
            transfers.insert(index, source);
        }
    }
    if roles.iter().enumerate().any(|(index, effect)| {
        matches!(effect, Effect::PopBlock { flows: Some(_), .. }) && !consumed.contains(&index)
    }) {
        return None;
    }
    Some(transfers)
}

/// Buffer replacement depends on completed logical length, independently of
/// whether the appended children came from one operation, a helper or a loop.
fn append_root(
    span: &Span,
    memory: Expr,
    capacity: Expr,
    bytes: Expr,
    length: Expr,
    element: u64,
    grow: bool,
    owns_children: bool,
) -> Expr {
    let (capacity, retained) = if grow {
        let replacement = contracts::multiply(
            span,
            contracts::literal(span, element),
            growth::grown_capacity(span, length.clone(), element),
        );
        let retained = choice(
            span,
            mk_ineq(span, &length, &capacity, InequalityOp::Le),
            bytes.clone(),
            contracts::maximum(span, bytes, replacement),
        );
        (contracts::maximum(span, capacity, length.clone()), retained)
    } else {
        (capacity, bytes)
    };
    with_root(span, memory, retained, capacity, length, owns_children)
}
