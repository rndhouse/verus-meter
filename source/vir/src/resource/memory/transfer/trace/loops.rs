//! Compose one checked iteration over disjoint persistent ownership roles.
//! Building, consumption, and transfer use the same region transitions.
//! Unsupported dependencies reject the summary rather than inventing footprints.

use super::*;
use crate::resource::memory::loops::Loop;

mod composition;

/// One iteration's disjoint roles and whole-child transfer edges. Applying this
/// graph to physical forests or original-input regions uses the same trip count.
struct Iteration {
    /// Checked transition and entry forest for each persistent collection.
    roles: Vec<(Effect, Node)>,
    /// Append role to pop role; each extracted child is consumed at most once.
    transfers: HashMap<usize, usize>,
    /// Nonnegative number of completed iterations.
    count: Expr,
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
        let mut roles = Vec::new();
        let composed = composition::compose(persistent);
        for effect in composition::blocks(span, composed, &tokens, &binder, self.layouts)? {
            let (location, typ) = match &effect {
                Effect::TransferBlock { location, typ, .. }
                | Effect::AppendBlock { location, typ, .. }
                | Effect::PopBlock { location, typ, .. }
                | Effect::Identity { location, typ } => (location, typ),
                _ => return None,
            };
            if location.1.iter().any(|slot| matches!(slot, OwnerSlot::Element(_))) {
                return None;
            }
            // A transition acts on one disjoint role, independently of child layout.
            if roles.iter().any(|(other, _): &(Effect, Node)| {
                let other = other.location().unwrap();
                other.0 == location.0
                    && (other.1.starts_with(&location.1) || location.1.starts_with(&other.1))
            }) {
                return None;
            }
            let after = std::mem::replace(&mut self.state, before.clone());
            let node = self.get(span, location, typ)?;
            self.state = after;
            roles.push((effect, node));
        }
        if roles.is_empty() {
            return None;
        }
        if bound_effects.iter().any(|effect| {
            !matches!(effect, Effect::Read(name)
            if roles.iter().all(|(effect, _)| effect.root() != name))
        }) {
            return None;
        }
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
        } else {
            let checked::Operation::Length { receiver } =
                self.checked.operations.get(&left.span.id)?.clone()
            else {
                return None;
            };
            let tested = self.checked_location(&receiver)?;
            if !roles.iter().any(|(effect, _)| {
                matches!(effect, Effect::PopBlock { location, amount, .. }
                    if location.0 == tested.0 && location.1 == tested.1 && contracts::constant(amount) == Some(1))
            }) {
                return None;
            }
        }
        let transfers = transfer_edges(&roles)?;
        let iteration = Iteration { roles, transfers, count };
        let Iteration { roles, transfers, count } = &iteration;
        let regions = &record.regions;
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
        // Restoring an entry forest conserves its local child charges as well
        // as its physical descriptors. This remains a proved invariant, never
        // an assumption justified solely by summary normalization.
        for (effect, _) in roles {
            if let Effect::Identity { location, .. } = effect {
                let role = (location.0.clone(), location.1.clone());
                if let Some(transfer) = record.transfer(&role, &role) {
                    self.loop_transfers.entry(span.id).or_default().push(transfer);
                }
            }
        }
        for (effect, _) in roles {
            if let Effect::AppendBlock { location, memory, .. } = effect {
                let mut valid = true;
                let _ = crate::ast_visitor::expr_visitor_check(memory, &mut |_, value| {
                    if let ExprX::Var(name) = &value.x {
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
        self.used.insert((checked::Kind::Loop, span.id));
        self.state = before;
        if let Some(counter) = counter {
            self.state.values.insert(counter, Value::Scalar(contracts::maximum(span, start, end)));
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
                Effect::AppendBlock { memory, length: width, minima, element, grow, .. } => {
                    let added = composition::tile(
                        span,
                        memory.clone(),
                        width.clone(),
                        count.clone(),
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
            if depth == 0 {
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
                    Effect::AppendBlock { memory, length, minima, element, grow, .. } => {
                        Some(Effect::AppendBlock {
                            location: location.clone(),
                            typ: initial.typ.clone(),
                            memory: composition::tile(
                                span,
                                memory.clone(),
                                length.clone(),
                                count.clone(),
                                expr::integer(span, 0),
                            ),
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
            if let Some(region) = regions
                .iter()
                .find(|region| region.location.0 == location.0 && region.location.1 == location.1)
            {
                let remaining = self.loop_region(span, index, &iteration, regions, region)?;
                self.regions.insert(region.exit, remaining);
            }
        }
        if regions.iter().any(|region| !self.regions.contains_key(&region.exit)) {
            return None;
        }
        // A containing iteration must see observations used by this loop's
        // count; it cannot repeat a count that depends on another changing role.
        self.effects.extend(bound_effects);
        Some(Value::Unit)
    }

    /// Original lifetime regions exclude all allocations created in this frame.
    /// Apply the same graph and index map used for complete physical forests.
    fn loop_region(
        &self,
        span: &Span,
        index: usize,
        iteration: &Iteration,
        regions: &[crate::resource::memory::loops::Region],
        region: &crate::resource::memory::loops::Region,
    ) -> Option<Expr> {
        let Iteration { roles, transfers, count } = iteration;
        let (effect, initial) = &roles[index];
        let original = region
            .entry
            .map(|id| self.regions.get(&id).cloned())
            .unwrap_or_else(|| Some(expr::empty(span, expr::record_type())))?;
        let remaining = match effect {
            Effect::Identity { .. } | Effect::AppendBlock { .. } => original,
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
                    take(span, original, length),
                )
            }
            Effect::TransferBlock { amount, .. } => {
                let moved = contracts::multiply(span, amount.clone(), count.clone());
                let source = transfers.get(&index)?;
                let source_location = roles[*source].0.location()?;
                let source_region = regions.iter().find(|r| {
                    r.location.0 == source_location.0 && r.location.1 == source_location.1
                })?;
                let source_memory = self.regions.get(&source_region.entry?)?.clone();
                expr::add(
                    span,
                    original,
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
fn transfer_edges(roles: &[(Effect, Node)]) -> Option<HashMap<usize, usize>> {
    let mut transfers = HashMap::new();
    let mut consumed = HashSet::new();
    for (index, (effect, _)) in roles.iter().enumerate() {
        if let Effect::TransferBlock { source, flows, .. } = effect {
            let source = roles.iter().position(|(effect, _)| {
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
    if roles.iter().enumerate().any(|(index, (effect, _))| {
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
