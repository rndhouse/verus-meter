//! Ordered iteration over an evolving ownership forest.
//!
//! Unlike disjoint range composition, a transition reads the result of every
//! previous visit. Runtime paths and removal reindexing therefore reuse the
//! straight-line forest algebra without assuming that selected children differ.

use super::*;

impl Trace<'_> {
    /// Build a recurrence from the checked body. Complete physical roots and
    /// original lifetime regions occupy separate slots in one specification
    /// forest, allowing transfers between roots without losing their provenance.
    pub(super) fn indexed_loop(&mut self, record: &Loop) -> Option<Value> {
        let span = &record.span;
        let control = record.control.as_ref()?;
        let counter = control.counter().cloned();
        if counter.is_none()
            && !matches!(
                self.checked.operations.get(&control.bounds().0.span.id),
                Some(checked::Operation::Length { .. })
            )
        {
            return None;
        }
        let (left, right) = control.bounds();
        let before = self.state.clone();
        if record.writes().any(|name| {
            before.values.contains_key(name)
                && !matches!(before.values[name], Value::Owner(_))
                && Some(name) != counter.as_ref()
        }) {
            return None;
        }
        let effect_start = self.effects.len();
        let start = self.scalar(left)?;
        let end = self.scalar(right)?;
        let count_effects = self.effects.split_off(effect_start);
        let count = contracts::maximum(
            span,
            expr::integer(span, 0),
            contracts::subtract(
                span,
                if counter.is_some() { end.clone() } else { start.clone() },
                if counter.is_some() { start.clone() } else { end.clone() },
            ),
        );
        let ordinal = fresh(span, "iteration_ordinal", int_typ());
        let state = fresh(span, "iteration_state", expr::memory_type());
        let ExprX::Var(ordinal_name) = &ordinal.x else { unreachable!() };
        let ExprX::Var(state_name) = &state.x else { unreachable!() };
        let binder = fresh(span, "iteration_counter", left.typ.clone());
        let ExprX::Var(binder_name) = &binder.x else { unreachable!() };
        let mut roots: Vec<_> = before
            .values
            .iter()
            .filter_map(|(name, value)| {
                if let Value::Owner(node) = value {
                    Some((name.clone(), node.clone()))
                } else {
                    None
                }
            })
            .collect();
        roots.sort_by(|(a, _), (b, _)| a.cmp(b));
        if roots.is_empty() {
            return None;
        }
        let mut initial = expr::empty(span, expr::record_type());
        for (slot, (name, node)) in roots.iter().enumerate() {
            initial = insert(span, initial, slot, node.memory.clone());
            self.state.values.insert(
                name.clone(),
                Value::Owner(Node { memory: select(span, state.clone(), slot), ..node.clone() }),
            );
        }
        for (offset, region) in record.regions.iter().enumerate() {
            let slot = roots.len() + offset;
            let memory = region
                .entry
                .map(|id| self.regions.get(&id).cloned())
                .unwrap_or_else(|| Some(expr::empty(span, expr::record_type())))?;
            initial = insert(span, initial, slot, memory);
            if let Some(id) = region.entry {
                self.regions.insert(id, select(span, state.clone(), slot));
            }
        }
        if let Some(counter) = &counter {
            self.state.values.insert(counter.clone(), Value::Scalar(binder.clone()));
        }
        let symbolic_end = self.scalar(right)?;
        let symbolic_start = self.scalar(left)?;
        self.effects.truncate(effect_start);
        let outer_tokens = self.loop_tokens.replace(HashSet::new());
        // Every owner is already parametric over the accumulator. Pop needs no
        // separate selection token, while allocation observations remain active.
        let outer_roots = self.loop_roots.replace(HashSet::new());
        let outer_inputs = std::mem::take(&mut self.loop_inputs);
        let outer_allocations = std::mem::take(&mut self.loop_allocations);
        let outer_calls = std::mem::take(&mut self.loop_calls);
        let outer_ceiling =
            std::mem::replace(&mut self.loop_size_ceiling, record.size_ceiling.unwrap_or(0));
        self.value(&record.body)?;
        if let Some(counter) = &counter {
            let Value::Scalar(next) = self.state.values.get(counter)? else { return None };
            let ExprX::Binary(BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow)), a, b) =
                &next.x
            else {
                return None;
            };
            if !matches!(&a.x, ExprX::Var(name) if name == binder_name)
                || contracts::constant(b) != Some(1)
            {
                return None;
            }
        } else {
            let next = self.scalar(left)?;
            let expected = contracts::maximum(
                span,
                expr::integer(span, 0),
                contracts::subtract(span, symbolic_start, expr::integer(span, 1)),
            );
            if !simplify::same_expression(&next, &simplify::simplify(&expected)) {
                return None;
            }
        }
        // Compare parametric observations, not merely their first-visit values:
        // coincidental equality at entry does not establish a stable trip count.
        let after_end = self.scalar(right)?;
        if !simplify::same_expression(&after_end, &symbolic_end) {
            return None;
        }
        let effects = self.effects.split_off(effect_start);
        let persistent: Vec<_> = effects
            .iter()
            .filter(|effect| before.values.contains_key(effect.root()))
            .cloned()
            .collect();
        // Keep the existing predicate boundary. A recurrence changes path
        // semantics, not which payload-dependent decisions are admitted.
        guards::partition(
            span,
            &persistent,
            binder_name,
            if counter.is_some() { start.clone() } else { expr::integer(span, 0) },
            count.clone(),
            &self.proof_values,
        )?;
        // Ceilings are proof candidates only: each operation must establish
        // its actual extent, and the complete body must prove charge induction.
        let observations: HashSet<_> = [state_name.clone()].into();
        let mut added = expr::integer(span, 0);
        for (site, actual, candidate) in &self.loop_allocations {
            let candidate = simplify::allocation_bound(
                candidate,
                &observations,
                record.size_ceiling.unwrap_or(0),
            );
            let bound = self.extent_bound(&candidate, binder_name, record, &start, &count)?;
            self.allocation_checks
                .push((site.clone(), mk_ineq(site, actual, &bound, InequalityOp::Le)));
            added = contracts::add(span, added, bound);
        }
        // An unreachable body needs no retained headroom at loop entry.
        // Its ordinary operation checks and back-edge obligations are vacuous.
        if contracts::constant(&count) == Some(0) {
            added = expr::integer(span, 0);
        }
        self.loop_repetitions.insert(span.id, simplify::simplify(&added));
        for (site, actual, candidate) in &self.loop_calls {
            let candidate = simplify::allocation_bound(
                candidate,
                &observations,
                record.size_ceiling.unwrap_or(0),
            );
            let bound = self.extent_bound(&candidate, binder_name, record, &start, &count)?;
            self.allocation_checks
                .push((site.clone(), mk_ineq(site, actual, &bound, InequalityOp::Le)));
            self.loop_scratch
                .entry(span.id)
                .and_modify(|old| {
                    *old = contracts::maximum(span, old.clone(), bound.clone());
                })
                .or_insert(bound);
        }
        let replacements = HashMap::from([(
            binder_name.clone(),
            contracts::add(span, start.clone(), ordinal.clone()),
        )]);
        let mut body = expr::empty(span, expr::record_type());
        let mut results = Vec::new();
        for (slot, (name, initial_node)) in roots.iter().enumerate() {
            let Value::Owner(node) = self.state.values.get(name)? else { return None };
            body = insert(span, body, slot, substitute(&node.memory, &replacements));
            let mut minima = initial_node.minima.clone();
            join_minima(span, &mut minima, &node.minima);
            for floor in minima.values_mut() {
                if !independent(&floor.capacity, binder_name)
                    || !independent(&floor.capacity, state_name)
                {
                    floor.capacity = expr::integer(span, 0);
                }
            }
            let changed =
                !simplify::same_expression(&node.memory, &select(span, state.clone(), slot));
            results.push((minima, changed));
        }
        for (offset, region) in record.regions.iter().enumerate() {
            body = insert(
                span,
                body,
                roots.len() + offset,
                substitute(self.regions.get(&region.body)?, &replacements),
            );
        }
        let builder = SpannedTyped::new(
            span,
            &Arc::new(TypX::SpecFn(
                Arc::new(vec![int_typ(), expr::memory_type()]),
                expr::memory_type(),
            )),
            ExprX::Closure(
                Arc::new(vec![
                    Arc::new(VarBinderX { name: ordinal_name.clone(), a: int_typ() }),
                    Arc::new(VarBinderX { name: state_name.clone(), a: expr::memory_type() }),
                ]),
                body,
            ),
        );
        let completed =
            simplify::finite_iteration(span, builder, initial.clone(), count, record.size_ceiling);
        // Earlier lifetime IDs remain first-visit peak witnesses. Exit IDs use
        // the full recurrence, including shifted or repeatedly selected children.
        let first =
            HashMap::from([(state_name.clone(), initial), (binder_name.clone(), start.clone())]);
        for memory in self.regions.values_mut() {
            *memory = substitute(memory, &first);
        }
        for (offset, region) in record.regions.iter().enumerate() {
            self.regions.insert(
                region.exit,
                simplify::simplify(&select(span, completed.clone(), roots.len() + offset)),
            );
        }
        self.state = before;
        for ((slot, (name, node)), (minima, changed)) in roots.into_iter().enumerate().zip(results)
        {
            if !changed {
                continue;
            }
            self.state.values.insert(
                name.clone(),
                Value::Owner(Node {
                    origin: None,
                    memory: simplify::simplify(&select(span, completed.clone(), slot)),
                    minima,
                    ..node
                }),
            );
            self.state.written.insert(name.clone());
            self.effects.push(Effect::Mutation(name));
        }
        if let Some(counter) = counter {
            self.state.values.insert(counter, Value::Scalar(contracts::maximum(span, start, end)));
        }
        // A containing range planner must still see the count's read roles.
        // Repeating a completed inner loop cannot freeze a changing observation.
        self.effects.extend(count_effects);
        self.loop_tokens = outer_tokens;
        self.loop_roots = outer_roots;
        self.loop_inputs = outer_inputs;
        self.loop_allocations = outer_allocations;
        self.loop_calls = outer_calls;
        self.loop_size_ceiling = outer_ceiling;
        self.used.insert((checked::Kind::Loop, span.id));
        Some(Value::Unit)
    }
}

/// Fresh bound symbols cannot collide with caller observations or nested loops.
fn fresh(span: &Span, name: &str, typ: Typ) -> Expr {
    let name = VarIdent(
        Arc::new(format!("$memory_{name}")),
        VarIdentDisambiguate::VirTemp(
            crate::resource::memory::accounting::Accounting::fresh_allocation(),
        ),
    );
    SpannedTyped::new(span, &typ, ExprX::Var(name))
}

/// Recover one physical root or original region from the shared accumulator.
fn select(span: &Span, memory: Expr, slot: usize) -> Expr {
    expr::subtree(span, memory, expr::path(span, [slot as i128]))
}

/// Pack an independent forest under a disjoint accumulator slot.
fn insert(span: &Span, memory: Expr, slot: usize, child: Expr) -> Expr {
    expr::add(span, memory, expr::prefix(span, child, expr::path(span, [slot as i128])))
}
