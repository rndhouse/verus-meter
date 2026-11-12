//! Checked scalar translations and comparison gaps shared by both loop planners.

use super::*;
use crate::resource::memory::loops::progress::{count, difference};

/// A visit ordinal binds every changing scalar; completed values contain only
/// immutable entry observations and the exact trip count.
pub(super) struct Progress {
    /// Bound ordinal used while evaluating one representative visit.
    pub(super) binder: VarIdent,
    /// First observations of both sides of the source condition.
    bounds: (Expr, Expr),
    /// Parametric observations at the representative loop head.
    head: (Expr, Expr),
    /// Persistent scalar entry values and proposed constant per-visit changes.
    scalars: BTreeMap<VarIdent, (Expr, i128)>,
    /// Immutable scalar definitions before binding this invocation's ordinal.
    definitions: BTreeMap<VarIdent, Expr>,
    /// Count dependencies stay visible to enclosing ownership composition.
    pub(super) reads: Vec<Effect>,
    /// Left-observation reads need stability or a checked logical length relation.
    pub(super) left_reads: Vec<Effect>,
    /// Right-observation reads have the same stability requirement.
    pub(super) stable_reads: Vec<Effect>,
    /// Logical role lengths before replacing roots with a recurrence accumulator.
    lengths: BTreeMap<crate::resource::memory::paths::LocalPath, Expr>,
    /// Parametric head observations distinguish identity from first-visit equality.
    head_lengths: BTreeMap<crate::resource::memory::paths::LocalPath, Expr>,
}

impl Trace<'_> {
    /// A containing iteration must pay for every completed inner visit, including
    /// counts depending on its own scalar state. This remains an induction
    /// candidate; the outer body proves the actual retained-charge relationship.
    pub(super) fn nested_growth(
        &self,
        record: &Loop,
        binder: &VarIdent,
        count: &Expr,
        observations: &HashSet<VarIdent>,
    ) -> Option<Expr> {
        let span = &record.span;
        let ceiling = self.loop_size_ceiling.clone().unwrap_or_else(|| expr::integer(span, 0));
        let observations = observations.iter().chain(self.loop_inputs.keys()).cloned().collect();
        let mut added = expr::integer(span, 0);
        for candidate in self
            .loop_allocations
            .iter()
            .map(|(_, _, value)| value)
            .chain(self.loop_calls.iter().map(|(_, _, value)| value))
            .chain(self.loop_nested.iter())
        {
            let candidate = simplify::allocation_bound(candidate, &observations, &ceiling);
            let bound = interval_upper(&candidate, binder, &expr::integer(span, 0), count)?;
            added = contracts::add(span, added, bound);
        }
        Some(simplify::simplify(&contracts::multiply(span, added, count.clone())))
    }

    /// Candidate ceilings may use symbolic invariant bounds and observations of
    /// enclosing visits. Every allocation site proves its own resulting bound.
    pub(super) fn size_bound(&self, record: &Loop) -> Expr {
        let span = &record.span;
        let mut bound = expr::integer(span, i128::from(record.size_ceiling.unwrap_or(0)));
        for candidate in &record.size_candidates {
            let mut evaluator = self.clone();
            if let Some(value) = evaluator.scalar(candidate) {
                bound = contracts::maximum(span, bound, value);
            }
        }
        simplify::simplify(&bound)
    }

    /// Bind persistent scalar translations before evaluating any ownership work.
    pub(super) fn begin_progress(&mut self, record: &Loop, binder: VarIdent) -> Option<Progress> {
        let control = record.control.as_ref()?;
        let first = self.effects.len();
        let left = if record.iterator.is_some() {
            self.progress_bounds(record)?.0
        } else {
            self.scalar(&control.start)?
        };
        let right_start = self.effects.len();
        let left_reads = self.effects[first..right_start].to_vec();
        let right = if record.iterator.is_some() {
            self.progress_bounds(record)?.1
        } else {
            self.scalar(&control.end)?
        };
        let stable_reads = self.effects[right_start..].to_vec();
        let bounds = (left, right);
        let definitions = self
            .state
            .definitions
            .iter()
            .filter(|(name, _)| record.stable_scalar(name))
            .map(|(name, value)| (name.clone(), value.clone()))
            .collect();
        let mut lengths = BTreeMap::new();
        for location in record.length_roles() {
            if let Some(Value::Owner(node)) = self.state.values.get(&location.0) {
                let path = expr::path(
                    &record.span,
                    location.1.iter().map(|slot| self.layouts.metadata_slot(slot)),
                );
                lengths.insert(
                    location.clone(),
                    property(
                        &record.span,
                        expr::subtree(&record.span, node.memory.clone(), path),
                        "length",
                    ),
                );
            }
        }
        let mut scalars = BTreeMap::new();
        for name in record.writes() {
            if let Some(value) = self.state.values.get(name) {
                match value {
                    Value::Owner(_) => continue,
                    Value::Scalar(value) => {
                        let (_, step) = record.scalar_steps.get(name)?;
                        scalars.insert(name.clone(), (value.clone(), *step));
                    }
                    _ => return None,
                }
            }
        }
        let ordinal = SpannedTyped::new(&record.span, &int_typ(), ExprX::Var(binder.clone()));
        if let Some(observation) = &record.progress {
            self.proof_values.insert(binder.clone(), observation.ordinal.clone());
        }
        for (name, (initial, step)) in &scalars {
            self.state.values.insert(
                name.clone(),
                Value::Scalar(at(&record.span, initial.clone(), *step, ordinal.clone())),
            );
        }
        self.bind_iterator_progress(record, ordinal)?;
        let head = self.progress_bounds(record)?;
        let reads = self.effects.split_off(first);
        Some(Progress {
            binder,
            bounds,
            head,
            scalars,
            definitions,
            reads,
            left_reads,
            stable_reads,
            head_lengths: lengths.clone(),
            lengths,
        })
    }

    /// Indexed repetition observes condition changes against a parametric forest,
    /// rather than against a coincidentally equal first-visit child.
    pub(super) fn refresh_progress(
        &mut self,
        record: &Loop,
        progress: &mut Progress,
    ) -> Option<()> {
        let first = self.effects.len();
        progress.head = self.progress_bounds(record)?;
        self.effects.truncate(first);
        progress.head_lengths = self.progress_lengths(record);
        Some(())
    }

    /// Observe fixed roles against the evaluator's current forest domain.
    fn progress_lengths(
        &self,
        record: &Loop,
    ) -> BTreeMap<crate::resource::memory::paths::LocalPath, Expr> {
        record
            .length_roles()
            .filter_map(|location| {
                let Value::Owner(node) = self.state.values.get(&location.0)? else { return None };
                let path = expr::path(
                    &record.span,
                    location.1.iter().map(|slot| self.layouts.metadata_slot(slot)),
                );
                Some((
                    location.clone(),
                    property(
                        &record.span,
                        expr::subtree(&record.span, node.memory.clone(), path),
                        "length",
                    ),
                ))
            })
            .collect()
    }

    /// Validate complete scalar and condition transitions, then derive a count.
    /// A first-visit coincidence cannot establish an invariant translation.
    pub(super) fn finish_progress(
        &mut self,
        record: &Loop,
        progress: &Progress,
    ) -> Option<(Expr, i128)> {
        let span = &record.span;
        for (name, (_, step)) in &progress.scalars {
            let Value::Scalar(next) = self.state.values.get(name)? else { return None };
            let ordinal = SpannedTyped::new(span, &int_typ(), ExprX::Var(progress.binder.clone()));
            let initial = &progress.scalars[name].0;
            let head = at(span, initial.clone(), *step, ordinal);
            if difference(&simplify::simplify(next), &simplify::simplify(&head)) != Some(*step) {
                return None;
            }
        }
        let control = record.control.as_ref()?;
        let first = self.effects.len();
        let after = self.progress_bounds(record)?;
        self.effects.truncate(first);
        let delta = |after: &Expr, before: &Expr| {
            difference(&simplify::simplify(after), &simplify::simplify(before))
                .map(|step| (step, false))
                .or_else(|| saturating_difference(after, before).map(|step| (step, true)))
        };
        let (left, left_saturates) = delta(&after.0, &progress.head.0)?;
        let (right, right_saturates) = delta(&after.1, &progress.head.1)?;
        // A concrete first visit may fold a length clamp away. Classify its
        // potential saturation from the checked observation as well, so known
        // initial lengths do not admit a different progress class from inputs.
        let length = |value: &Expr| {
            matches!(
                self.checked.operations.get(&value.span.id),
                Some(checked::Operation::Length { .. })
            )
        };
        let left_saturates = left_saturates || (left < 0 && length(&control.start));
        let right_saturates = right_saturates || (right < 0 && length(&control.end));
        // A consuming length may clamp only across its final comparison with
        // a stable lower boundary. Two clamped operands can close their gap at
        // a different rate once either reaches zero, so a relative stride alone
        // cannot describe that stopping condition.
        if (left_saturates
            && (right != 0 || !matches!(control.comparison, InequalityOp::Gt | InequalityOp::Ge)))
            || (right_saturates
                && (left != 0
                    || !matches!(control.comparison, InequalityOp::Lt | InequalityOp::Le)))
        {
            return None;
        }
        let stride = control.stride(left, right)?;
        let count =
            count(span, control.gap(progress.bounds.0.clone(), progress.bounds.1.clone()), stride);
        Some((simplify::simplify(&count), stride))
    }

    /// Install scalar exit values after the ownership planner restores entry state.
    pub(super) fn complete_progress(&mut self, record: &Loop, progress: &Progress, count: &Expr) {
        // The native iterator is moved into the loop wrapper and cannot escape.
        // Its symbolic position still matters to containing checked visits.
        if let Some(iterator) = &record.iterator {
            if let Some(Value::Iterator(sequence)) = self.state.values.get_mut(&iterator.receiver) {
                sequence.position = count.clone();
            }
        }
        for (name, (initial, step)) in &progress.scalars {
            self.state.values.insert(
                name.clone(),
                Value::Scalar(simplify::simplify(&at(
                    &record.span,
                    initial.clone(),
                    *step,
                    count.clone(),
                ))),
            );
        }
    }

    /// Length candidates use the same checked operations as forest repetition.
    /// Mixed append/pop programs and guarded writes retain their existing exact
    /// forests but need a richer prefix relation before receiving a candidate.
    pub(super) fn record_progress(
        &mut self,
        record: &Loop,
        progress: &Progress,
        stride: i128,
        effects: &[Effect],
    ) {
        let mut lengths = BTreeMap::<crate::resource::memory::paths::LocalPath, i128>::new();
        let mut blocked = HashSet::new();
        let mut blocked_roots = HashSet::new();
        for effect in effects {
            let delta = match effect {
                Effect::Append { .. } => Some(1),
                Effect::Pop { .. } => Some(-1),
                Effect::AppendBlock { length, .. } | Effect::GenerateBlock { length, .. } => {
                    contracts::constant(length).map(i128::from)
                }
                Effect::PopBlock { amount, .. } => {
                    contracts::constant(amount).map(|n| -i128::from(n))
                }
                Effect::TransferBlock { amount, .. } => contracts::constant(amount).map(i128::from),
                Effect::Identity { .. } => Some(0),
                Effect::Read(_) => continue,
                _ => None,
            };
            if let Some(location) = effect.location() {
                let path = (location.0.clone(), location.1.clone());
                if location.1.iter().any(|slot| matches!(slot, OwnerSlot::Element(_))) {
                    continue;
                }
                if let Some(delta) = delta {
                    let old = lengths.entry(path.clone()).or_default();
                    if *old != 0 && delta != 0 && old.signum() != delta.signum() {
                        blocked.insert(path);
                    } else if let Some(next) = old.checked_add(delta) {
                        *old = next;
                    } else {
                        blocked.insert(path);
                    }
                } else {
                    blocked.insert(path);
                }
            } else if !matches!(effect, Effect::Read(_)) {
                blocked_roots.insert(effect.root().clone());
                blocked.extend(lengths.keys().filter(|(name, _)| name == effect.root()).cloned());
            }
        }
        lengths.retain(|path, _| !blocked.contains(path) && !blocked_roots.contains(&path.0));
        for (path, next) in self.progress_lengths(record) {
            if let Some(delta) = progress.head_lengths.get(&path).and_then(|head| {
                difference(&next, head).or_else(|| saturating_difference(&next, head))
            }) {
                lengths.entry(path).or_insert(delta);
            }
        }
        let entry = |value: &Expr| {
            let value = substitute(value, &self.proof_values);
            crate::ast_visitor::expr_visitor_check(&value, &mut |scope, value| {
                if matches!(&value.x, ExprX::Var(name) if !scope.contains_key(name) && !record.stable_scalar(name)) { Err(()) } else { Ok(()) }
            }).ok().map(|_| value)
        };
        let bounds = (entry(&progress.bounds.0), entry(&progress.bounds.1));
        let scalars = progress
            .scalars
            .iter()
            .filter_map(|(name, (initial, _))| Some((name.clone(), entry(initial)?)))
            .collect();
        let definitions = progress
            .definitions
            .iter()
            .filter_map(|(name, value)| {
                let value = entry(value)?;
                if matches!(&value.x, ExprX::Var(var) if var == name) {
                    return None;
                }
                Some((name.clone(), value))
            })
            .collect();
        let entry_lengths = progress
            .lengths
            .iter()
            .filter(|_| !record.nested)
            .filter_map(|(path, initial)| Some((path.clone(), entry(initial)?)))
            .collect();
        self.loop_progress.insert(
            record.span.id,
            crate::resource::memory::loops::progress::Evidence {
                stride,
                lengths,
                bounds,
                scalars,
                definitions,
                entry_lengths,
                prefixes: BTreeMap::new(),
            },
        );
    }

    /// Repeat the accepted branch program over the completed prefix, rather
    /// than assuming a single length delta for all branches. These expressions
    /// become induction candidates in the executable loop's proof domain.
    pub(super) fn record_prefix_lengths(
        &mut self,
        record: &Loop,
        effects: &[Effect],
        tokens: &HashSet<VarIdent>,
        binder: &VarIdent,
    ) -> Option<()> {
        if !effects.iter().any(|effect| matches!(effect, Effect::Guarded { .. })) {
            return Some(());
        }
        let Some(observation) = &record.progress else { return Some(()) };
        let span = &record.span;
        let programs = guards::partition(
            span,
            effects,
            binder,
            expr::integer(span, 0),
            observation.ordinal.clone(),
            &self.proof_values,
        )?;
        let mut lengths: BTreeMap<_, _> = record
            .length_roles()
            .filter_map(|path| Some((path.clone(), record.entry_length(path)?)))
            .collect();
        let mut changed = HashSet::new();
        let mut blocked = HashSet::new();
        for phase in programs {
            let initial = lengths.clone();
            let mut joined = initial.clone();
            for program in phase {
                let effects = composition::compose(program.effects);
                let blocks =
                    composition::blocks(span, effects.clone(), tokens, binder, self.layouts)
                        .or_else(|| {
                            composition::generators(
                                span,
                                effects,
                                tokens,
                                binder,
                                self.layouts,
                                &self.loop_inputs,
                            )
                        })?;
                let mut selected = initial.clone();
                for effect in blocks {
                    if let Some(location) = effect.location() {
                        let path = (location.0.clone(), location.1.clone());
                        let Some(length) = selected.get_mut(&path) else { continue };
                        *length = match &effect {
                            Effect::AppendBlock { length: width, .. }
                            | Effect::GenerateBlock { length: width, .. } => contracts::add(
                                span,
                                length.clone(),
                                contracts::multiply(span, width.clone(), program.count.clone()),
                            ),
                            Effect::TransferBlock { amount, .. } => contracts::add(
                                span,
                                length.clone(),
                                contracts::multiply(span, amount.clone(), program.count.clone()),
                            ),
                            Effect::PopBlock { amount, .. } => contracts::maximum(
                                span,
                                expr::integer(span, 0),
                                contracts::subtract(
                                    span,
                                    length.clone(),
                                    contracts::multiply(
                                        span,
                                        amount.clone(),
                                        program.count.clone(),
                                    ),
                                ),
                            ),
                            Effect::Identity { .. } => length.clone(),
                            _ => {
                                blocked.insert(path);
                                continue;
                            }
                        };
                        changed.insert(path);
                    } else if !matches!(effect, Effect::Read(_)) {
                        blocked.extend(
                            selected.keys().filter(|(name, _)| name == effect.root()).cloned(),
                        );
                    }
                }
                for (path, length) in selected {
                    joined.insert(
                        path.clone(),
                        choice(span, program.condition.clone(), length, joined[&path].clone()),
                    );
                }
            }
            lengths = joined;
        }
        let mut prefixes = BTreeMap::new();
        for (path, length) in lengths {
            if !changed.contains(&path) || blocked.contains(&path) {
                continue;
            }
            let length = substitute(&length, &self.proof_values);
            // Input geometry without a body observation remains unavailable to
            // this proof candidate; its exact ownership template is unaffected.
            let closed = crate::ast_visitor::expr_visitor_check(&length, &mut |scope, value| {
                if matches!(&value.x, ExprX::Var(name) if !scope.contains_key(name) && self.symbols.iter().any(|symbol| &symbol.name == name)) { Err(()) } else { Ok(()) }
            }).is_ok();
            if closed {
                prefixes.insert(path, length);
            }
        }
        self.loop_progress.get_mut(&record.span.id)?.prefixes = prefixes;
        Some(())
    }
}

/// A translation is evaluated in mathematical integers, with native overflow
/// checked by the unchanged executable assignments.
fn at(span: &Span, initial: Expr, step: i128, ordinal: Expr) -> Expr {
    if step >= 0 {
        contracts::add(span, initial, contracts::multiply(span, expr::integer(span, step), ordinal))
    } else {
        contracts::subtract(
            span,
            initial,
            contracts::multiply(span, expr::integer(span, -step), ordinal),
        )
    }
}

/// Interval arithmetic proposes an upper extent over the whole ordinal range.
/// Subtraction and decreasing counters use both endpoints; multiplication uses
/// all endpoint products. Unknown ordinal-dependent expressions reject.
pub(super) fn interval_upper(
    value: &Expr,
    binder: &VarIdent,
    low: &Expr,
    high: &Expr,
) -> Option<Expr> {
    fn interval(value: &Expr, binder: &VarIdent, low: &Expr, high: &Expr) -> Option<(Expr, Expr)> {
        let span = &value.span;
        if independent(value, binder) {
            return Some((value.clone(), value.clone()));
        }
        if matches!(&value.x, ExprX::Var(name) if name == binder) {
            return Some((low.clone(), high.clone()));
        }
        if let ExprX::If(_, yes, Some(no)) = &value.x {
            let (a, b) = interval(yes, binder, low, high)?;
            let (c, d) = interval(no, binder, low, high)?;
            return Some((contracts::minimum(span, a, c), contracts::maximum(span, b, d)));
        }
        let ExprX::Binary(BinaryOp::Arith(op), left, right) = &value.x else { return None };
        let (a, b) = interval(left, binder, low, high)?;
        let (c, d) = interval(right, binder, low, high)?;
        Some(match op {
            ArithOp::Add(_) => (contracts::add(span, a, c), contracts::add(span, b, d)),
            ArithOp::Sub(_) => (contracts::subtract(span, a, d), contracts::subtract(span, b, c)),
            ArithOp::Mul(_) => {
                let products = [
                    contracts::multiply(span, a.clone(), c.clone()),
                    contracts::multiply(span, a, d.clone()),
                    contracts::multiply(span, b.clone(), c),
                    contracts::multiply(span, b, d),
                ];
                let lower =
                    products.iter().cloned().reduce(|a, b| contracts::minimum(span, a, b))?;
                let upper = products.into_iter().reduce(|a, b| contracts::maximum(span, a, b))?;
                (lower, upper)
            }
            _ => return None,
        })
    }
    interval(value, binder, low, high).map(|(_, upper)| simplify::simplify(&upper))
}

/// Recognize exactly max(previous + delta, 0), preserving intermediate floors.
/// Stripping every clamp would misclassify pop/append mixtures whose floor is
/// positive, so only a zero final floor yields this induction candidate.
fn saturating_difference(value: &Expr, previous: &Expr) -> Option<i128> {
    fn translate(value: &Expr, previous: &Expr) -> Option<(i128, Option<i128>)> {
        if simplify::same_expression(value, previous) {
            return Some((0, None));
        }
        if let ExprX::If(condition, yes, Some(no)) = &value.x {
            if let ExprX::Binary(BinaryOp::Inequality(InequalityOp::Ge), a, b) = &condition.x {
                let inner = if contracts::constant(a) == Some(0)
                    && contracts::constant(yes) == Some(0)
                    && simplify::same_expression(b, no)
                {
                    no
                } else if contracts::constant(b) == Some(0)
                    && contracts::constant(no) == Some(0)
                    && simplify::same_expression(a, yes)
                {
                    yes
                } else {
                    return None;
                };
                let (delta, floor) = translate(inner, previous)?;
                return Some((delta, Some(floor.unwrap_or(0).max(0))));
            }
        }
        let ExprX::Binary(BinaryOp::Arith(op), a, b) = &value.x else { return None };
        let amount = i128::from(contracts::constant(b)?);
        let amount = match op {
            ArithOp::Add(_) => amount,
            ArithOp::Sub(_) => -amount,
            _ => return None,
        };
        let (delta, floor) = translate(a, previous)?;
        Some((
            delta.checked_add(amount)?,
            match floor {
                Some(floor) => Some(floor.checked_add(amount)?),
                None => None,
            },
        ))
    }
    let value = simplify::simplify(value);
    let (delta, floor) = translate(&value, previous)?;
    (delta <= 0 && floor == Some(0)).then_some(delta)
}
