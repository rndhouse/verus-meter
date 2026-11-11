//! Compose one checked iteration over disjoint persistent ownership roles.
//! Building, consumption, and transfer use the same region transitions.
//! Unsupported dependencies reject the summary rather than inventing footprints.

use super::*;

pub(super) enum Effect {
    Mutation(VarIdent),
    Read(VarIdent),
    Append { location: Location, typ: Typ, child: Value, element: u64, grow: bool },
    Pop { location: Location, typ: Typ, token: Option<VarIdent> },
}

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

impl Effect {
    fn location(&self) -> Option<&Location> {
        match self {
            Self::Append { location, .. } | Self::Pop { location, .. } => Some(location),
            _ => None,
        }
    }

    fn root(&self) -> &VarIdent {
        match self {
            Self::Mutation(name) | Self::Read(name) => name,
            Self::Append { location, .. } | Self::Pop { location, .. } => &location.0,
        }
    }
}

fn local(value: &Expr) -> Option<&VarIdent> {
    match &value.x {
        ExprX::Var(name) => Some(name),
        ExprX::ReadPlace(place, _) => match &place.x {
            PlaceX::Local(name) => Some(name),
            _ => None,
        },
        _ => None,
    }
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
    pub(super) fn loop_value(
        &mut self,
        span: &Span,
        condition: &Option<Expr>,
        body: &Expr,
    ) -> Option<Value> {
        let before = self.state.clone();
        let used = self.used.clone();
        let regions = self.regions.clone();
        let tokens = self.loop_tokens.clone();
        let invariants = self.loop_invariants.clone();
        let effects = self.effects.len();
        let depth = self.branch_depth;
        if let Some(value) = self.collection_loop(span, condition, body) {
            return Some(value);
        }
        self.state = before;
        self.regions = regions;
        self.loop_tokens = tokens;
        self.loop_invariants = invariants;
        self.used = used;
        self.effects.truncate(effects);
        self.branch_depth = depth;
        // Preserve the existing read-only traversal case, without exporting
        // unknown scalar results or ignoring executable ownership effects.
        let mut effects = false;
        for region in condition.iter().chain(std::iter::once(body)) {
            let _ = crate::ast_visitor::expr_visitor_check(region, &mut |_, value| {
                effects |= self.layouts.owner(&value.typ)
                    || matches!(value.x, ExprX::Call { .. } | ExprX::Return(_));
                Ok::<(), VirErr>(())
            });
        }
        if effects {
            return None;
        }
        for value in self.state.values.values_mut() {
            if matches!(value, Value::Scalar(_)) {
                *value = Value::Unknown;
            }
        }
        if self.checked.loops.get(&span.id).is_some_and(Vec::is_empty) {
            self.used.insert((checked::Kind::Loop, span.id));
        }
        Some(Value::Unit)
    }

    fn collection_loop(
        &mut self,
        span: &Span,
        condition: &Option<Expr>,
        body: &Expr,
    ) -> Option<Value> {
        let ExprX::Binary(BinaryOp::Inequality(op), left, right) = &condition.as_ref()?.x else {
            return None;
        };
        let counted = match op {
            InequalityOp::Lt => true,
            InequalityOp::Gt => false,
            _ => return None,
        };
        let before = self.state.clone();
        let counter = if counted { Some(local(left)?.clone()) } else { None };
        let start = self.scalar(left)?;
        let mut invalid = false;
        let _ = crate::ast_visitor::expr_visitor_check(body, &mut |_, value| {
            if let ExprX::Assign { place, .. } = &value.x {
                if let PlaceX::Local(name) = &place.x {
                    invalid |= before.values.contains_key(name)
                        && !matches!(before.values[name], Value::Owner(_))
                        && Some(name) != counter.as_ref();
                }
            }
            Ok::<(), VirErr>(())
        });
        if invalid {
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
        self.value(body)?;
        let tokens = std::mem::replace(&mut self.loop_tokens, outer_tokens).unwrap();
        self.branch_depth = depth;
        let effects = self.effects.split_off(effect_start);
        let persistent: Vec<_> = effects
            .into_iter()
            .filter(|effect| before.values.contains_key(effect.root()))
            .collect();
        let mut roles = Vec::new();
        for effect in persistent {
            let (location, typ) = match &effect {
                Effect::Append { location, typ, .. } | Effect::Pop { location, typ, .. } => {
                    (location, typ)
                }
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
                matches!(effect, Effect::Pop { location, .. }
                if location.0 == tested.0 && location.1 == tested.1)
            }) {
                return None;
            }
        }
        let transfers = transfer_edges(&roles, &tokens, &binder)?;
        let iteration = Iteration { roles, transfers, count };
        let Iteration { roles, transfers, count } = &iteration;
        let regions = self.checked.loops.get(&span.id)?.clone();
        // Each transfer preserves the sum of the source and destination child
        // charges. These are proof candidates, not assumed accounting facts.
        let charges = self.checked.loop_charges.get(&span.id)?;
        for (target, source) in transfers {
            let charge = |index: usize| {
                let location = roles[index].0.location()?;
                charges.iter().find(|charge| {
                    charge.location.0 == location.0 && charge.location.1 == location.1
                })
            };
            let a = charge(*source)?;
            let b = charge(*target)?;
            self.loop_invariants.entry(span.id).or_default().push(mk_ineq(
                span,
                &contracts::add(span, a.current.clone(), b.current.clone()),
                &contracts::add(span, a.entry.clone(), b.entry.clone()),
                InequalityOp::Le,
            ));
        }
        self.used.insert((checked::Kind::Loop, span.id));
        self.state = before;
        if let Some(counter) = counter {
            self.state.values.insert(counter, Value::Scalar(contracts::maximum(span, start, end)));
        }
        for (index, (effect, initial)) in roles.iter().enumerate() {
            let location = effect.location()?;
            let length = property(span, initial.memory.clone(), "length");
            let capacity = property(span, initial.memory.clone(), "capacity");
            let bytes = property(span, initial.memory.clone(), "bytes");
            let mut node = initial.clone();
            match effect {
                Effect::Pop { .. } => {
                    let final_length = contracts::maximum(
                        span,
                        expr::integer(span, 0),
                        contracts::subtract(span, length, count.clone()),
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
                Effect::Append { child, element, grow, .. } => {
                    let added = if let Some(source) = transfers.get(&index) {
                        let source = &roles[*source].1;
                        reverse_range(
                            span,
                            source.memory.clone(),
                            property(span, source.memory.clone(), "length"),
                            count.clone(),
                            length.clone(),
                        )
                    } else if let Value::Owner(child) = child {
                        expr::operation(
                            span,
                            "repeat",
                            vec![child.memory.clone(), length.clone(), count.clone()],
                            expr::memory_type(),
                        )
                    } else if !self.layouts.owning_elements(&node.typ) {
                        expr::empty(span, expr::record_type())
                    } else {
                        return None;
                    };
                    node.memory = expr::add(span, node.memory, added);
                    if let Value::Owner(child) = child {
                        let minima = child
                            .minima
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
                        join_minima(span, &mut node.minima, &minima);
                    }
                    let final_length = contracts::add(span, length, count.clone());
                    let (capacity, retained) = if *grow {
                        let replacement = contracts::multiply(
                            span,
                            contracts::literal(span, *element),
                            growth::grown_capacity(span, final_length.clone(), *element),
                        );
                        let retained = choice(
                            span,
                            mk_ineq(span, &final_length, &capacity, InequalityOp::Le),
                            bytes.clone(),
                            contracts::maximum(span, bytes, replacement),
                        );
                        (contracts::maximum(span, capacity, final_length.clone()), retained)
                    } else {
                        (capacity, bytes)
                    };
                    node.memory = with_root(
                        span,
                        node.memory,
                        retained,
                        capacity,
                        final_length,
                        self.layouts.owning_elements(&node.typ),
                    );
                }
                _ => return None,
            }
            self.set(span, location, node)?;
            if let Some(region) = regions
                .iter()
                .find(|region| region.location.0 == location.0 && region.location.1 == location.1)
            {
                let remaining = self.loop_region(span, index, &iteration, &regions, region)?;
                self.regions.insert(region.exit, remaining);
            }
        }
        if regions.iter().any(|region| !self.regions.contains_key(&region.exit)) {
            return None;
        }
        Some(Value::Unit)
    }

    /// Original lifetime regions exclude all allocations created in this frame.
    /// Apply the same graph and index map used for complete physical forests.
    fn loop_region(
        &self,
        span: &Span,
        index: usize,
        iteration: &Iteration,
        regions: &[checked::LoopRegion],
        region: &checked::LoopRegion,
    ) -> Option<Expr> {
        let Iteration { roles, transfers, count } = iteration;
        let (effect, initial) = &roles[index];
        let original = region
            .entry
            .map(|id| self.regions.get(&id).cloned())
            .unwrap_or_else(|| Some(expr::empty(span, expr::record_type())))?;
        let remaining = match effect {
            Effect::Pop { .. } => {
                let length = contracts::maximum(
                    span,
                    expr::integer(span, 0),
                    contracts::subtract(
                        span,
                        property(span, initial.memory.clone(), "length"),
                        count.clone(),
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
            Effect::Append { .. } => {
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
                        count.clone(),
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

/// Edges move complete child forests, without assuming a uniform footprint.
/// Other payloads must be independent of the counter and all extracted children.
fn transfer_edges(
    roles: &[(Effect, Node)],
    tokens: &HashSet<VarIdent>,
    binder: &VarIdent,
) -> Option<HashMap<usize, usize>> {
    let mut transfers = HashMap::new();
    let mut consumed = HashSet::new();
    for (index, (effect, _)) in roles.iter().enumerate() {
        if let Effect::Append { child: Value::Owner(child), .. } = effect {
            let memory = simplify::simplify(&child.memory);
            if let ExprX::Var(name) = &memory.x {
                if tokens.contains(name) {
                    let source = roles.iter().position(|(effect, _)| {
                        matches!(effect,
                        Effect::Pop { token: Some(token), .. } if token == name)
                    })?;
                    if !consumed.insert(source) {
                        return None;
                    }
                    transfers.insert(index, source);
                    continue;
                }
            }
            if !independent(&memory, binder)
                || tokens.iter().any(|token| !independent(&memory, token))
                || child.minima.values().any(|floor| !independent(&floor.capacity, binder))
            {
                return None;
            }
        }
    }
    Some(transfers)
}
