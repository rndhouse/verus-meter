//! Closed collection regions for checked loops. A representative iteration must
//! have one unconditional persistent effect; temporary owning values may have
//! any supported fixed or repeated layout. Unsupported dependencies decline the
//! entire template, rather than guessing a per-element allocation.

use super::*;

pub(super) enum Effect {
    Mutation(VarIdent),
    Read(VarIdent),
    Append(Location, Typ, Value),
    Pop(Location, Typ),
}

impl Effect {
    fn root(&self) -> &VarIdent {
        match self {
            Self::Mutation(name) | Self::Read(name) => name,
            Self::Append(location, _, _) | Self::Pop(location, _) => &location.0,
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
        let effects = self.effects.len();
        let depth = self.branch_depth;
        if let Some(value) = self.collection_loop(span, condition, body) {
            return Some(value);
        }
        self.state = before;
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
        Some(Value::Unit)
    }

    fn collection_loop(
        &mut self,
        span: &Span,
        condition: &Option<Expr>,
        body: &Expr,
    ) -> Option<Value> {
        let Some(condition) = condition else { return None };
        let ExprX::Binary(BinaryOp::Inequality(op), left, right) = &condition.x else {
            return None;
        };
        let (left, right, growing) = match op {
            InequalityOp::Lt => (left, right, true),
            InequalityOp::Gt => (left, right, false),
            _ => return None,
        };
        let before = self.state.clone();
        let counter = if growing { Some(local(left)?.clone()) } else { None };
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
        // A fresh counter exposes footprint dependence on the iteration index.
        // It is never exported: all surviving expressions must eliminate it.
        let binder = VarIdent(
            Arc::new("$memory_transfer_iteration".into()),
            // This private binder never escapes its representative iteration.
            // Use the loop identity without consuming allocation-state IDs.
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
        let effect_start = self.effects.len();
        let depth = self.branch_depth;
        self.branch_depth = 0;
        self.value(body)?;
        self.branch_depth = depth;
        let effects = self.effects.split_off(effect_start);
        let persistent: Vec<_> =
            effects.iter().filter(|effect| before.values.contains_key(effect.root())).collect();
        let [effect] = persistent.as_slice() else { return None };
        let (location, mut node) = match effect {
            Effect::Append(location, typ, _) | Effect::Pop(location, typ) => {
                // Fixed paths are stable throughout the iteration. An indexed
                // receiver could select a different collection on each pass.
                if location.1.iter().any(|slot| matches!(slot, OwnerSlot::Element(_))) {
                    return None;
                }
                let after = std::mem::replace(&mut self.state, before.clone());
                let node = self.get(span, location, typ)?;
                self.state = after;
                (location, node)
            }
            _ => return None,
        };
        if bound_effects
            .iter()
            .any(|effect| !matches!(effect, Effect::Read(name) if *name != location.0))
        {
            return None;
        }
        let length = property(span, node.memory.clone(), "length");
        let capacity = property(span, node.memory.clone(), "capacity");
        let bytes = property(span, node.memory.clone(), "bytes");
        if growing {
            let Effect::Append(_, _, child) = effect else { return None };
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
            let count = contracts::maximum(
                span,
                expr::integer(span, 0),
                contracts::subtract(span, end.clone(), start.clone()),
            );
            if let Value::Owner(child) = child {
                if !independent(&child.memory, &binder)
                    || child.minima.values().any(|floor| !independent(&floor.capacity, &binder))
                {
                    return None;
                }
                node.memory = expr::add(
                    span,
                    node.memory,
                    expr::operation(
                        span,
                        "repeat",
                        vec![child.memory.clone(), length.clone(), count.clone()],
                        expr::memory_type(),
                    ),
                );
                let minima = child
                    .minima
                    .iter()
                    .map(|(path, floor)| {
                        (
                            std::iter::once(Step::Repeated).chain(path.iter().cloned()).collect(),
                            floor.clone(),
                        )
                    })
                    .collect();
                join_minima(span, &mut node.minima, &minima);
            } else if self.layouts.owning_elements(&node.typ) {
                return None;
            }
            let final_length = contracts::add(span, length, count);
            // Every replacement in an append-only interval is bounded by
            // growth at its final length. Reservation floors are separate
            // from this upper bound; sufficient spare capacity retains bytes.
            let element = self.layouts.vector_element(&node.typ, span).ok()?;
            let replacement = contracts::multiply(
                span,
                contracts::literal(span, element),
                growth::grown_capacity(span, final_length.clone(), element),
            );
            let retained = choice(
                span,
                mk_ineq(span, &final_length, &capacity, InequalityOp::Le),
                bytes.clone(),
                contracts::maximum(span, bytes, replacement),
            );
            node.memory = with_root(
                span,
                node.memory,
                retained,
                contracts::maximum(span, capacity, final_length.clone()),
                final_length,
                self.layouts.owning_elements(&node.typ),
            );
            self.state = before;
            self.state.values.insert(counter?, Value::Scalar(contracts::maximum(span, start, end)));
        } else {
            if !matches!(effect, Effect::Pop(_, _)) {
                return None;
            }
            // The condition must read this exact collection, not an unrelated
            // counter which happens to be paired with a pop in the body.
            let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &left.x
            else {
                return None;
            };
            let (tested, _) = self.receiver(args.first()?)?;
            if attrs.resource_intrinsic != Some(ResourceIntrinsic::VecLen)
                || tested.0 != location.0
                || tested.1 != location.1
            {
                return None;
            }
            let final_length = contracts::minimum(
                span,
                length,
                contracts::maximum(span, expr::integer(span, 0), end),
            );
            node.memory = with_root(
                span,
                expr::operation(
                    span,
                    "take_children",
                    vec![node.memory, final_length.clone()],
                    expr::memory_type(),
                ),
                bytes,
                capacity,
                final_length,
                self.layouts.owning_elements(&node.typ),
            );
            self.state = before;
        }
        self.set(span, location, node)?;
        Some(Value::Unit)
    }
}
