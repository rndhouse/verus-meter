//! Ordered reduction of checked iteration effects before choosing repeated roles.
//!
//! Reduce whole-child identities, then compose monotone operations on disjoint
//! roles into ordered blocks. Body accounting has already checked all
//! intermediate lifetimes and allocation peaks; reducing a retained
//! transformation must never erase those proof obligations.

use super::*;

/// Cancel a last-element extraction followed by restoration of that exact child.
/// Disjoint paths can interleave. A read, unknown mutation, overlapping parent,
/// or changed payload prevents the reduction. Runtime indices are deliberately
/// excluded: equal path classes do not imply equal executable indices.
pub(super) fn compose(effects: Vec<Effect>) -> Vec<Effect> {
    let mut result: Vec<Effect> = Vec::new();
    for effect in effects {
        let Effect::Append { location, child: Value::Owner(child), typ, .. } = &effect else {
            result.push(effect);
            continue;
        };
        if location.1.iter().any(|slot| matches!(slot, OwnerSlot::Element(_))) {
            result.push(effect);
            continue;
        }
        let memory = simplify::simplify(&child.memory);
        let ExprX::Var(name) = &memory.x else {
            result.push(effect);
            continue;
        };
        let previous = result.iter().rposition(|previous| {
            if previous.root() != &location.0 {
                return false;
            }
            match previous {
                Effect::Identity { .. } => false,
                _ => previous.location().is_none_or(|other| {
                    other.1.starts_with(&location.1) || location.1.starts_with(&other.1)
                }),
            }
        });
        if let Some(index) = previous {
            if matches!(&result[index], Effect::Pop { location: source, token: Some(token), .. }
                if source.0 == location.0 && source.1 == location.1 && token == name)
            {
                result[index] = Effect::Identity { location: location.clone(), typ: typ.clone() };
                continue;
            }
        }
        result.push(effect);
    }
    // A role may contain nested or sequential round trips. Retain an identity
    // only when no remaining operation overlaps it; otherwise it is redundant
    // beside that role's nontrivial transformation.
    let mut identities = HashSet::new();
    let keep: Vec<_> = result
        .iter()
        .map(|effect| {
            let Effect::Identity { location, .. } = effect else { return true };
            identities.insert((location.0.clone(), location.1.clone()))
                && !result.iter().any(|other| {
                    !matches!(other, Effect::Identity { .. })
                        && other.root() == &location.0
                        && other.location().is_some_and(|other| {
                            other.1.starts_with(&location.1) || location.1.starts_with(&other.1)
                        })
                })
        })
        .collect();
    result.into_iter().zip(keep).filter_map(|(effect, keep)| keep.then_some(effect)).collect()
}

/// Combine adjacent effects on the same disjoint role into ordered forest
/// blocks. Whole-child transfer tokens stay explicit for the transfer graph;
/// fresh blocks may not depend on those tokens or on the iteration counter.
pub(super) fn blocks(
    span: &Span,
    effects: Vec<Effect>,
    tokens: &HashSet<VarIdent>,
    binder: &VarIdent,
    layouts: &crate::resource::memory::layout::Layouts,
) -> Option<Vec<Effect>> {
    let referenced = |name: &VarIdent| {
        effects.iter().any(|effect| match effect {
            Effect::Append { child: Value::Owner(child), .. } => !independent(&child.memory, name),
            Effect::AppendBlock { memory, length, .. } => {
                !independent(memory, name) || !independent(length, name)
            }
            _ => false,
        })
    };
    let used: HashSet<_> = tokens.iter().filter(|token| referenced(token)).cloned().collect();
    let sources: HashMap<_, _> = effects
        .iter()
        .filter_map(|effect| match effect {
            Effect::Pop { location, token: Some(token), .. } => {
                Some((token.clone(), location.clone()))
            }
            _ => None,
        })
        .collect();
    let mut result: Vec<Effect> = Vec::new();
    for effect in effects {
        let effect = match effect {
            Effect::Append { location, typ, child, element, grow } => {
                let (memory, minima) = match &child {
                    Value::Owner(node)
                        if tokens.iter().any(|token| !independent(&node.memory, token)) =>
                    {
                        let memory = simplify::simplify(&node.memory);
                        let ExprX::Var(token) = &memory.x else {
                            return None;
                        };
                        let source = sources.get(token)?.clone();
                        let next = Effect::TransferBlock {
                            location,
                            source,
                            typ,
                            amount: expr::integer(span, 1),
                            flows: vec![token.clone()],
                            minima: node.minima.clone(),
                            element,
                            grow,
                        };
                        // Range appends use the same role merge below.
                        let next = merge(span, &mut result, next)?;
                        if let Some(next) = next {
                            result.push(next);
                        }
                        continue;
                    }
                    Value::Owner(node) => (
                        expr::prefix(span, node.memory.clone(), expr::path(span, [0])),
                        node.minima.clone(),
                    ),
                    _ if layouts.owning_elements(&typ) => return None,
                    _ => (expr::empty(span, expr::record_type()), Minima::new()),
                };
                Effect::AppendBlock {
                    location,
                    typ,
                    memory,
                    length: expr::integer(span, 1),
                    minima,
                    element,
                    grow,
                }
            }
            Effect::Pop { location, typ, token } => {
                let flows = token.filter(|token| used.contains(token)).map(|token| vec![token]);
                Effect::PopBlock { location, typ, amount: expr::integer(span, 1), flows }
            }
            effect => effect,
        };
        if let Effect::AppendBlock { memory, length, minima, .. } = &effect {
            if !independent(memory, binder)
                || !independent(length, binder)
                || tokens
                    .iter()
                    .any(|token| !independent(memory, token) || !independent(length, token))
                || minima.values().any(|floor| !independent(&floor.capacity, binder))
            {
                return None;
            }
        }
        if let Effect::PopBlock { amount, .. } = &effect {
            if !independent(amount, binder)
                || tokens.iter().any(|token| !independent(amount, token))
            {
                return None;
            }
        }
        if let Some(effect) = merge(span, &mut result, effect)? {
            result.push(effect);
        }
    }
    Some(result)
}

pub(super) fn shift(span: &Span, memory: Expr, start: Expr) -> Expr {
    expr::operation(span, "shift_children", vec![memory, start], expr::memory_type())
}

pub(super) fn tile(span: &Span, memory: Expr, width: Expr, count: Expr, start: Expr) -> Expr {
    simplify::simplify(&expr::operation(
        span,
        "tile_children",
        vec![memory, width, count, start],
        expr::memory_type(),
    ))
}

/// Merge only disjoint roles or like monotone effects. Mixed source/destination
/// roles and partial range routing require a different repeated transformation.
fn merge(span: &Span, result: &mut [Effect], effect: Effect) -> Option<Option<Effect>> {
    let location = effect.location()?;
    if location.1.iter().any(|slot| matches!(slot, OwnerSlot::Element(_))) {
        return None;
    }
    let previous = result.iter().rposition(|previous| {
        previous.root() == &location.0
            && previous.location().is_none_or(|other| {
                other.1.starts_with(&location.1) || location.1.starts_with(&other.1)
            })
    });
    if let Some(index) = previous {
        let other = result[index].location()?;
        if other.1 != location.1 {
            return None;
        }
        match (&mut result[index], &effect) {
            (
                Effect::AppendBlock { memory, length, minima, element, grow, .. },
                Effect::AppendBlock {
                    memory: next,
                    length: width,
                    minima: floors,
                    element: size,
                    grow: permission,
                    ..
                },
            ) if element == size && grow == permission => {
                *memory = simplify::simplify(&expr::add(
                    span,
                    memory.clone(),
                    shift(span, next.clone(), length.clone()),
                ));
                *length = simplify::simplify(&contracts::add(span, length.clone(), width.clone()));
                join_minima(span, minima, floors);
                return Some(None);
            }
            (
                Effect::PopBlock { amount, flows, .. },
                Effect::PopBlock { amount: next, flows: next_flows, .. },
            ) => {
                match (flows.as_mut(), next_flows) {
                    (Some(flows), Some(next)) => flows.extend(next.iter().cloned()),
                    (None, None) => {}
                    _ => return None,
                }
                *amount = simplify::simplify(&contracts::add(span, amount.clone(), next.clone()));
                return Some(None);
            }
            (
                Effect::TransferBlock { source, amount, flows, minima, element, grow, .. },
                Effect::TransferBlock {
                    source: next_source,
                    amount: next_amount,
                    flows: next_flows,
                    minima: floors,
                    element: size,
                    grow: permission,
                    ..
                },
            ) if source.0 == next_source.0
                && source.1 == next_source.1
                && element == size
                && grow == permission =>
            {
                *amount =
                    simplify::simplify(&contracts::add(span, amount.clone(), next_amount.clone()));
                flows.extend(next_flows.iter().cloned());
                join_minima(span, minima, floors);
                return Some(None);
            }
            _ => return None,
        }
    }
    Some(Some(effect))
}
