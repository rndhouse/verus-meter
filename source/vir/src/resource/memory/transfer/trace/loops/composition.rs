//! Ordered reduction of checked iteration effects before choosing repeated roles.
//!
//! Only whole-child identities are reduced here. Body accounting has already
//! checked all intermediate lifetimes and allocation peaks; reducing a retained
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
