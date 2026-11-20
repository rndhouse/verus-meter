//! Trace guarded alternatives and join continuing ownership and scalar states.
//!
//! Exited branches retain their detached states; only reachable alternatives
//! contribute to the continuing result and path.

use super::*;

impl Trace<'_> {
    /// A data-dependent condition can leave identical checked storage effects.
    pub(super) fn branch(
        &mut self,
        span: &Span,
        condition: &Expr,
        yes: &Expr,
        no: &Option<Expr>,
    ) -> Option<Value> {
        let observation = match self.value(condition)? {
            Value::Scalar(condition) => return self.branch_from(span, condition, yes, no),
            Value::Unknown => None,
            Value::UnknownSize(source) => Some(source),
            _ => return None,
        };
        if self.loop_tokens.is_none() {
            self.failure = observation.map(|source| {
                let mut failure = Failure::new(
                    &condition.span,
                    "a scalar operand needs an unresolved size relationship",
                );
                failure.observation = Some(source);
                failure
            });
            return None;
        }
        let result = self.branch_with_condition(span, None, yes, no);
        if result.is_none() && self.failure.is_none() {
            let mut failure = Failure::new(
                &condition.span,
                "cannot establish a common collection effect for both branches of the loop",
            );
            failure.observation = observation;
            self.failure = Some(failure);
        }
        result
    }

    /// Trace guarded alternatives, preserve exits, and join continuing states.
    pub(super) fn branch_from(
        &mut self,
        span: &Span,
        condition: Expr,
        yes: &Expr,
        no: &Option<Expr>,
    ) -> Option<Value> {
        self.branch_with_condition(span, Some(condition), yes, no)
    }

    fn branch_with_condition(
        &mut self,
        span: &Span,
        condition: Option<Expr>,
        yes: &Expr,
        no: &Option<Expr>,
    ) -> Option<Value> {
        let before = self.state.clone();
        let outer = self.path.clone();
        if let Some(condition) = &condition {
            self.path = exits::and(span, outer.clone(), condition.clone());
        }
        let effect_start = self.effects.len();
        let exit_start = self.exits.len();
        let yes_value = self.value(yes)?;
        let yes = self.state.clone();
        let yes_reachable = self.reachable;
        let yes_path = self.path.clone();
        let yes_effects = self.effects.split_off(effect_start);
        self.state = before;
        self.reachable = true;
        self.path = condition.as_ref().map_or_else(
            || outer.clone(),
            |condition| exits::and(span, outer.clone(), exits::not(span, condition.clone())),
        );
        let no_value = if let Some(no) = no { self.value(no)? } else { Value::Unit };
        let no = self.state.clone();
        let no_effects = self.effects.split_off(effect_start);
        if condition.is_none()
            && (!yes_reachable || !self.reachable || self.exits.len() != exit_start)
        {
            return None;
        }
        self.state = match (yes_reachable, self.reachable) {
            (true, true) => Self::join_states(span, condition.as_ref(), yes, no)?,
            (true, false) => yes,
            _ => no,
        };
        let no_reachable = self.reachable;
        if yes_reachable && no_reachable {
            self.path = outer;
        } else if yes_reachable {
            self.path = yes_path;
        }
        self.reachable |= yes_reachable;
        if let Some(condition) = &condition {
            let decision = Arc::new(condition.clone());
            for (selected, effects) in [(true, yes_effects), (false, no_effects)] {
                self.effects.extend(effects.into_iter().map(|effect| Effect::Guarded {
                    decision: decision.clone(),
                    selected,
                    effect: Box::new(effect),
                }));
            }
        } else {
            self.effects.extend(common_inline_appends(yes_effects, no_effects)?);
        }
        if let Some(joins) = self.checked.branches.get(&span.id) {
            self.used.insert((checked::Kind::Branch, span.id));
            for join in joins {
                let memory = |id: Option<usize>| match id {
                    Some(id) => self.regions.get(&id).cloned(),
                    None => Some(expr::empty(span, expr::record_type())),
                };
                let memory =
                    choose(span, condition.as_ref(), &memory(join.yes)?, &memory(join.no)?)?;
                self.regions.insert(join.result, simplify::simplify(&memory));
            }
        }
        match (yes_reachable, no_reachable) {
            (true, true) => Self::join_values(span, condition.as_ref(), &yes_value, &no_value),
            (true, false) => Some(yes_value),
            (false, true) => Some(no_value),
            (false, false) => Some(Value::Unit),
        }
    }

    /// Join matching live bindings and retain only shared immutable definitions.
    pub(super) fn join_state(span: &Span, condition: Expr, yes: State, no: State) -> Option<State> {
        Self::join_states(span, Some(&condition), yes, no)
    }

    fn join_states(span: &Span, condition: Option<&Expr>, yes: State, no: State) -> Option<State> {
        if let Some(condition) = condition
            && let ExprX::Const(Constant::Bool(selected)) = condition.x
        {
            return Some(if selected { yes } else { no });
        }
        if yes.values.keys().collect::<HashSet<_>>() != no.values.keys().collect::<HashSet<_>>() {
            return None;
        }
        let values = yes
            .values
            .iter()
            .map(|(name, left)| {
                Some((name.clone(), Self::join_values(span, condition, left, &no.values[name])?))
            })
            .collect::<Option<_>>()?;
        let definitions = yes
            .definitions
            .into_iter()
            .filter(|(name, definition)| {
                no.definitions
                    .get(name)
                    .is_some_and(|other| simplify::inspect::same_expression(definition, other))
            })
            .collect();
        let mut written = yes.written;
        written.extend(no.written);
        Some(State { values, definitions, written })
    }

    /// Join compatible symbolic values without losing owner shape or reservation minima.
    pub(super) fn join_value(
        span: &Span,
        condition: Expr,
        yes: &Value,
        no: &Value,
    ) -> Option<Value> {
        Self::join_values(span, Some(&condition), yes, no)
    }

    fn join_values(
        span: &Span,
        condition: Option<&Expr>,
        yes: &Value,
        no: &Value,
    ) -> Option<Value> {
        Some(match (yes, no) {
            (Value::Iterator(yes), Value::Iterator(no)) => {
                use crate::resource::memory::iterators::{Items, Sequence};
                let items = match (&yes.items, &no.items) {
                    (Items::Range { first: a, step }, Items::Range { first: b, step: other })
                        if step == other =>
                    {
                        Items::Range { first: choose(span, condition, a, b)?, step: *step }
                    }
                    (Items::Collection, Items::Collection) => Items::Collection,
                    (Items::Owned(a), Items::Owned(b)) => {
                        Items::Owned(Self::join_owner(span, condition, a, b)?)
                    }
                    _ => return None,
                };
                Value::Iterator(Sequence {
                    items,
                    count: choose(span, condition, &yes.count, &no.count)?,
                    position: choose(span, condition, &yes.position, &no.position)?,
                })
            }
            (Value::CollectionLength(yes), Value::CollectionLength(no)) => {
                Value::CollectionLength(choose(span, condition, yes, no)?)
            }
            (Value::Owner(yes), Value::Owner(no)) => {
                Value::Owner(Self::join_owner(span, condition, yes, no)?)
            }
            (Value::Scalar(yes), Value::Scalar(no)) => {
                choose(span, condition, yes, no).map_or(Value::Unknown, Value::Scalar)
            }
            (Value::Unit, Value::Unit) => Value::Unit,
            (Value::Owner(_) | Value::Iterator(_), _)
            | (_, Value::Owner(_) | Value::Iterator(_))
                if condition.is_none() =>
            {
                return None;
            }
            (Value::UnknownSize(span), _) | (_, Value::UnknownSize(span)) => {
                Value::UnknownSize(span.clone())
            }
            (Value::Unknown, _) | (_, Value::Unknown) => Value::Unknown,
            _ => return None,
        })
    }

    fn join_owner(span: &Span, condition: Option<&Expr>, yes: &Node, no: &Node) -> Option<Node> {
        let mut minima = yes.minima.clone();
        join_minima(span, &mut minima, &no.minima);
        Some(Node {
            origin: if yes.origin == no.origin { yes.origin } else { None },
            typ: yes.typ.clone(),
            memory: choose(span, condition, &yes.memory, &no.memory)?,
            minima,
        })
    }
}

/// Descriptors may depend on a known condition. An opaque condition can only
/// preserve observations that agree on both paths.
fn choose(span: &Span, condition: Option<&Expr>, yes: &Expr, no: &Expr) -> Option<Expr> {
    if let Some(condition) = condition {
        Some(choice(span, condition.clone(), yes.clone(), no.clone()))
    } else if simplify::inspect::same_expression(yes, no) {
        Some(yes.clone())
    } else {
        None
    }
}

/// Payload values of inline appends are absent from the ownership descriptor.
/// Keep both paths' read dependencies and require identical ordered writes.
fn common_inline_appends(yes: Vec<Effect>, no: Vec<Effect>) -> Option<Vec<Effect>> {
    let (yes_reads, yes): (Vec<_>, Vec<_>) =
        yes.into_iter().partition(|effect| matches!(effect, Effect::Read(_)));
    let (no_reads, no): (Vec<_>, Vec<_>) =
        no.into_iter().partition(|effect| matches!(effect, Effect::Read(_)));
    if yes.len() != no.len() {
        return None;
    }
    for (yes, no) in yes.iter().zip(&no) {
        let (
            Effect::Append { location: a, typ, child, original, element, grow },
            Effect::Append {
                location: b,
                typ: other_typ,
                child: other_child,
                original: other_original,
                element: other_element,
                grow: other_grow,
            },
        ) = (yes, no)
        else {
            return None;
        };
        if a.0 != b.0
            || a.1 != b.1
            || a.2.len() != b.2.len()
            || !a.2.iter().zip(&b.2).all(|(a, b)| simplify::inspect::same_expression(a, b))
            || !crate::ast_util::types_equal(typ, other_typ)
            || matches!(child, Value::Owner(_) | Value::Iterator(_))
            || matches!(other_child, Value::Owner(_) | Value::Iterator(_))
            || !simplify::inspect::same_expression(original, other_original)
            || element != other_element
            || grow != other_grow
        {
            return None;
        }
    }
    let appends = yes.into_iter().map(|mut effect| {
        let Effect::Append { child, .. } = &mut effect else { unreachable!() };
        *child = Value::Unknown;
        effect
    });
    Some(yes_reads.into_iter().chain(no_reads).chain(appends).collect())
}
