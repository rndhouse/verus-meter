//! Trace guarded alternatives and join continuing ownership and scalar states.
//!
//! Exited branches retain their detached states; only reachable alternatives
//! contribute to the continuing result and path.

use super::*;

impl Trace<'_> {
    /// Evaluate a scalar condition before tracing its two alternatives.
    pub(super) fn branch(
        &mut self,
        span: &Span,
        condition: &Expr,
        yes: &Expr,
        no: &Option<Expr>,
    ) -> Option<Value> {
        let condition = self.scalar(condition)?;
        self.branch_from(span, condition, yes, no)
    }

    /// Trace guarded alternatives, preserve exits, and join continuing states.
    pub(super) fn branch_from(
        &mut self,
        span: &Span,
        condition: Expr,
        yes: &Expr,
        no: &Option<Expr>,
    ) -> Option<Value> {
        let before = self.state.clone();
        let outer = self.path.clone();
        self.path = exits::and(span, outer.clone(), condition.clone());
        let effect_start = self.effects.len();
        let yes_value = self.value(yes)?;
        let yes = self.state.clone();
        let yes_reachable = self.reachable;
        let yes_path = self.path.clone();
        let yes_effects = self.effects.split_off(effect_start);
        self.state = before;
        self.reachable = true;
        self.path = exits::and(span, outer.clone(), exits::not(span, condition.clone()));
        let no_value = if let Some(no) = no { self.value(no)? } else { Value::Unit };
        let no = self.state.clone();
        let no_effects = self.effects.split_off(effect_start);
        self.state = match (yes_reachable, self.reachable) {
            (true, true) => Self::join_state(span, condition.clone(), yes, no)?,
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
        for (selected, effects) in [(true, yes_effects), (false, no_effects)] {
            self.effects.extend(effects.into_iter().map(|effect| Effect::Guarded {
                condition: condition.clone(),
                selected,
                effect: Box::new(effect),
            }));
        }
        if let Some(joins) = self.checked.branches.get(&span.id) {
            self.used.insert((checked::Kind::Branch, span.id));
            for join in joins {
                let memory = |id: Option<usize>| match id {
                    Some(id) => self.regions.get(&id).cloned(),
                    None => Some(expr::empty(span, expr::record_type())),
                };
                let memory = choice(span, condition.clone(), memory(join.yes)?, memory(join.no)?);
                self.regions.insert(join.result, simplify::simplify(&memory));
            }
        }
        match (yes_reachable, no_reachable) {
            (true, true) => Self::join_value(span, condition, &yes_value, &no_value),
            (true, false) => Some(yes_value),
            (false, true) => Some(no_value),
            (false, false) => Some(Value::Unit),
        }
    }

    /// Join matching live bindings and retain only shared immutable definitions.
    pub(super) fn join_state(span: &Span, condition: Expr, yes: State, no: State) -> Option<State> {
        if let ExprX::Const(Constant::Bool(selected)) = condition.x {
            return Some(if selected { yes } else { no });
        }
        if yes.values.keys().collect::<HashSet<_>>() != no.values.keys().collect::<HashSet<_>>() {
            return None;
        }
        let values = yes
            .values
            .iter()
            .map(|(name, left)| {
                Some((
                    name.clone(),
                    Self::join_value(span, condition.clone(), left, &no.values[name])?,
                ))
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
        Some(match (yes, no) {
            (Value::Iterator(yes), Value::Iterator(no)) if yes.step == no.step => {
                Value::Iterator(crate::resource::memory::iterators::Sequence {
                    first: choice(span, condition.clone(), yes.first.clone(), no.first.clone()),
                    count: choice(span, condition.clone(), yes.count.clone(), no.count.clone()),
                    position: choice(span, condition, yes.position.clone(), no.position.clone()),
                    step: yes.step,
                })
            }
            (Value::Owner(yes), Value::Owner(no)) => {
                let mut minima = yes.minima.clone();
                join_minima(span, &mut minima, &no.minima);
                Value::Owner(Node {
                    origin: if yes.origin == no.origin { yes.origin } else { None },
                    typ: yes.typ.clone(),
                    memory: choice(span, condition, yes.memory.clone(), no.memory.clone()),
                    minima,
                })
            }
            (Value::Scalar(yes), Value::Scalar(no)) => {
                Value::Scalar(choice(span, condition, yes.clone(), no.clone()))
            }
            (Value::Unit, Value::Unit) => Value::Unit,
            (Value::Unknown, _) | (_, Value::Unknown) => Value::Unknown,
            _ => return None,
        })
    }
}
