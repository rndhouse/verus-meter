//! Close symbolic control-flow edges using their exact scalar path guards.

use super::*;
use crate::resource::memory::control::Target;

/// A detached symbolic result and the persistent owners surviving its scopes.
#[derive(Clone)]
pub(super) struct Edge {
    /// Compiler-resolved destination accepted by the body proof.
    pub(super) target: Target,
    /// Scalar path selecting this edge; never inferred from payload bytes.
    pub(super) condition: Expr,
    /// Persistent ownership after lexical cleanup.
    pub(super) state: State,
    /// Complete forest or scalar produced by this exit.
    pub(super) result: Value,
}

pub(super) fn and(span: &Span, left: Expr, right: Expr) -> Expr {
    simplify::simplify(&SpannedTyped::new(
        span,
        &bool_typ(),
        ExprX::Logical(LogicalOp::And, left, right),
    ))
}

pub(super) fn not(span: &Span, value: Expr) -> Expr {
    simplify::simplify(&SpannedTyped::new(span, &bool_typ(), ExprX::Unary(UnaryOp::Not, value)))
}

impl Trace<'_> {
    /// Only checked head guards and current-loop continuations can close an
    /// ordinary counted visit. Other exits need a different recurrence and
    /// remain unsupported when a precise reusable summary is required.
    pub(super) fn iteration(
        &mut self,
        record: &crate::resource::memory::loops::Loop,
    ) -> Option<()> {
        let first_exit = self.exits.len();
        let outer = self.path.clone();
        self.path = crate::ast_util::mk_bool(&record.span, true);
        for id in &record.head_breaks {
            if self.checked.exits.get(id) != Some(&Target::Break(record.label.clone())) {
                return None;
            }
            self.used.insert((checked::Kind::Exit, *id));
        }
        let result = self.value(&record.iteration_body)?;
        if self.exits[first_exit..]
            .iter()
            .any(|edge| edge.target != Target::Continue(record.label.clone()))
        {
            return None;
        }
        self.finish_exits(&record.span, result, &Target::Continue(record.label.clone()))?;
        if !self.reachable {
            return None;
        }
        self.path = outer;
        Some(())
    }
    /// Effects after a conditional exit execute only on its surviving path.
    pub(super) fn guard_effects(&mut self, start: usize, path: &Expr) {
        if matches!(path.x, ExprX::Const(Constant::Bool(true))) {
            return;
        }
        let effects = self.effects.split_off(start);
        self.effects.extend(effects.into_iter().map(|effect| Effect::Guarded {
            condition: path.clone(),
            selected: true,
            effect: Box::new(effect),
        }));
    }

    /// Consume one destination while preserving edges to outer lexical targets.
    /// Conditions join complete forests rather than replacing them with costs.
    pub(super) fn finish_exits(
        &mut self,
        span: &Span,
        normal: Value,
        target: &Target,
    ) -> Option<Value> {
        let mut result = self.reachable.then_some(normal);
        let edges = std::mem::take(&mut self.exits);
        for edge in edges {
            if &edge.target != target {
                self.exits.push(edge);
                continue;
            }
            if let Some(previous) = result {
                result =
                    Some(Self::join_value(span, edge.condition.clone(), &edge.result, &previous)?);
                self.state =
                    Self::join_state(span, edge.condition.clone(), edge.state, self.state.clone())?;
                self.path = simplify::simplify(&SpannedTyped::new(
                    span,
                    &bool_typ(),
                    ExprX::Logical(LogicalOp::Or, self.path.clone(), edge.condition),
                ));
            } else {
                result = Some(edge.result);
                self.state = edge.state;
                self.path = edge.condition;
            }
        }
        self.reachable = result.is_some();
        Some(result.unwrap_or(Value::Unit))
    }

    pub(super) fn single_visit(
        &mut self,
        record: &crate::resource::memory::loops::Loop,
    ) -> Option<Value> {
        let span = &record.span;
        let outer = self.path.clone();
        let condition = if record.conditional {
            self.scalar(&record.condition)?
        } else {
            crate::ast_util::mk_bool(span, true)
        };
        // The condition executes even when the body does not. Its ownership
        // changes belong to both normal completion and any body exit.
        let entry = self.state.clone();
        self.path = and(span, outer.clone(), condition.clone());
        let first_effect = self.effects.len();
        self.value(&record.body)?;
        if record.conditional {
            self.guard_effects(first_effect, &condition);
        }
        // A checked single visit has no normal back edge. Only breaks produce
        // the loop value; returns and outer labelled exits keep propagating.
        if self.reachable {
            return None;
        }
        let result = self.finish_exits(span, Value::Unit, &Target::Break(record.label.clone()))?;
        let result = if record.conditional {
            let normal_path = and(span, outer, not(span, condition.clone()));
            let value = if self.reachable {
                Self::join_value(span, condition.clone(), &result, &Value::Unit)?
            } else {
                Value::Unit
            };
            self.state = if self.reachable {
                Self::join_state(span, condition.clone(), self.state.clone(), entry)?
            } else {
                entry
            };
            self.path = if self.reachable {
                simplify::simplify(&SpannedTyped::new(
                    span,
                    &bool_typ(),
                    ExprX::Logical(LogicalOp::Or, self.path.clone(), normal_path),
                ))
            } else {
                normal_path
            };
            self.reachable = true;
            value
        } else {
            result
        };
        self.used.insert((checked::Kind::Loop, span.id));
        Some(result)
    }
}
