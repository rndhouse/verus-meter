//! Evaluate source control flow and scalar operands through checked transitions.
//!
//! Executable ownership operations dispatch to body accounting's recorded rule.
//! Block cleanup also removes locals from detached exit states.

use super::*;
use crate::resource::memory::{execution, model, projections};

impl Trace<'_> {
    /// Trace an operand only when its result has a representable scalar value.
    pub(super) fn scalar(&mut self, value: &Expr) -> Option<Expr> {
        match self.value(value)? {
            Value::Scalar(value) => Some(value),
            _ => None,
        }
    }

    /// Trace reachable statements and remove scoped locals from continuing and exit states.
    fn block(&mut self, span: &Span, statements: &Stmts, tail: &Option<Expr>) -> Option<Value> {
        let first_exit = self.exits.len();
        let block_path = self.path.clone();
        let mut locals = self.checked.scopes.get(&span.id).cloned().unwrap_or_default();
        if !locals.is_empty() {
            self.used.insert((checked::Kind::Scope, span.id));
        }
        for statement in statements.iter() {
            if !self.reachable {
                break;
            }
            let path = self.path.clone();
            let first_effect = self.effects.len();
            match &statement.x {
                StmtX::Expr(value) => {
                    self.value(value)?;
                }
                StmtX::Decl { pattern, init, .. } => {
                    if execution::ignored_statement(statement, self.modes) {
                        continue;
                    }
                    if matches!(pattern.x, PatternX::Wildcard) && contracts::scalar(&pattern.typ) {
                        if let Some(init) = init {
                            self.place_value(init, &pattern.typ)?;
                        }
                    } else {
                        let PatternX::Var(binding) = &pattern.x else {
                            return None;
                        };
                        let value = if let Some(init) = init {
                            self.place_value(init, &binding.typ)?
                        } else {
                            Value::Unknown
                        };
                        if self.reachable {
                            if binding.user_mut == Some(false)
                                && contracts::scalar(&binding.typ)
                                && let Some(init) = init
                            {
                                let init = crate::ast_util::place_to_spec_expr(init);
                                if let Ok(definition) = projections::spec_value(&init) {
                                    self.state.definitions.insert(binding.name.clone(), definition);
                                }
                            }
                            if !locals.contains(&binding.name) {
                                if matches!(value, Value::Owner(_)) {
                                    return None;
                                }
                                locals.push(binding.name.clone());
                            }
                            self.state.values.insert(binding.name.clone(), value);
                        }
                    }
                }
            }
            // Initializer exits still finish this statement's guarded effects;
            // the next visit to the statement loop handles unreachable suffixes.
            if !simplify::inspect::same_expression(&path, &block_path) {
                self.guard_effects(first_effect, &path);
            }
        }
        let path = self.path.clone();
        let first_effect = self.effects.len();
        let value = if self.reachable
            && let Some(tail) = tail
        {
            self.value(tail)?
        } else {
            Value::Unit
        };
        if !simplify::inspect::same_expression(&path, &block_path) {
            self.guard_effects(first_effect, &path);
        }
        for edge in &mut self.exits[first_exit..] {
            for local in &locals {
                edge.state.values.remove(local);
                edge.state.definitions.remove(local);
            }
        }
        for local in locals {
            self.state.values.remove(&local);
            self.state.definitions.remove(&local);
        }
        Some(value)
    }

    /// Dispatch executable expressions using checked ownership operations and exits.
    pub(super) fn value(&mut self, value: &Expr) -> Option<Value> {
        let span = &value.span;
        if let Some(inner) = model::widening_integer_cast(value) {
            let inner = self.scalar(inner)?;
            return Some(Value::Scalar(SpannedTyped::new(span, &value.typ, inner.x.clone())));
        }
        if execution::ignored_expression(value)
            || matches!(
                &value.x,
                ExprX::ResourceAssert(_)
                    | ExprX::ResourceAssertCurrent(_)
                    | ExprX::ResourceSection(_)
            )
        {
            return Some(Value::Unit);
        }
        if let Some(operation) = self.checked.operations.get(&span.id).cloned() {
            // Temporary wrappers may share a call's source span. Dispatch only
            // at the executable operation, so its operands are evaluated once.
            if matches!(&value.x, ExprX::Call { .. } | ExprX::Ctor(..)) {
                self.used.insert((checked::Kind::Operation, span.id));
                return self.operation(value, operation);
            }
        }
        match &value.x {
            ExprX::UnaryOpr(UnaryOpr::LoopIsolationBoundary(_), inner) => self.value(inner),
            ExprX::Const(_) => Some(Value::Scalar(value.clone())),
            ExprX::Var(name) => {
                if self.layouts.owner(&value.typ) {
                    None
                } else {
                    Some(self.state.values.get(name).cloned().unwrap_or(Value::Unknown))
                }
            }
            ExprX::ReadPlace(place, _) => self.place_value(place, &value.typ),
            ExprX::Block(statements, tail) => self.block(span, statements, tail),
            ExprX::If(condition, yes, no) => self.branch(span, condition, yes, no),
            ExprX::Match(scrutinee, arms, _) => self.match_value(span, scrutinee, arms),
            ExprX::Logical(op, left, right) => {
                let condition = self.scalar(left)?;
                let constant = crate::ast_util::mk_bool(span, *op != LogicalOp::And);
                if *op == LogicalOp::Or {
                    self.branch_from(span, condition, &constant, &Some(right.clone()))
                } else {
                    self.branch_from(span, condition, right, &Some(constant))
                }
            }
            ExprX::Assign { place, rhs, op, typ, .. } => {
                let value = self.value(rhs)?;
                if let Some(transition) = self.checked.assignments.get(&place.span.id).cloned() {
                    self.used.insert((checked::Kind::Assign, place.span.id));
                    let Value::Owner(child) = value else {
                        return None;
                    };
                    let location = self.checked_location(&transition.destination)?;
                    if let Some(input) = &transition.input {
                        self.replace_region(span, &location, input)?;
                    }
                    self.set(span, &location, child)?;
                } else if self.layouts.owner(typ) {
                    return None;
                } else if let PlaceX::Local(name) = &place.x {
                    let value = if let (Some(op), Value::Scalar(right)) = (op, &value) {
                        let Value::Scalar(left) = self.state.values.get(name)? else {
                            return None;
                        };
                        Value::Scalar(Self::binary(
                            span,
                            *op,
                            left.clone(),
                            right.clone(),
                            &rhs.typ,
                        ))
                    } else {
                        value
                    };
                    self.state.values.insert(name.clone(), value);
                } else {
                    return None;
                }
                Some(Value::Unit)
            }
            ExprX::Binary(op, left, right) => {
                let left = self.scalar(left)?;
                let right = self.scalar(right)?;
                Some(Value::Scalar(Self::binary(span, *op, left, right, &value.typ)))
            }
            ExprX::Unary(op, operand) => {
                let operand = self.scalar(operand)?;
                Some(Value::Scalar(SpannedTyped::new(span, &value.typ, ExprX::Unary(*op, operand))))
            }
            ExprX::UnaryOpr(op, operand) if contracts::scalar(&value.typ) => {
                let operand = self.scalar(operand)?;
                Some(Value::Scalar(SpannedTyped::new(
                    span,
                    &value.typ,
                    ExprX::UnaryOpr(op.clone(), operand),
                )))
            }
            ExprX::Ctor(..) if self.layouts.owner(&value.typ) => None,
            ExprX::Ctor(Dt::Tuple(0), _, fields, None) if fields.is_empty() => Some(Value::Unit),
            ExprX::Ctor(_, _, fields, None) => {
                for field in fields.iter() {
                    self.value(&field.a)?;
                }
                Some(Value::Unknown)
            }
            ExprX::ArrayLiteral(elements) => {
                for element in elements.iter() {
                    self.value(element)?;
                }
                Some(Value::Unknown)
            }
            ExprX::Call { .. } => None,
            ExprX::Loop { .. } => self.loop_value(span),
            ExprX::NeverToAny(inner) => self.value(inner),
            ExprX::Return(value) | ExprX::BreakOrContinue { value, .. } => {
                let target = self.checked.exits.get(&span.id)?.clone();
                self.used.insert((checked::Kind::Exit, span.id));
                let result = if let Some(value) = value { self.value(value)? } else { Value::Unit };
                if self.reachable {
                    self.exits.push(exits::Edge {
                        target,
                        condition: self.path.clone(),
                        state: self.state.clone(),
                        result,
                    });
                    self.reachable = false;
                }
                Some(Value::Unit)
            }
            _ => None,
        }
    }

    /// Use mathematical arithmetic in templates after body verification checks overflow.
    fn binary(span: &Span, op: BinaryOp, left: Expr, right: Expr, typ: &Typ) -> Expr {
        let op = match op {
            BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Error(_))) => {
                BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow))
            }
            BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Error(_))) => {
                BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Allow))
            }
            BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Error(_))) => {
                BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Allow))
            }
            _ => op,
        };
        SpannedTyped::new(span, typ, ExprX::Binary(op, left, right))
    }

    /// Assemble checked aggregate fields into one owner forest and reservation map.
    pub(super) fn construct(
        &mut self,
        value: &Expr,
        fields: Vec<(Expr, Option<OwnerSlot>)>,
        tag: u64,
    ) -> Option<Value> {
        let span = &value.span;
        let mut memory = expr::push(
            span,
            expr::empty(span, expr::record_type()),
            allocated(
                span,
                expr::integer(span, 0),
                expr::integer(span, 0),
                expr::integer(span, i128::from(tag)),
            ),
        );
        let mut minima = Minima::new();
        for (field, slot) in fields {
            let value = self.value(&field)?;
            if let Some(slot) = slot {
                let Value::Owner(child) = value else { return None };
                memory = expr::add(
                    span,
                    memory,
                    expr::prefix(
                        span,
                        child.memory,
                        expr::path(span, [self.layouts.metadata_slot(&slot)]),
                    ),
                );
                minima.extend(child.minima.into_iter().map(|(path, floor)| {
                    (std::iter::once(Step::Fixed(slot.clone())).chain(path).collect(), floor)
                }));
            }
        }
        Some(Value::Owner(Node { origin: None, typ: value.typ.clone(), memory, minima }))
    }
}
