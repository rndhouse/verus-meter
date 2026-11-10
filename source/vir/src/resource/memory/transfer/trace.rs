//! Interpret only the ownership-relevant, pure portion of a checked body.
//! Unsupported value dependencies or reusable mutations decline precision.

mod operations;

use super::*;
use crate::ast_util::{bool_typ, int_typ, mk_eq, mk_ineq};
use crate::messages::Span;
use crate::resource::memory::{
    contracts, growth,
    heap::OwnerSlot,
    metadata::reservations::{Step, join_minima},
};
use std::collections::HashSet;
use std::sync::Arc;

type Location = (VarIdent, Vec<OwnerSlot>, Vec<Expr>);

#[derive(Clone, Default)]
struct State {
    values: HashMap<VarIdent, Value>,
    written: HashSet<VarIdent>,
}

struct Trace<'a> {
    layouts: &'a super::super::layout::Layouts,
    functions: &'a HashMap<Fun, Function>,
    summaries: &'a HashMap<Fun, super::super::summary::FunctionSummary>,
    modes: &'a HashMap<VarIdent, Mode>,
    state: State,
    symbols: Vec<Symbol>,
    appends: bool,
}

pub(super) fn summarize(
    function: &Function,
    layouts: &super::super::layout::Layouts,
    functions: &HashMap<Fun, Function>,
    summaries: &HashMap<Fun, super::super::summary::FunctionSummary>,
    modes: &HashMap<VarIdent, Mode>,
) -> Option<Template> {
    let mut trace = Trace {
        layouts,
        functions,
        summaries,
        modes,
        state: State::default(),
        symbols: vec![],
        appends: false,
    };
    for (index, parameter) in function.x.params.iter().enumerate() {
        if parameter.x.mode != Mode::Exec {
            continue;
        }
        let typ = layouts.borrowed_owner(&parameter.x.typ).unwrap_or(&parameter.x.typ);
        let value = if layouts.owner(typ) {
            let memory = trace.symbol(&parameter.span, Input::Forest(index), expr::memory_type());
            let memory = trace.input_memory(&parameter.span, index, typ, &memory, &mut vec![])?;
            let mut minima = Minima::new();
            trace.input_minima(&parameter.span, index, typ, &mut vec![], &mut minima)?;
            Value::Owner(Node { typ: typ.clone(), memory, minima })
        } else if contracts::scalar(typ) {
            Value::Scalar(trace.symbol(&parameter.span, Input::Scalar(index), typ.clone()))
        } else {
            Value::Unknown
        };
        trace.state.values.insert(parameter.x.name.clone(), value);
    }
    let result = trace.value(function.x.body.as_ref()?)?;
    if layouts.owner(&function.x.outer_ret.x.typ) && !matches!(result, Value::Owner(_)) {
        return None;
    }
    let mut borrowed = BTreeMap::new();
    for (index, parameter) in function.x.params.iter().enumerate() {
        if matches!(&*parameter.x.typ, TypX::MutRef(_))
            && trace.state.written.contains(&parameter.x.name)
        {
            let Value::Owner(node) = trace.state.values.get(&parameter.x.name)? else {
                continue;
            };
            borrowed.insert(index, node.clone());
        }
    }
    // Unused scalar arguments need no snapshot or additional representability restriction.
    let mut names = HashSet::new();
    let mut collect = |value: &Expr| {
        let _ = crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
            if let ExprX::Var(name) = &value.x {
                names.insert(name.clone());
            }
            Ok::<(), VirErr>(())
        });
    };
    for node in borrowed.values().chain(match &result {
        Value::Owner(node) => Some(node),
        _ => None,
    }) {
        collect(&node.memory);
        for floor in node.minima.values() {
            collect(&floor.capacity);
        }
    }
    if let Value::Scalar(value) = &result {
        collect(value);
    }
    trace.symbols.retain(|symbol| names.contains(&symbol.name));
    Some(Template { symbols: trace.symbols, appends: trace.appends, borrowed, result })
}

impl Trace<'_> {
    /// Fixed ownership is finite even when runtime children have unbounded
    /// depth. Keep the fixed descriptors explicit so composing helpers does
    /// not repeatedly select scalar properties from an opaque whole forest.
    fn input_memory(
        &mut self,
        span: &Span,
        parameter: usize,
        typ: &Typ,
        forest: &Expr,
        path: &mut Vec<OwnerSlot>,
    ) -> Option<Expr> {
        let mut property =
            |field| self.symbol(span, Input::Property(parameter, path.clone(), field), int_typ());
        let bytes = property("bytes");
        let capacity = property("capacity");
        let length = property("length");
        let mut memory = expr::push(
            span,
            expr::empty(span, expr::record_type()),
            allocated(span, bytes, capacity, length),
        );
        for (slot, child) in self.layouts.owned_children(typ, span).ok()? {
            path.push(slot.clone());
            let child = self.input_memory(span, parameter, &child, forest, path)?;
            path.pop();
            memory = expr::add(
                span,
                memory,
                expr::prefix(span, child, expr::path(span, [self.layouts.metadata_slot(&slot)])),
            );
        }
        if self.layouts.owning_elements(typ) {
            let selected = path.iter().fold(forest.clone(), |memory, slot| {
                expr::subtree(span, memory, expr::path(span, [self.layouts.metadata_slot(slot)]))
            });
            memory = expr::add(
                span,
                memory,
                expr::operation(span, "runtime", vec![selected], expr::memory_type()),
            );
        }
        Some(memory)
    }

    fn symbol(&mut self, span: &Span, input: Input, typ: Typ) -> Expr {
        let name = VarIdent(
            Arc::new("$memory_transfer_input".into()),
            VarIdentDisambiguate::VirTemp(super::super::accounting::Accounting::fresh_allocation()),
        );
        self.symbols.push(Symbol { name: name.clone(), input });
        SpannedTyped::new(span, &typ, ExprX::Var(name))
    }

    fn input_minima(
        &mut self,
        span: &Span,
        parameter: usize,
        typ: &Typ,
        path: &mut Vec<Step>,
        result: &mut Minima,
    ) -> Option<()> {
        if self.layouts.vector(typ) {
            let capacity = self.symbol(span, Input::Minimum(parameter, path.clone()), int_typ());
            result.insert(
                path.clone(),
                Floor { capacity, element: self.layouts.vector_element(typ, span).ok()? },
            );
        }
        for (slot, child) in self.layouts.owned_children(typ, span).ok()? {
            path.push(Step::Fixed(slot));
            self.input_minima(span, parameter, &child, path, result)?;
            path.pop();
        }
        if let Some(child) = self.element_type(typ) {
            if self.layouts.owner(&child) {
                path.push(Step::Repeated);
                self.input_minima(span, parameter, &child, path, result)?;
                path.pop();
            }
        }
        Some(())
    }

    fn element_type(&self, typ: &Typ) -> Option<Typ> {
        if self.layouts.vector(typ) {
            let TypX::Datatype(_, types, _) = &**typ else {
                return None;
            };
            return types.first().cloned();
        }
        if let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            if let TypX::Primitive(Primitive::Slice, types) = &**inner {
                return types.first().cloned();
            }
        }
        None
    }

    fn scalar(&mut self, value: &Expr) -> Option<Expr> {
        match self.value(value)? {
            Value::Scalar(value) => Some(value),
            _ => None,
        }
    }

    fn indices_expr(&mut self, value: &Expr, result: &mut HashMap<u64, Expr>) -> Option<()> {
        if let Some(args) = super::super::paths::vector_index(value) {
            self.indices_expr(&args[0], result)?;
            result.insert(value.span.id, self.scalar(&args[1])?);
        } else {
            match &value.x {
                ExprX::ReadPlace(place, _)
                | ExprX::BorrowMut(place)
                | ExprX::TwoPhaseBorrowMut(place) => self.indices_place(place, result)?,
                ExprX::UnaryOpr(UnaryOpr::Field(_), base)
                | ExprX::Unary(UnaryOp::MutRefCurrent, base) => self.indices_expr(base, result)?,
                _ => {}
            }
        }
        Some(())
    }

    fn indices_place(&mut self, place: &Place, result: &mut HashMap<u64, Expr>) -> Option<()> {
        match &place.x {
            PlaceX::Temporary(value) => self.indices_expr(value, result)?,
            PlaceX::Field(_, base) | PlaceX::DerefMut(base) => self.indices_place(base, result)?,
            PlaceX::Index(base, index, _, _) => {
                self.indices_place(base, result)?;
                result.insert(place.span.id, self.scalar(index)?);
            }
            _ => {}
        }
        Some(())
    }

    fn location(&mut self, value: &Expr, typ: &Typ) -> Option<Location> {
        let (name, path) = super::super::paths::expr(value, typ)?;
        let mut indices = HashMap::new();
        self.indices_expr(value, &mut indices)?;
        let expressions = path
            .iter()
            .map(|slot| match slot {
                OwnerSlot::Element(id) => indices.get(id).cloned(),
                _ => Some(expr::integer(&value.span, self.layouts.metadata_slot(slot))),
            })
            .collect::<Option<Vec<_>>>()?;
        Some((name, path, expressions))
    }

    fn place_location(&mut self, place: &Place, typ: &Typ) -> Option<Location> {
        let value = SpannedTyped::new(
            &place.span,
            &place.typ,
            ExprX::ReadPlace(
                place.clone(),
                UnfinalizedReadKind { preliminary_kind: ReadKind::Copy, id: 0 },
            ),
        );
        self.location(&value, typ)
    }

    fn path(span: &Span, steps: &[Expr]) -> Expr {
        steps.iter().fold(expr::path(span, []), |path, step| expr::push(span, path, step.clone()))
    }

    fn class(path: &[OwnerSlot]) -> Vec<Step> {
        path.iter()
            .map(|slot| match slot {
                OwnerSlot::Element(_) => Step::Repeated,
                _ => Step::Fixed(slot.clone()),
            })
            .collect()
    }

    fn get(&self, span: &Span, location: &Location, typ: &Typ) -> Option<Node> {
        let Value::Owner(root) = self.state.values.get(&location.0)? else {
            return None;
        };
        let class = Self::class(&location.1);
        let minima = root
            .minima
            .iter()
            .filter_map(|(path, floor)| {
                path.strip_prefix(class.as_slice()).map(|rest| (rest.to_vec(), floor.clone()))
            })
            .collect();
        // Select one ownership edge at a time, matching the finite projection
        // algebra used by local borrows. A repeated edge can then expose the
        // fixed layout below it without flattening arbitrary composite paths.
        let memory = location.2.iter().fold(root.memory.clone(), |memory, step| {
            expr::subtree(span, memory, Self::path(span, std::slice::from_ref(step)))
        });
        Some(Node { typ: typ.clone(), memory, minima })
    }

    fn set(&mut self, span: &Span, location: &Location, child: Node) -> Option<()> {
        if location.1.is_empty() {
            self.state.values.insert(location.0.clone(), Value::Owner(child));
        } else {
            let Value::Owner(root) = self.state.values.get_mut(&location.0)? else {
                return None;
            };
            let mut parents = Vec::new();
            let mut selected = root.memory.clone();
            for step in &location.2 {
                let path = Self::path(span, std::slice::from_ref(step));
                parents.push((selected.clone(), path.clone()));
                selected = expr::subtree(span, selected, path);
            }
            root.memory = parents.into_iter().rev().fold(child.memory, |memory, (parent, path)| {
                expr::operation(span, "replace", vec![parent, path, memory], expr::memory_type())
            });
            let class = Self::class(&location.1);
            if !class.iter().any(|step| matches!(step, Step::Repeated)) {
                root.minima.retain(|path, _| !path.starts_with(&class));
            }
            let child = child
                .minima
                .into_iter()
                .map(|(path, floor)| (class.iter().cloned().chain(path).collect(), floor))
                .collect();
            join_minima(span, &mut root.minima, &child);
        }
        self.state.written.insert(location.0.clone());
        Some(())
    }

    fn take(&mut self, span: &Span, location: &Location, typ: &Typ) -> Option<Node> {
        let child = self.get(span, location, typ)?;
        if location.1.is_empty() {
            self.state.values.remove(&location.0);
        } else {
            self.set(
                span,
                location,
                Node {
                    typ: typ.clone(),
                    memory: expr::empty(span, expr::record_type()),
                    minima: Minima::new(),
                },
            )?;
        }
        Some(child)
    }

    fn receiver(&mut self, value: &Expr) -> Option<(Location, Node)> {
        let mut typ = super::super::paths::referent(&value.typ);
        while let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            typ = inner;
        }
        let location = self.location(value, typ)?;
        let owner = self.get(&value.span, &location, typ)?;
        Some((location, owner))
    }

    fn block(&mut self, statements: &Stmts, tail: &Option<Expr>) -> Option<Value> {
        let mut locals = Vec::new();
        for statement in statements.iter() {
            match &statement.x {
                StmtX::Expr(value) => {
                    self.value(value)?;
                }
                StmtX::Decl { pattern, init, .. } => {
                    if super::super::execution::ignored_statement(statement, self.modes) {
                        continue;
                    }
                    let PatternX::Var(binding) = &pattern.x else {
                        return None;
                    };
                    let value = if let Some(init) = init {
                        self.place_value(init)?
                    } else {
                        Value::Unknown
                    };
                    self.state.values.insert(binding.name.clone(), value);
                    locals.push(binding.name.clone());
                }
            }
        }
        let value = if let Some(tail) = tail { self.value(tail)? } else { Value::Unit };
        for local in locals {
            self.state.values.remove(&local);
        }
        Some(value)
    }

    fn place_value(&mut self, place: &Place) -> Option<Value> {
        if let PlaceX::Temporary(value) = &place.x {
            return self.value(value);
        }
        if self.layouts.owner(&place.typ) {
            let location = self.place_location(place, &place.typ)?;
            return Some(Value::Owner(self.take(&place.span, &location, &place.typ)?));
        }
        if let PlaceX::Local(name) = &place.x {
            return Some(self.state.values.get(name).cloned().unwrap_or(Value::Unknown));
        }
        self.place_effects(place)?;
        Some(Value::Unknown)
    }

    fn place_effects(&mut self, place: &Place) -> Option<()> {
        match &place.x {
            PlaceX::Temporary(value) => {
                self.value(value)?;
            }
            PlaceX::Field(_, base) | PlaceX::DerefMut(base) => self.place_effects(base)?,
            PlaceX::Index(base, index, _, _) => {
                self.place_effects(base)?;
                self.value(index)?;
            }
            PlaceX::Local(_) => {}
            _ => return None,
        }
        Some(())
    }

    fn value(&mut self, value: &Expr) -> Option<Value> {
        let span = &value.span;
        if super::super::execution::ignored_expression(value)
            || matches!(
                &value.x,
                ExprX::ResourceAssert(_)
                    | ExprX::ResourceAssertCurrent(_)
                    | ExprX::ResourceSection(_)
            )
        {
            return Some(Value::Unit);
        }
        match &value.x {
            ExprX::Const(_) => Some(Value::Scalar(value.clone())),
            ExprX::Var(name) => {
                if self.layouts.owner(&value.typ) {
                    let location = self.location(value, &value.typ)?;
                    Some(Value::Owner(self.take(span, &location, &value.typ)?))
                } else {
                    Some(self.state.values.get(name).cloned().unwrap_or(Value::Unknown))
                }
            }
            ExprX::ReadPlace(place, _) => self.place_value(place),
            ExprX::Block(statements, tail) => self.block(statements, tail),
            ExprX::If(condition, yes, no) => self.branch(span, condition, yes, no),
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
                if self.layouts.owner(typ) {
                    let Value::Owner(child) = value else {
                        return None;
                    };
                    let location = self.place_location(place, typ)?;
                    self.set(span, &location, child)?;
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
                if let UnaryOp::Length(_) = op {
                    let typ = super::super::paths::referent(&operand.typ);
                    let location = self.location(operand, typ)?;
                    return Some(Value::Scalar(property(
                        span,
                        self.get(span, &location, typ)?.memory,
                        "length",
                    )));
                }
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
            ExprX::Ctor(_, variant, fields, None) if self.layouts.owner(&value.typ) => {
                self.construct(value, variant, fields)
            }
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
            ExprX::Call { target: CallTarget::Fun(_, target, _, _, attrs), args, .. } => {
                self.call(value, target, attrs.resource_intrinsic, args)
            }
            ExprX::Loop { body, cond, .. } => {
                // A read-only traversal can preserve ownership even when its
                // scalar result cannot be expressed by a finite template.
                let mut effects = false;
                for region in cond.iter().chain(std::iter::once(body)) {
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
            _ => None,
        }
    }

    fn binary(span: &Span, op: BinaryOp, left: Expr, right: Expr, typ: &Typ) -> Expr {
        let op = match op {
            BinaryOp::Arith(ArithOp::Add(_)) => {
                BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow))
            }
            BinaryOp::Arith(ArithOp::Sub(_)) => {
                BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Allow))
            }
            BinaryOp::Arith(ArithOp::Mul(_)) => {
                BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Allow))
            }
            _ => op,
        };
        SpannedTyped::new(span, typ, ExprX::Binary(op, left, right))
    }

    fn branch(
        &mut self,
        span: &Span,
        condition: &Expr,
        yes: &Expr,
        no: &Option<Expr>,
    ) -> Option<Value> {
        let condition = self.scalar(condition)?;
        self.branch_from(span, condition, yes, no)
    }

    fn branch_from(
        &mut self,
        span: &Span,
        condition: Expr,
        yes: &Expr,
        no: &Option<Expr>,
    ) -> Option<Value> {
        let before = self.state.clone();
        let yes_value = self.value(yes)?;
        let yes = self.state.clone();
        self.state = before;
        let no_value = if let Some(no) = no { self.value(no)? } else { Value::Unit };
        let no = self.state.clone();
        if yes.values.keys().collect::<HashSet<_>>() != no.values.keys().collect::<HashSet<_>>() {
            return None;
        }
        self.state.values = yes
            .values
            .iter()
            .map(|(name, left)| {
                Some((
                    name.clone(),
                    Self::join_value(span, condition.clone(), left, &no.values[name])?,
                ))
            })
            .collect::<Option<_>>()?;
        self.state.written.extend(yes.written);
        self.state.written.extend(no.written);
        Self::join_value(span, condition, &yes_value, &no_value)
    }

    fn join_value(span: &Span, condition: Expr, yes: &Value, no: &Value) -> Option<Value> {
        Some(match (yes, no) {
            (Value::Owner(yes), Value::Owner(no)) => {
                let mut minima = yes.minima.clone();
                join_minima(span, &mut minima, &no.minima);
                Value::Owner(Node {
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

    fn construct(
        &mut self,
        value: &Expr,
        variant: &Ident,
        fields: &Binders<Expr>,
    ) -> Option<Value> {
        let span = &value.span;
        let mut memory = expr::push(
            span,
            expr::empty(span, expr::record_type()),
            allocated(
                span,
                expr::integer(span, 0),
                expr::integer(span, 0),
                expr::integer(
                    span,
                    i128::from(self.layouts.option(&value.typ) && variant.as_str() == "Some"),
                ),
            ),
        );
        let mut minima = Minima::new();
        for field in fields.iter() {
            if let Value::Owner(child) = self.value(&field.a)? {
                let slot = if self.layouts.option(&value.typ) {
                    OwnerSlot::Contents
                } else {
                    OwnerSlot::Field(field.name.clone())
                };
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
        Some(Value::Owner(Node { typ: value.typ.clone(), memory, minima }))
    }
}
