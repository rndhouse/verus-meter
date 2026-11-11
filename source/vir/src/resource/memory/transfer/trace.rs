//! Specialize checked ownership transitions into parametric forests.
//!
//! Source syntax supplies scalar expressions and control flow. Ownership rules,
//! layout sizes, and resolved paths come exclusively from body accounting; a
//! template is exported only after every recorded transition is consumed.
//! Unrepresentable effects fail inference; runtime ownership interfaces then
//! report unsupported instead of exporting a byte-only approximation.

mod loops;
mod operations;
mod patterns;
mod provenance;

#[cfg(test)]
mod tests;

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

use super::effects::{Effect, Location};

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
    /// Authoritative operation decisions made by body accounting.
    checked: &'a Checked,
    /// Whole-body coverage, including branches and representative loop bodies.
    used: HashSet<(checked::Kind, u64)>,
    state: State,
    symbols: Vec<Symbol>,
    /// Immutable allocation regions addressed by body lifetime identities.
    regions: BTreeMap<usize, Expr>,
    /// Effects on persistent owners distinguish collection regions from
    /// temporary child construction during a representative loop iteration.
    effects: Vec<Effect>,
    /// Pattern branches keep unsupported mutations opaque; `if` branches record
    /// explicit guards instead.
    branch_depth: usize,
    /// Temporary payload symbols expose data flow within one iteration. They
    /// must be eliminated by the loop summary, never exported as free symbols.
    loop_tokens: Option<HashSet<VarIdent>>,
    /// Only persistent roles need range tokens; temporary construction keeps
    /// its concrete forest so it can compose as fresh output.
    loop_roots: Option<HashSet<VarIdent>>,
    /// Structural transfers from completed loop graphs. No proof expressions
    /// are constructed here; evidence is published only with a complete template.
    loop_transfers: HashMap<u64, Vec<super::super::loops::Transfer>>,
    /// Per-role append envelopes, expressed in ordinary immutable inputs.
    loop_growth: HashMap<u64, Vec<(super::super::paths::LocalPath, Expr)>>,
    /// Convert immutable symbolic inputs back into body-proof observations.
    proof_values: HashMap<VarIdent, Expr>,
}

pub(super) fn summarize(
    function: &Function,
    layouts: &super::super::layout::Layouts,
    functions: &HashMap<Fun, Function>,
    summaries: &HashMap<Fun, super::super::summary::FunctionSummary>,
    modes: &HashMap<VarIdent, Mode>,
    checked: &Checked,
) -> Option<Inferred> {
    let mut trace = Trace {
        layouts,
        functions,
        summaries,
        modes,
        checked,
        used: HashSet::new(),
        state: State::default(),
        symbols: vec![],
        regions: BTreeMap::new(),
        effects: vec![],
        branch_depth: 0,
        loop_tokens: None,
        loop_roots: None,
        loop_transfers: HashMap::new(),
        loop_growth: HashMap::new(),
        proof_values: HashMap::new(),
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
            Value::Owner(Node { origin: Some(index), typ: typ.clone(), memory, minima })
        } else if contracts::scalar(typ) {
            let symbol = trace.symbol(&parameter.span, Input::Scalar(index), typ.clone());
            let ExprX::Var(name) = &symbol.x else { unreachable!() };
            trace.proof_values.insert(
                name.clone(),
                SpannedTyped::new(&parameter.span, typ, ExprX::Var(parameter.x.name.clone())),
            );
            Value::Scalar(symbol)
        } else {
            Value::Unknown
        };
        trace.state.values.insert(parameter.x.name.clone(), value);
    }
    trace.initialize_regions(function)?;
    let result = trace.value(function.x.body.as_ref()?)?;
    if !checked.covered(&trace.used) {
        return None;
    }
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
    let effects = trace.parameter_effects(function, &result);
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
    trace.regions.retain(|id, _| *id >= checked.inputs.len());
    for region in trace.regions.values() {
        collect(region);
    }
    if let Some(effects) = &effects {
        for (_, effect) in effects {
            effect.expressions(&mut collect);
        }
    }
    // A template may refer only to caller observations. In particular, a
    // representative iteration's counter and extracted-child tokens cannot
    // escape through intermediate lifetime regions or returned descriptors.
    if names.iter().any(|name| !trace.symbols.iter().any(|symbol| &symbol.name == name)) {
        return None;
    }
    trace.symbols.retain(|symbol| names.contains(&symbol.name));
    Some(Inferred {
        loops: trace.loop_transfers,
        growth: trace.loop_growth,
        template: Template {
            regions: trace.regions,
            symbols: trace.symbols,
            effects,
            borrowed,
            result,
        },
    })
}

impl Trace<'_> {
    /// Export only checked, parameter-relative effects. Captured input forests
    /// in a payload require a transfer relation, not repeated fresh construction.
    fn parameter_effects(
        &self,
        function: &Function,
        result: &Value,
    ) -> Option<Vec<(usize, Effect)>> {
        let closed = |value: &Expr| {
            let mut closed = true;
            let _ = crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
                if let ExprX::Var(name) = &value.x {
                    closed &= self.symbols.iter().any(|symbol| {
                        &symbol.name == name && matches!(symbol.input, Input::Scalar(_))
                    });
                }
                Ok::<(), VirErr>(())
            });
            closed
        };
        if let Value::Owner(node) = result {
            if node.origin.is_none() && !closed(&node.memory) {
                return None;
            }
        }
        let mut effects = Vec::new();
        for effect in &self.effects {
            let Some(index) = function.x.params.iter().position(|parameter| {
                matches!(&*parameter.x.typ, TypX::MutRef(_)) && &parameter.x.name == effect.root()
            }) else {
                continue;
            };
            if !effect.exportable() {
                return None;
            }
            fn valid(effect: &Effect, closed: &impl Fn(&Expr) -> bool) -> bool {
                match effect {
                    Effect::Guarded { condition, effect, .. } => {
                        closed(condition) && valid(effect, closed)
                    }
                    Effect::Append {
                        child: Value::Owner(Node { origin: Some(_), .. }), ..
                    } => true,
                    _ => {
                        let mut valid = true;
                        effect.expressions(&mut |value| valid &= closed(value));
                        valid
                    }
                }
            }
            if !valid(effect, &closed) {
                return None;
            }
            effects.push((index, effect.clone()));
        }
        Some(effects)
    }

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

    fn checked_location(&mut self, place: &checked::Place) -> Option<Location> {
        let (name, path) = &place.location;
        let mut indices = HashMap::new();
        self.indices_expr(&place.source, &mut indices)?;
        let expressions = path
            .iter()
            .map(|slot| match slot {
                OwnerSlot::Element(id) => indices.get(id).cloned(),
                _ => Some(expr::integer(&place.source.span, self.layouts.metadata_slot(slot))),
            })
            .collect::<Option<Vec<_>>>()?;
        Some((name.clone(), path.clone(), expressions))
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
        Some(Node {
            origin: if location.1.is_empty() { root.origin } else { None },
            typ: typ.clone(),
            memory,
            minima,
        })
    }

    fn set(&mut self, span: &Span, location: &Location, child: Node) -> Option<()> {
        self.effects.push(Effect::Mutation(location.0.clone()));
        if location.1.is_empty() {
            self.state.values.insert(location.0.clone(), Value::Owner(child));
        } else {
            let Value::Owner(root) = self.state.values.get_mut(&location.0)? else {
                return None;
            };
            root.origin = None;
            let mut parents = Vec::new();
            let mut selected = root.memory.clone();
            for step in &location.2 {
                let path = Self::path(span, std::slice::from_ref(step));
                parents.push((selected.clone(), path.clone()));
                selected = expr::subtree(span, selected, path);
            }
            root.memory = parents.into_iter().rev().fold(child.memory, |memory, (parent, path)| {
                super::super::metadata::operations::replace(span, parent, path, memory)
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
            self.effects.push(Effect::Mutation(location.0.clone()));
            self.state.values.remove(&location.0);
        } else {
            self.set(
                span,
                location,
                Node {
                    origin: None,
                    typ: typ.clone(),
                    memory: expr::empty(span, expr::record_type()),
                    minima: Minima::new(),
                },
            )?;
        }
        Some(child)
    }

    fn block(&mut self, span: &Span, statements: &Stmts, tail: &Option<Expr>) -> Option<Value> {
        let mut locals = self.checked.scopes.get(&span.id).cloned().unwrap_or_default();
        if !locals.is_empty() {
            self.used.insert((checked::Kind::Scope, span.id));
        }
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
                        self.place_value(init, &binding.typ)?
                    } else {
                        Value::Unknown
                    };
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
        let value = if let Some(tail) = tail { self.value(tail)? } else { Value::Unit };
        for local in locals {
            self.state.values.remove(&local);
        }
        Some(value)
    }

    fn place_value(&mut self, place: &Place, typ: &Typ) -> Option<Value> {
        if let PlaceX::Temporary(value) = &place.x {
            return self.value(value);
        }
        if let Some(transition) = self.checked.moves.get(&place.span.id).cloned() {
            self.used.insert((checked::Kind::Move, place.span.id));
            let location = self.checked_location(&transition)?;
            return Some(Value::Owner(self.take(&place.span, &location, &transition.typ)?));
        }
        if self.layouts.owner(typ) {
            return None;
        }
        // A scalar read through a box does not consume the outer owner. Its
        // value may be irrelevant to ownership inference, but its actual result
        // type must govern this decision rather than the enclosing place type.
        if let PlaceX::Local(name) = &place.x {
            return Some(match self.state.values.get(name) {
                Some(Value::Owner(_)) => Value::Unknown,
                value => value.cloned().unwrap_or(Value::Unknown),
            });
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
        if let Some(operation) = self.checked.operations.get(&span.id).cloned() {
            // Temporary wrappers may share a call's source span. Dispatch only
            // at the executable operation, so its operands are evaluated once.
            if matches!(&value.x, ExprX::Call { .. } | ExprX::Ctor(..)) {
                self.used.insert((checked::Kind::Operation, span.id));
                return self.operation(value, operation);
            }
        }
        match &value.x {
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
            _ => None,
        }
    }

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
        let effect_start = self.effects.len();
        let yes_value = self.value(yes)?;
        let yes = self.state.clone();
        let yes_effects = self.effects.split_off(effect_start);
        self.state = before;
        let no_value = if let Some(no) = no { self.value(no)? } else { Value::Unit };
        let no = self.state.clone();
        let no_effects = self.effects.split_off(effect_start);
        self.state = Self::join_state(span, condition.clone(), yes, no)?;
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
        Self::join_value(span, condition, &yes_value, &no_value)
    }

    fn join_state(span: &Span, condition: Expr, yes: State, no: State) -> Option<State> {
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
        let mut written = yes.written;
        written.extend(no.written);
        Some(State { values, written })
    }

    fn join_value(span: &Span, condition: Expr, yes: &Value, no: &Value) -> Option<Value> {
        Some(match (yes, no) {
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

    fn construct(
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
