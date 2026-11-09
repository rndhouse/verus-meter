//! Function entry and structural traversal of executable expressions/scopes.

use super::accounting::{Accounting, CheckKind, MemoryReport, Obligation, Peak};
use super::footprint::MemoryKind;
use super::layout::Layouts;
use super::model::{arithmetic, eligible, unit, unsupported};
use crate::ast::*;
use crate::messages::{Span, error};
use crate::resolution_inference::ResolutionInfo;
use std::collections::{HashMap, HashSet};

/// Checked facts and proof work awaiting publication by the crate-wide pass.
pub(super) struct FunctionAnalysis {
    /// Collected peaks and diagnostic events for this checked body.
    pub(super) report: MemoryReport,
    /// Call-composition facts published only after body accounting succeeds.
    pub(super) summary: super::summary::FunctionSummary,
    /// Executed direct call sites cross-checked against the canonical graph.
    pub(super) calls: Vec<(Fun, Span)>,
    /// Declared bound when it must be proved as a formula rather than a constant.
    pub(super) symbolic_bound: Option<Expr>,
    /// Memory inequalities to assert at their original execution sites.
    pub(super) obligations: Vec<Obligation>,
    /// Additional safety conditions, such as reserved vector capacity.
    pub(super) checks: Vec<(Span, Expr)>,
    /// Erased vector state and the proof instrumentation that maintains it.
    pub(super) growth: super::growth::Growth,
}

/// A cumulative bound and the history visible where it is asserted.
pub(super) struct Checkpoint {
    // The assertion location used for diagnostics.
    span: Span,
    // Maximum permitted cumulative model bytes at this assertion.
    budget: u64,
    // Historical cost points that can precede this assertion.
    peak: Peak,
}

/// One function's evolving ownership state and already checked callee facts.
pub(super) struct Analysis<'a> {
    /// Live named values, including their identities across moves.
    pub(super) slots: HashMap<VarIdent, super::lifetime::Value>,
    /// An expression result waiting to become a destination or return value.
    pub(super) produced: Option<super::lifetime::Value>,
    /// Completed callee facts, available because checking proceeds callee first.
    pub(super) summaries: &'a HashMap<Fun, super::summary::FunctionSummary>,
    /// Heap allocation retained by the expression currently producing an owner.
    pub(super) result_owner: Option<super::heap::Owner>,
    /// Declared budget envelopes used for lookup and conservative fallbacks.
    pub(super) budgets: &'a HashMap<Fun, u64>,
    /// Source-model sizes and supported ownership layouts.
    pub(super) layouts: &'a Layouts,
    /// Local declarations used to validate signatures and instantiate contracts.
    pub(super) functions: &'a HashMap<Fun, Function>,
    /// Resolved execution modes used to omit ghost storage and initializers.
    pub(super) var_modes: HashMap<VarIdent, Mode>,
    /// Current live charges, alternative paths, and accumulated peak history.
    pub(super) storage: Accounting,
    /// Executed direct call sites cross-checked against the canonical graph.
    pub(super) calls: Vec<(Fun, Span)>,
    /// Pending cumulative-peak assertions and the history visible at each site.
    pub(super) checkpoints: Vec<Checkpoint>,
    /// Immutable scalar names safe to reuse in generated budget formulas.
    pub(super) stable_scalars: HashSet<VarIdent>,
    /// Allocation ownership and restrictions on transfers across regions.
    pub(super) heap: super::heap::Heap,
    /// Memory inequalities to assert at their original execution sites.
    pub(super) obligations: Vec<Obligation>,
    /// Additional safety conditions, such as reserved vector capacity.
    pub(super) checks: Vec<(Span, Expr)>,
    /// Erased vector state and the proof instrumentation that maintains it.
    pub(super) growth: super::growth::Growth,
    /// Active function or section allowance used for inductive loop bounds.
    pub(super) bound: Expr,
}

impl Analysis<'_> {
    pub(super) fn discard(&mut self, expr: &Expr) -> Result<(), VirErr> {
        let result = self.expr(expr)?;
        self.storage.release(
            &expr.span,
            MemoryKind::host_local(),
            result,
            "consumed expression result",
        );
        Ok(())
    }

    pub(super) fn block(
        &mut self,
        expr: &Expr,
        stmts: &Stmts,
        tail: &Option<Expr>,
        destination: bool,
    ) -> Result<(), VirErr> {
        if let Some(stmt) = stmts.first() {
            if let StmtX::Expr(marker) = &stmt.x {
                if let ExprX::ResourceSection(budget) = &marker.x {
                    if !unit(&expr.typ) {
                        return Err(unsupported(&expr.span, "value-returning memory sections"));
                    }
                    return self.section(expr, &marker.span, budget, &stmts[1..], tail);
                }
            }
        }
        self.block_value(expr, stmts, tail, destination, false)
    }

    pub(super) fn block_contents(
        &mut self,
        expr: &Expr,
        stmts: &[Stmt],
        tail: &Option<Expr>,
    ) -> Result<(), VirErr> {
        self.block_value(expr, stmts, tail, false, false)
    }

    pub(super) fn block_new(
        &mut self,
        expr: &Expr,
        stmts: &Stmts,
        tail: &Option<Expr>,
    ) -> Result<(), VirErr> {
        self.block_value(expr, stmts, tail, false, true)
    }

    fn block_value(
        &mut self,
        expr: &Expr,
        stmts: &[Stmt],
        tail: &Option<Expr>,
        destination: bool,
        new_value: bool,
    ) -> Result<(), VirErr> {
        let mut locals = Vec::new();
        self.storage.event(&expr.span, "enter lexical scope".into());
        for stmt in stmts.iter() {
            match &stmt.x {
                StmtX::Expr(e) => self.discard(e)?,
                StmtX::Decl { pattern, init, els, .. } => {
                    if super::execution::ignored_statement(stmt, &self.var_modes) {
                        continue;
                    }
                    let PatternX::Var(binding) = &pattern.x else {
                        return Err(unsupported(
                            &stmt.span,
                            "destructuring or wildcard declarations",
                        ));
                    };
                    match self.var_modes.get(&binding.name) {
                        Some(Mode::Spec | Mode::Proof) => continue,
                        Some(Mode::Exec) => {}
                        None => {
                            return Err(unsupported(
                                &stmt.span,
                                "declarations without a resolved execution mode",
                            ));
                        }
                    }
                    if els.is_some()
                        || !matches!(binding.by_ref, ByRef::No)
                        || binding.user_mut.is_none()
                    {
                        return Err(unsupported(
                            &stmt.span,
                            "let-else, ref bindings, or generated declarations",
                        ));
                    }
                    if binding.user_mut == Some(false) && super::contracts::scalar(&binding.typ) {
                        self.stable_scalars.insert(binding.name.clone());
                    }
                    locals.push((stmt.span.clone(), binding.name.clone()));
                    let value = if let Some(init) = init {
                        self.produce_place(init, &binding.typ, binding.copy, &stmt.span)?
                    } else {
                        self.fresh_value(&stmt.span, &binding.typ)?
                    };
                    self.slots.insert(binding.name.clone(), value);
                    if self.layouts.owner(&binding.typ) {
                        let owner = self
                            .result_owner
                            .take()
                            .ok_or_else(|| unsupported(&stmt.span, "uninitialized heap owners"))?;
                        self.heap.owners.insert(binding.name.clone(), owner);
                    }
                }
            }
        }
        if let Some(tail) = tail {
            if new_value {
                self.produced = Some(self.produce(tail)?);
            } else if destination {
                self.initialize_expr(tail)?;
            } else {
                self.discard(tail)?;
            }
        }
        for (span, name) in locals.into_iter().rev() {
            self.drop_owner(&name, &span)?;
            if let Some(value) = self.slots.remove(&name) {
                self.release_value(value, &span);
            }
        }
        self.storage.event(&expr.span, "exit lexical scope".into());
        Ok(())
    }

    /// Evaluate source expressions. Only a standalone aggregate leaves a storage
    /// charge; scalar/reference operations introduce no implicit objects.
    pub(super) fn expr(&mut self, expr: &Expr) -> Result<u64, VirErr> {
        if self.layouts.owner(&expr.typ) {
            let value = self.produce(expr)?;
            let owner = self.result_owner.take().expect("produced owner");
            self.release_owner(owner, &expr.span);
            return self.expression_value(value, &expr.span);
        }
        if let Some(bytes) = self.value_expr(expr)? {
            return Ok(bytes);
        }
        if let Some(bytes) = self.vector_expr(expr)? {
            return Ok(bytes);
        }
        if let Some(bytes) = self.heap_expr(expr)? {
            return Ok(bytes);
        }
        if let Some(bytes) = self.construction(expr, false)? {
            return Ok(bytes);
        }
        let mut operands = 0u64;
        match &expr.x {
            ExprX::ResourceSection(_) => {
                return Err(unsupported(
                    &expr.span,
                    "section metadata outside the start of a block",
                ));
            }
            ExprX::ResourceAssert(budget) => {
                let budget = super::budget::evaluate_body_budget(
                    budget,
                    self.budgets,
                    self.functions,
                    self.layouts,
                )?;
                self.checkpoints.push(Checkpoint {
                    span: expr.span.clone(),
                    budget,
                    peak: self.storage.peak(),
                });
                return Ok(0);
            }
            _ if super::execution::ignored_expression(expr) => return Ok(0),
            ExprX::Block(stmts, tail) => {
                self.block(expr, stmts, tail, false)?;
                return Ok(0);
            }
            ExprX::Const(Constant::Bool(_) | Constant::Int(_)) => {}
            ExprX::Ctor(Dt::Tuple(0), _, fields, None) if fields.is_empty() => {}
            ExprX::ReadPlace(place, kind)
                if matches!(kind.preliminary_kind, ReadKind::Unused | ReadKind::UnusedCopy) =>
            {
                if let PlaceX::Temporary(value) = &place.x {
                    // Rust-to-VIR wraps non-unit expression statements in an
                    // unused temporary place. It is the expression's result,
                    // not an additional copy or a reference with extended lifetime.
                    return self.expr(value);
                }
                if matches!(kind.preliminary_kind, ReadKind::Unused)
                    && matches!(place.x, PlaceX::Local(_))
                {
                    let value = self.take_value(place)?;
                    self.release_value(value, &expr.span);
                    return Ok(0);
                }
                return self.read(place, &expr.typ);
            }
            ExprX::ReadPlace(place, kind)
                if matches!(kind.preliminary_kind, ReadKind::Move(_))
                    && crate::ast_util::types_equal(&place.typ, &expr.typ)
                    && matches!(place.x, PlaceX::Local(_)) =>
            {
                let value = self.take_value(place)?;
                self.release_value(value, &expr.span);
                return Ok(0);
            }
            ExprX::ReadPlace(place, kind) => {
                return if matches!(kind.preliminary_kind, ReadKind::ImmutBor) {
                    self.borrow(place, &expr.typ)
                } else {
                    self.read(place, &expr.typ)
                };
            }
            ExprX::BorrowMut(place) => return self.borrow(place, &expr.typ),
            ExprX::Unary(UnaryOp::Not, arg) => operands = self.expr(arg)?,
            ExprX::Binary(
                BinaryOp::Eq(Mode::Exec)
                | BinaryOp::Ne
                | BinaryOp::Inequality(_)
                | BinaryOp::BoolAndNoSC
                | BinaryOp::BoolOrNoSC
                | BinaryOp::BoolXor,
                lhs,
                rhs,
            ) => {
                let left = self.expr(lhs)?;
                let right = self.expr(rhs)?;
                operands = left.checked_add(right).expect("bounded by live total");
            }
            ExprX::Logical(LogicalOp::And | LogicalOp::Or, lhs, rhs) => {
                // Charge the RHS possibility even if the LHS is a constant.
                self.discard(lhs)?;
                operands = self.expr(rhs)?;
            }
            ExprX::Binary(..) if super::model::negative_literal(expr).is_some() => {}
            ExprX::Binary(op, lhs, rhs) if arithmetic(op) => {
                if !crate::ast_util::types_equal(&lhs.typ, &expr.typ)
                    || !crate::ast_util::types_equal(&rhs.typ, &expr.typ)
                {
                    return Err(unsupported(&expr.span, "mixed-type arithmetic"));
                }
                operands = self.expr(lhs)? + self.expr(rhs)?;
            }
            ExprX::Call { .. } => {
                let bytes = self.call_expr(expr, false)?;
                return if let Some(value) = self.produced.take() {
                    self.expression_value(value, &expr.span)
                } else {
                    Ok(bytes)
                };
            }
            ExprX::Match(scrutinee, arms, _) => {
                self.option_match(expr, scrutinee, arms, false)?;
                return Ok(0);
            }
            ExprX::Assign { place, rhs, op, typ, .. } => {
                if self.layouts.owner(typ) {
                    return Err(unsupported(&expr.span, "reassignment of heap owners"));
                }
                if op.as_ref().is_some_and(|op| !arithmetic(op)) {
                    return Err(unsupported(&expr.span, "this compound assignment"));
                }
                if let PlaceX::Local(name) = &place.x {
                    if self.slots.get(name).is_none_or(|v| v.bytes == 0) {
                        let value = self.produce(rhs)?;
                        self.slots.insert(name.clone(), value);
                    } else {
                        self.initialize_expr(rhs)?;
                    }
                } else {
                    self.initialize_expr(rhs)?;
                }
                self.access(place, typ)?;
                return Ok(0);
            }
            ExprX::If(cond, then_expr, else_expr) if unit(&expr.typ) => {
                self.conditional(expr, cond, then_expr, else_expr.as_ref(), false)?;
                return Ok(0);
            }
            ExprX::Loop {
                cond: Some(cond),
                body,
                source: LoopSource::Loop,
                is_for_loop: false,
                atomic_call: false,
                ..
            } if unit(&expr.typ) => {
                let loop_scalars = self.stable_scalars.clone();
                let entry = self.storage.live();
                let ids: Vec<_> = self
                    .heap
                    .owners
                    .values()
                    .filter_map(|o| o.vector)
                    .chain(self.heap.borrowed.values().copied())
                    .collect();
                let live = self.storage.live_expression(&expr.span).total();
                let protection = self.heap.protect();
                let first_checkpoint = self.checkpoints.len();
                self.storage.event(&expr.span, "analyze reusable while iteration".into());
                self.discard(cond)?;
                self.discard(body)?;
                assert_eq!(self.storage.live(), entry);
                // Every checkpoint may be reached after a previous complete
                // iteration. With reusable storage, one iteration's maximum is
                // the fixed point, including any nested loops or alternatives.
                let iteration_peak = self.storage.peak();
                for checkpoint in &mut self.checkpoints[first_checkpoint..] {
                    checkpoint.peak.merge(&iteration_peak);
                }
                self.heap.unprotect(protection);
                let mut invariants =
                    self.growth.invariants(&expr.span, &ids, &loop_scalars, &self.bound);
                invariants.push(crate::ast_util::mk_ineq(
                    &expr.span,
                    &live,
                    &self.bound,
                    InequalityOp::Le,
                ));
                self.growth.loops.insert(expr.span.id, invariants);
                return Ok(0);
            }
            _ => {
                return Err(unsupported(
                    &expr.span,
                    "this executable expression or control-flow exit",
                ));
            }
        }
        self.result(expr, operands)
    }

    pub(super) fn check_checkpoints(&mut self) -> Result<(), VirErr> {
        for checkpoint in &self.checkpoints {
            for (span, cost) in &checkpoint.peak.costs {
                self.obligations.push(Obligation {
                    span: span.clone(),
                    cost: cost.clone(),
                    bound: super::footprint::MemoryBudget::total(super::contracts::literal(
                        &checkpoint.span,
                        checkpoint.budget,
                    )),
                    kind: CheckKind::Checkpoint,
                });
            }
        }
        Ok(())
    }

    pub(super) fn result(&mut self, expr: &Expr, operands: u64) -> Result<u64, VirErr> {
        self.layouts.size(&expr.typ, &expr.span)?;
        self.storage.release(
            &expr.span,
            MemoryKind::host_local(),
            operands,
            "consumed aggregate operands",
        );
        Ok(0)
    }
}

pub(super) fn check(
    function: &Function,
    modes: Option<&ResolutionInfo>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
    budgets: &HashMap<Fun, u64>,
    summaries: &HashMap<Fun, super::summary::FunctionSummary>,
) -> Result<Option<FunctionAnalysis>, VirErr> {
    let Some(&budget) = budgets.get(&function.x.name) else {
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |_, expr| {
                if matches!(expr.x, ExprX::ResourceSection(_)) {
                    Err(error(
                        &expr.span,
                        "mem_peak sections require a function-level mem_peak contract",
                    ))
                } else if matches!(expr.x, ExprX::ResourceAssert(_)) {
                    Err(error(
                        &expr.span,
                        "mem_peak checkpoints require a function-level mem_peak contract",
                    ))
                } else {
                    Ok(())
                }
            })?;
        }
        return Ok(None);
    };
    let f = &function.x;
    eligible(function)?;
    let body = f
        .body
        .as_ref()
        .ok_or_else(|| unsupported(&function.span, "functions without a verified body"))?;
    let modes = modes.ok_or_else(|| {
        unsupported(&function.span, "functions without execution-mode information")
    })?;
    let mut analysis = Analysis {
        slots: HashMap::new(),
        produced: None,
        summaries,
        result_owner: None,
        budgets,
        layouts,
        functions,
        var_modes: modes.var_modes.clone(),
        storage: Accounting::new(&function.span, budget),
        calls: Vec::new(),
        checkpoints: Vec::new(),
        stable_scalars: super::contracts::inputs(function),
        heap: super::heap::Heap::default(),
        obligations: Vec::new(),
        checks: Vec::new(),
        growth: super::growth::Growth::default(),
        bound: super::contracts::function_bound(function, budgets, functions, layouts)?,
    };
    if f.outer_ret.x.mode != Mode::Exec {
        return Err(unsupported(&function.span, "ghost or tracked return values"));
    }
    layouts.return_size(&f.outer_ret.x.typ, &function.span)?;
    let capacities = super::inference::infer(
        function,
        layouts,
        summaries,
        functions,
        &analysis.bound,
        &modes.var_modes,
    )?;
    for (index, param) in f.params.iter().enumerate() {
        analysis.var_modes.insert(param.x.name.clone(), param.x.mode);
        if param.x.mode == Mode::Exec {
            if layouts.borrowed_vector(&param.x.typ).is_some() {
                if param.x.user_mut {
                    return Err(unsupported(
                        &param.span,
                        "mutable bindings for borrowed vector parameters",
                    ));
                }
            }
            if layouts.owner(&param.x.typ) {
                analysis.storage.add_input(index);
                analysis.heap.owners.insert(
                    param.x.name.clone(),
                    super::heap::Owner {
                        input: Some(index),
                        capacity: capacities.get(&param.x.name).cloned(),
                        ..Default::default()
                    },
                );
            }
            if layouts.vector(&param.x.typ) || layouts.borrowed_vector(&param.x.typ).is_some() {
                let typ = layouts.borrowed_vector(&param.x.typ).unwrap_or(&param.x.typ);
                let allocation = super::accounting::Accounting::fresh_allocation();
                let state = analysis.growth.new_vector(
                    &param.span,
                    capacities
                        .get(&param.x.name)
                        .cloned()
                        .unwrap_or_else(|| super::contracts::literal(&param.span, 0)),
                    super::footprint::Charge {
                        kind: MemoryKind::host_heap(),
                        amount: super::contracts::literal(&param.span, 0),
                    },
                    layouts.vector_element(typ, &param.span)?,
                    Some(index),
                    allocation,
                );
                analysis.growth.vectors[state].reserved = capacities.contains_key(&param.x.name);
                analysis.storage.set_allocation(
                    allocation,
                    MemoryKind::host_heap(),
                    analysis.growth.vectors[state].backing.bytes.clone(),
                );
                if let Some(owner) = analysis.heap.owners.get_mut(&param.x.name) {
                    owner.vector = Some(state);
                    owner.dynamic = Some(allocation);
                } else {
                    analysis.heap.borrowed.insert(param.x.name.clone(), state);
                }
            }
            let mut value = analysis.fresh_value(&param.span, &param.x.typ)?;
            value.parameter = Some(index);
            analysis.slots.insert(param.x.name.clone(), value);
        }
    }
    let symbolic_bound = super::symbolic::function_bound(function, budgets, functions, layouts)?;
    let result = analysis.produce(body)?;
    let return_parameter = result.parameter;
    let profiles = analysis
        .storage
        .points()
        .iter()
        .map(|p| super::lifetime::Profile {
            cost: p.cost.clone(),
            result: !p.values.is_disjoint(&result.origins),
            inputs: p.inputs.clone(),
        })
        .collect();
    let result_owner = analysis.result_owner.take();
    let (returned_capacity, replacement) = super::vector_calls::summarize_result(
        function,
        result_owner.as_ref(),
        &analysis.growth,
        &analysis.bound,
    )?;
    let returned = super::ownership::summarize(function, result_owner.as_ref(), replacement)?;
    analysis.check_checkpoints()?;
    let report = if symbolic_bound.is_some() {
        analysis.storage.finish_conditional()
    } else {
        analysis.storage.finish(&function.span)
    };
    let bound =
        symbolic_bound.clone().unwrap_or_else(|| super::contracts::literal(&function.span, budget));
    analysis.obligations.extend(report.cost_points.iter().map(|(span, cost)| Obligation {
        span: span.clone(),
        cost: cost.clone(),
        bound: super::footprint::MemoryBudget::total(bound.clone()),
        kind: CheckKind::Function,
    }));
    Ok(Some(FunctionAnalysis {
        report,
        summary: super::summary::FunctionSummary {
            vectors: super::vector_calls::VectorSummary {
                returned_capacity,
                reservations: f
                    .params
                    .iter()
                    .enumerate()
                    .filter_map(|(i, p)| capacities.get(&p.x.name).cloned().map(|c| (i, c)))
                    .collect(),
            },

            return_parameter,
            profiles,
            allocations: super::allocations::AllocationSummary {
                returned,
                retained: analysis
                    .heap
                    .borrowed
                    .values()
                    .filter_map(|id| {
                        let state = &analysis.growth.vectors[*id];
                        state.backing.changed.then(|| {
                            (
                                state.backing.input.unwrap(),
                                super::footprint::Charge {
                                    kind: state.backing.kind.clone(),
                                    amount: super::growth::retained_bound(
                                        state,
                                        function,
                                        &analysis.bound,
                                    ),
                                },
                            )
                        })
                    })
                    .collect(),
            },
        },
        calls: analysis.calls,
        symbolic_bound,
        obligations: analysis.obligations,
        checks: analysis.checks,
        growth: analysis.growth,
    }))
}
