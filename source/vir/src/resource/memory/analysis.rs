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
    /// Historical cost points that can precede this assertion.
    pub(super) peak: Peak,
}

/// One function's evolving ownership state and already checked callee facts.
pub(super) struct Analysis<'a> {
    /// Executable ownership transitions accepted by this body's accounting.
    pub(super) transitions: super::transfer::Checked,
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
    /// Disjoint owned input nodes, indexed by lifetime provenance ID.
    pub(super) input_paths: Vec<super::paths::InputPath>,
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
        let mut owned_locals = Vec::new();
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
                        owned_locals.push(binding.name.clone());
                        let mut owner = self
                            .result_owner
                            .take()
                            .ok_or_else(|| unsupported(&stmt.span, "uninitialized heap owners"))?;
                        let value = SpannedTyped::new(
                            &stmt.span,
                            &binding.typ,
                            ExprX::Var(binding.name.clone()),
                        );
                        self.bind_collection_sources(&stmt.span, &mut owner, &binding.typ, value)?;
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
        if !owned_locals.is_empty() {
            self.transitions.scope(&expr.span, owned_locals);
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
        if let Some(owner) = self.extracted_owner(expr, true)? {
            self.release_owner(owner, &expr.span);
            return Ok(0);
        }
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
            ExprX::ResourceAssertCurrent(budget) => {
                let budget = super::budget::evaluate_body_budget(
                    budget,
                    self.budgets,
                    self.functions,
                    self.layouts,
                )?;
                // Snapshot live charges here. Earlier peaks and later loop iterations
                // must not inflate a query about this execution point.
                self.obligations.push(Obligation {
                    span: expr.span.clone(),
                    cost: self.storage.live_expression(&expr.span),
                    bound: super::footprint::MemoryBudget::total(super::contracts::literal(
                        &expr.span, budget,
                    )),
                    kind: CheckKind::CurrentCheckpoint,
                });
                return Ok(0);
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
                    self.assign_owner(place, typ, rhs)?;
                    return Ok(0);
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
            ExprX::Loop { .. } => {
                self.analyze_loop(expr)?;
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
                        "memory sections require a function-level memory contract",
                    ))
                } else if matches!(
                    expr.x,
                    ExprX::ResourceAssert(_) | ExprX::ResourceAssertCurrent(_)
                ) {
                    Err(error(
                        &expr.span,
                        "memory checkpoints require a function-level memory contract",
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
        transitions: Default::default(),
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
        input_paths: Vec::new(),
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
    let mut input_vectors = HashMap::new();
    for (index, param) in f.params.iter().enumerate() {
        analysis.var_modes.insert(param.x.name.clone(), param.x.mode);
        if param.x.mode == Mode::Exec {
            let borrowed = layouts.borrowed_owner(&param.x.typ);
            if borrowed.is_some() && param.x.user_mut {
                return Err(unsupported(
                    &param.span,
                    "mutable bindings for borrowed owner parameters",
                ));
            }
            if layouts.owner(&param.x.typ) || borrowed.is_some() {
                let typ = borrowed.unwrap_or(&param.x.typ);
                let mut owner = analysis.input_owner(
                    typ,
                    &param.span,
                    layouts.size(&param.x.typ, &param.span)?,
                    &param.x.name,
                    &mut vec![],
                    &capacities,
                )?;
                owner.visit_paths(&mut vec![], &mut |path, node| {
                    if let Some(id) = node.vector {
                        input_vectors.insert((index, path.clone()), id);
                    }
                });
                let value =
                    SpannedTyped::new(&param.span, &param.x.typ, ExprX::Var(param.x.name.clone()));
                analysis.bind_collection_sources(&param.span, &mut owner, typ, value)?;
                if borrowed.is_some() {
                    analysis.heap.borrowed.insert(param.x.name.clone(), owner);
                } else {
                    analysis.mark_input(&mut owner, index, &mut vec![]);
                    analysis.heap.owners.insert(param.x.name.clone(), owner);
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
    let zero_charges = analysis.growth.zero_charges();
    let zero_forests = analysis.growth.zero_forests();
    let profiles = analysis
        .storage
        .points()
        .iter()
        .map(|p| super::lifetime::Profile {
            cost: p
                .cost
                .map(&function.span, &|value| {
                    super::metadata::profiles::simplify(value, &zero_charges, &zero_forests)
                })
                .expect("infallible zero-charge substitution"),
            result: !p.values.is_disjoint(&result.origins),
            inputs: p.inputs.clone(),
        })
        .collect::<Vec<_>>();
    let result_owner = analysis.result_owner.take();
    let (returned, returned_capacities) = super::ownership::summarize(
        function,
        result_owner.as_ref(),
        &analysis.growth,
        &analysis.bound,
    )?;
    let mut child_replacements = HashMap::new();
    for (name, path) in &analysis.heap.replaced {
        // Runtime positions belong to the collection effect, never to the
        // fixed-path ownership interface (their operation-local loans are gone).
        if super::paths::indexed(path) {
            continue;
        }
        let index = f.params.iter().position(|p| p.x.name == *name).unwrap();
        let child = analysis.heap.borrowed[name].at(path).unwrap();
        let (owner, capacities) =
            super::ownership::summarize(function, Some(child), &analysis.growth, &analysis.bound)?;
        child_replacements.insert(
            (index, path.clone()),
            super::allocations::ChildReplacement { owner: owner.unwrap(), capacities },
        );
    }
    analysis.check_checkpoints()?;
    let inferred = super::transfer::summarize(
        function,
        layouts,
        functions,
        summaries,
        &modes.var_modes,
        &analysis.transitions,
    )?;
    if let Some(inferred) = &inferred {
        analysis.apply_loop_transfers(&inferred.loops);
    }
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
    let summary = super::summary::FunctionSummary {
        transfer: inferred.map(|inferred| inferred.template),
        vectors: super::vector_calls::VectorSummary {
            removals: input_vectors
                .into_iter()
                .filter_map(|(path, id)| (!analysis.growth.vectors[id].append_only).then_some(path))
                .collect(),
            returned_capacities,
            reservations: capacities
                .into_iter()
                .map(|((name, path), capacity)| {
                    let index = f.params.iter().position(|p| p.x.name == name).unwrap();
                    ((index, path), capacity)
                })
                .collect(),
        },

        return_parameter,
        input_paths: analysis.input_paths.clone(),
        profiles,
        allocations: super::allocations::AllocationSummary {
            returned,
            children: child_replacements,
            collections: {
                let mut effects = HashMap::new();
                for (index, param) in f.params.iter().enumerate() {
                    if let Some(owner) = analysis.heap.borrowed.get(&param.x.name) {
                        for (path, effect) in super::elements::additions(owner, &analysis.growth) {
                            if !analysis.heap.is_replaced(&param.x.name, &path) {
                                effects.insert((index, path), effect);
                            }
                        }
                    }
                }
                effects
            },
            retained: {
                let mut effects = HashMap::new();
                for (index, param) in f.params.iter().enumerate() {
                    if let Some(owner) = analysis.heap.borrowed.get(&param.x.name) {
                        for (path, charge) in super::ownership::replacements(
                            owner,
                            &analysis.growth,
                            function,
                            &analysis.bound,
                        ) {
                            if !analysis.heap.is_replaced(&param.x.name, &path) {
                                effects.insert((index, path), charge);
                            }
                        }
                    }
                }
                effects
            },
        },
    };
    super::transfer::validate(function, layouts, &summary)?;
    Ok(Some(FunctionAnalysis {
        report,
        summary,
        calls: analysis.calls,
        symbolic_bound,
        obligations: analysis.obligations,
        checks: analysis.checks,
        growth: analysis.growth,
    }))
}
