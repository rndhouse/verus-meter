//! Function entry and structural traversal of executable expressions/scopes.

use super::accounting::{Accounting, CheckKind, MemoryReport, Obligation};
use super::footprint::MemoryKind;
use super::layout::Layouts;
use super::model::{arithmetic, eligible, unit, unsupported};
use crate::ast::*;
use crate::messages::{Span, error};
use std::collections::{HashMap, HashSet};

/// Checked facts and proof work awaiting publication by the crate-wide pass.
pub(super) struct FunctionAnalysis {
    /// Collected peaks and diagnostic events for this checked body.
    pub(super) report: MemoryReport,
    /// Call-composition facts published only after body accounting succeeds.
    pub(super) summary: Option<super::summary::FunctionSummary>,
    /// Local obligations can be checked while a required global proof is still
    /// unavailable. A helper can expose its local ownership transformation
    /// to checked callers while this error prevents crate verification.
    pub(super) incomplete: Option<VirErr>,
    /// A native mutex helper has a checked local summary. Its acquisition
    /// identities still need a checked call path into a composed domain.
    pub(super) needs_mutex_caller: bool,
    /// Local actor effects exist even when no general call summary is admissible.
    pub(super) effects: std::sync::Arc<super::summary::BodyEffects>,
    /// Declared bound when it must be proved as a formula rather than a constant.
    pub(super) symbolic_bound: Option<Expr>,
    /// Memory inequalities to assert at their original execution sites.
    pub(super) obligations: Vec<Obligation>,
    /// Additional safety conditions, such as reserved vector capacity.
    pub(super) checks: Vec<(Span, Expr)>,
    /// Erased vector state and the proof instrumentation that maintains it.
    pub(super) growth: super::growth::Growth,
}

/// One function's evolving ownership state and already checked callee facts.
pub(super) struct Analysis<'a> {
    /// Rust's evaluated value for a named integer used in a reservation.
    pub(super) reservation_constant: &'a dyn Fn(&Fun) -> Option<u64>,
    /// Fresh VIR positions for proof checks at implicit source boundaries.
    pub(super) fresh_span: &'a dyn Fn(&Span) -> Span,
    /// Current actor's lexical capture bindings, used by nested constructions.
    pub(super) worker_inputs: Vec<super::workers::Input>,
    /// Body-local views into a retained closure environment. Moving a view
    /// creates destination inline storage without retiring the enclosing slot.
    pub(super) capture_views: HashSet<VarIdent>,
    /// Nested accounting views of one source boundary are one evaluation.
    pub(super) evaluations: std::collections::BTreeMap<crate::messages::AstId, usize>,
    /// Runtime capture types and bodies recovered by mode checking and rustc.
    pub(super) concurrency: &'a super::concurrency::Evidence,
    /// Current checked worker body; None denotes the enclosing accounting function.
    pub(super) current_worker: Option<super::workers::WorkerId>,
    /// Independently budgeted sections enclosing this point on this actor.
    pub(super) section_scopes: Vec<crate::messages::AstId>,
    /// Reachable fallthrough and pending lexical exits share one lifetime model.
    pub(super) flow: super::control::Flow,
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
    pub(super) checkpoints: Vec<super::checkpoints::Checkpoint>,
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
    /// Reuse the same transfer-derived loop and extent evidence in ordinary
    /// functions and asynchronous bodies. Every condition remains a proof obligation.
    pub(super) fn apply_transfer_evidence(
        &mut self,
        inferred: &super::transfer::Inferred,
    ) -> Result<(), VirErr> {
        self.apply_progress_evidence(&inferred.progress);
        self.growth.publications.extend(inferred.publications.clone());
        for progress in inferred.progress.values() {
            for prefix in &progress.populations {
                if self.transitions.captured_populations.is_empty() {
                    prefix.emit(&mut self.growth, &HashMap::new())?;
                } else {
                    self.growth.captured_prefixes.push(prefix.clone());
                }
            }
        }
        self.apply_loop_evidence(
            &inferred.loops,
            &inferred.growth,
            &inferred.scratch,
            &inferred.repetitions,
        )?;
        for (span, condition) in &inferred.checks {
            let check = SpannedTyped::new(
                span,
                &crate::ast_util::unit_typ(),
                ExprX::AssertAssume {
                    is_assume: false,
                    expr: condition.clone(),
                    msg: Some(super::model::unsupported(
                        span,
                        "an allocation extent beyond the inferred iteration bound",
                    )),
                },
            );
            self.growth
                .before
                .entry(span.id)
                .or_default()
                .push(crate::def::Spanned::new(span.clone(), StmtX::Expr(check)));
        }
        Ok(())
    }

    /// Immutable scalar values and shared slice lengths can be reread inside
    /// isolated loop proofs without losing a section's entry allowance.
    pub(super) fn record_immutable_binding(&mut self, name: &VarIdent, typ: &Typ) {
        if super::contracts::scalar(typ) {
            self.stable_scalars.insert(name.clone());
        } else if matches!(&**typ, TypX::Decorate(TypDecoration::Ref, None, inner) if super::model::slice(inner))
        {
            self.growth.immutable_slices.insert(name.clone());
        }
    }

    /// Operation-local allocation observations include the current unit counters.
    /// Persistent contracts still use only immutable function inputs.
    pub(super) fn allocation_scalars(&self) -> HashSet<VarIdent> {
        self.stable_scalars
            .iter()
            .chain(&self.growth.loop_counters)
            .chain(&self.growth.carried_scalars)
            .cloned()
            .collect()
    }

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
                    if !unit(&expr.typ)
                        && !matches!(&*expr.typ, TypX::Decorate(TypDecoration::Never, _, _))
                    {
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
        let first_exit = self.flow.exits.len();
        let mut holders = self.transitions.holders.enter(expr);
        self.storage.event(&expr.span, "enter lexical scope".into());
        for stmt in stmts {
            if !self.flow.reachable {
                break;
            }
            let moved_from = self.moved_holder_source(stmt);
            let start = holders.before_statement(stmt, moved_from, &mut self.storage)?;
            let evaluation = self.enter_temporary_scope(stmt.span.id);
            // Even an early source exit must pass its statement's temporary
            // cleanup before the enclosing lexical scopes unwind.
            'statement: {
                match &stmt.x {
                    StmtX::Expr(e) => self.discard(e)?,
                    StmtX::Decl { pattern, init, els, .. } => {
                        if super::execution::ignored_statement(stmt, &self.var_modes) {
                            break 'statement;
                        }
                        if matches!(pattern.x, PatternX::Wildcard)
                            && super::contracts::scalar(&pattern.typ)
                            && els.is_none()
                            && let Some(init) = init
                        {
                            // A discarded scalar item evaluates its initializer but
                            // creates no named value lifetime, including in `for _`.
                            let scratch = self.read(init, &pattern.typ)?;
                            self.storage.release(
                                &stmt.span,
                                MemoryKind::host_local(),
                                scratch,
                                "discarded scalar initializer",
                            );
                            break 'statement;
                        }
                        if els.is_none()
                            && let Some(source) = init
                            && let Some(fields) =
                                super::synchronization::rwlock::write_pattern(pattern)
                        {
                            self.split_writer_result(
                                source,
                                fields,
                                &mut locals,
                                &mut owned_locals,
                            )?;
                            if self.layouts.owner(&pattern.typ) {
                                self.transitions.pattern(
                                    &pattern.span,
                                    super::transfer::checked::Pattern::WriterPair,
                                );
                            }
                            break 'statement;
                        }
                        let Some((binding, source_type, binding_init)) =
                            super::execution::declaration_binding(
                                self.layouts,
                                pattern,
                                init.as_ref(),
                            )
                        else {
                            return Err(unsupported(
                                &stmt.span,
                                "destructuring or wildcard declarations",
                            ));
                        };
                        let init = &binding_init;
                        match self.var_modes.get(&binding.name) {
                            Some(Mode::Spec | Mode::Proof) => break 'statement,
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
                        if binding.user_mut == Some(false) {
                            self.record_immutable_binding(&binding.name, &binding.typ);
                        }
                        locals.push((stmt.span.clone(), binding.name.clone()));
                        let from_iterator = init.as_ref().is_some_and(|source| {
                            matches!(&source.x, PlaceX::Local(name)
                                    if self.growth.iterator_item_slots.contains(name)
                                    && self.growth.implicit_collection_loop_slots.contains(name))
                        });
                        // An immutable borrowed pattern just visits the existing
                        // element. A binding of a consumed value provides storage.
                        let item_view = from_iterator
                            && binding.user_mut == Some(false)
                            && matches!(&*binding.typ, TypX::Decorate(TypDecoration::Ref, None, _));
                        let value = if item_view
                            || self.growth.implicit_collection_loop_slots.contains(&binding.name)
                        {
                            if let Some(init) = init {
                                if self.layouts.owner(&binding.typ)
                                    && matches!(init.x, PlaceX::Local(_))
                                {
                                    let moved = self.produce_place(
                                        init,
                                        &binding.typ,
                                        binding.copy,
                                        &stmt.span,
                                    )?;
                                    self.release_value(moved, &stmt.span);
                                } else {
                                    self.initialize(init, &binding.typ)?;
                                }
                            }
                            super::lifetime::Value::unit()
                        } else if let Some(init) = init {
                            let value =
                                self.produce_place(init, source_type, binding.copy, &stmt.span)?;
                            if from_iterator && !binding.copy {
                                self.release_value(value, &stmt.span);
                                self.fresh_value(&stmt.span, &binding.typ)?
                            } else {
                                value
                            }
                        } else {
                            self.fresh_value(&stmt.span, &binding.typ)?
                        };
                        if !self.flow.reachable {
                            break 'statement;
                        }
                        let mut value = value;
                        // A mutable reference slot can be rewritten through another
                        // borrow. Only immutable bindings may keep an identity view.
                        if binding.user_mut != Some(false)
                            || matches!(&*binding.typ, TypX::MutRef(_))
                                && !matches!(
                                    value.synchronization_view,
                                    Some(super::synchronization::local::View::Payload(_))
                                )
                        {
                            value.synchronization_view = None;
                        }
                        self.slots.insert(binding.name.clone(), value);
                        if self.layouts.owner(&binding.typ) {
                            owned_locals.push(binding.name.clone());
                            if init.is_none()
                                && self.growth.iterator_item_slots.contains(&binding.name)
                            {
                                break 'statement;
                            }
                            let mut owner = self.result_owner.take().ok_or_else(|| {
                                unsupported(&stmt.span, "uninitialized heap owners")
                            })?;
                            let value = SpannedTyped::new(
                                &stmt.span,
                                &binding.typ,
                                ExprX::Var(binding.name.clone()),
                            );
                            self.bind_collection_sources(
                                &stmt.span,
                                &mut owner,
                                &binding.typ,
                                value,
                            )?;
                            self.heap.owners.insert(binding.name.clone(), owner);
                        }
                    }
                }
            }
            self.finish_temporary_scope(evaluation);
            holders.mark(start, &mut self.storage);
            if self.flow.reachable
                && let StmtX::Decl { pattern, init: Some(source), els: None, .. } = &stmt.x
            {
                if let Some([_, handle]) = super::synchronization::rwlock::write_pattern(pattern) {
                    holders.initialized(self.bind_writer_holder(handle, source));
                } else {
                    holders.initialized(self.bind_holder(pattern, None, Some(source)));
                }
            }
        }
        if self.flow.reachable {
            holders.finish(self, expr, tail.as_ref())?;
        }
        if let Some(tail) = tail.as_ref().filter(|_| self.flow.reachable) {
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
        self.cleanup_scope(&expr.span, &locals, first_exit);
        self.storage.event(&expr.span, "exit lexical scope".into());
        Ok(())
    }

    /// Evaluate source expressions. Only a standalone aggregate leaves a storage
    /// charge; scalar/reference operations introduce no implicit objects.
    pub(super) fn expr(&mut self, expr: &Expr) -> Result<u64, VirErr> {
        let evaluation = self.enter_temporary_scope(expr.span.id);
        let result = self.expr_inner(expr)?;
        self.finish_temporary_scope(evaluation);
        Ok(result)
    }

    fn expr_inner(&mut self, expr: &Expr) -> Result<u64, VirErr> {
        if let Some(copied) = self.copied_closure_read(expr) {
            return self.expr(&copied);
        }
        match &expr.x {
            ExprX::UnaryOpr(UnaryOpr::LoopIsolationBoundary(_), inner) => {
                self.record_collection_loop_header(inner);
                return self.expr(inner);
            }
            ExprX::NeverToAny(inner) => return self.expr(inner),
            ExprX::Return(value) => {
                self.exit(expr, super::control::Target::Return, value.as_ref())?;
                return Ok(0);
            }
            ExprX::BreakOrContinue { label, is_break, value } => {
                let target = if *is_break {
                    super::control::Target::Break(label.clone())
                } else {
                    super::control::Target::Continue(label.clone())
                };
                self.exit(expr, target, value.as_ref())?;
                return Ok(0);
            }
            _ => {}
        }
        if let Some(owner) = self.extracted_owner(expr, true)? {
            self.release_owner(owner, &expr.span);
            return Ok(0);
        }
        if self.layouts.owner(&expr.typ) {
            let value = self.produce(expr)?;
            if !self.flow.reachable {
                return Ok(0);
            }
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
            ExprX::ResourceAssertCurrent(budget) | ExprX::ResourceAssert(budget) => {
                self.checkpoint(expr, budget)?;
                return Ok(0);
            }
            _ if super::execution::ignored_expression(expr) => return Ok(0),
            // Mode checking requires the invariant operand and binder to be
            // proof-only. Every executable statement in its body still runs.
            ExprX::OpenInvariant(_, _, body, _) => return self.expr(body),
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
            ExprX::UnaryOpr(
                UnaryOpr::IntegerTypeBound(IntegerTypeBoundKind::ArchWordBits),
                operand,
            ) if matches!(&operand.x, ExprX::Const(Constant::Int(_))) => {}
            ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(_), operand) => {
                operands = self.expr(operand)?;
            }
            ExprX::Unary(UnaryOp::Not, arg) => operands = self.expr(arg)?,
            ExprX::Unary(UnaryOp::Clip { .. }, _)
                if super::model::widening_integer_cast(expr).is_some() =>
            {
                operands = self.expr(super::model::widening_integer_cast(expr).unwrap())?;
            }
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
                if self.layouts.owner(&lhs.typ) || self.layouts.owner(&rhs.typ) {
                    // Comparison borrows its operands. Releasing an owned
                    // temporary after evaluating only the left operand could
                    // free its backing before the right operand allocates.
                    // Owning comparisons need a reviewed call/lifetime rule.
                    return Err(unsupported(
                        &expr.span,
                        "owning comparisons without reviewed memory effects",
                    ));
                }
                let left = self.expr(lhs)?;
                let right = self.expr(rhs)?;
                operands = left.checked_add(right).expect("bounded by live total");
            }
            ExprX::Logical(op @ (LogicalOp::And | LogicalOp::Or), lhs, rhs) => {
                // A skipped operand retains its live storage. Use the same
                // ownership protection and path joins as an explicit branch;
                // charging the RHS peak alone cannot justify its release effects.
                if *op == LogicalOp::And {
                    self.conditional(expr, lhs, rhs, None, false)?;
                } else {
                    let yes = crate::ast_util::mk_bool(&expr.span, true);
                    self.conditional(expr, lhs, &yes, Some(rhs), false)?;
                }
                return Ok(0);
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
                    if self.growth.implicit_collection_loop_slots.contains(name) {
                        self.initialize_expr(rhs)?;
                    } else if self.slots.get(name).is_none_or(|v| v.bytes == 0) {
                        let value = self.produce(rhs)?;
                        self.slots.insert(name.clone(), value);
                    } else {
                        self.initialize_expr(rhs)?;
                    }
                    // A late initialization or later write cannot preserve an
                    // immutable view from the previous value of this slot.
                    if let Some(slot) = self.slots.get_mut(name) {
                        slot.synchronization_view = None;
                    }
                } else {
                    self.initialize_expr(rhs)?;
                }
                self.access(place, typ)?;
                return Ok(0);
            }
            ExprX::If(cond, then_expr, else_expr)
                if unit(&expr.typ) || super::model::diverging(&expr.typ) =>
            {
                self.conditional(expr, cond, then_expr, else_expr.as_ref(), false)?;
                return Ok(0);
            }
            ExprX::Loop { .. } => {
                self.analyze_loop(expr)?;
                return if let Some(value) = self.produced.take() {
                    self.expression_value(value, &expr.span)
                } else {
                    Ok(0)
                };
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
    modes: Option<&HashMap<VarIdent, Mode>>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
    budgets: &HashMap<Fun, u64>,
    summaries: &HashMap<Fun, super::summary::FunctionSummary>,
    concurrency: &super::concurrency::Evidence,
    reservation_constant: &dyn Fn(&Fun) -> Option<u64>,
    fresh_span: &dyn Fn(&Span) -> Span,
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
    let accounting_function = super::concurrency::accounting_body(function, concurrency)?;
    let function = &accounting_function;
    let f = &function.x;
    eligible(function, layouts)?;
    let body = f
        .body
        .as_ref()
        .ok_or_else(|| unsupported(&function.span, "functions without a verified body"))?;
    let modes = modes.ok_or_else(|| {
        unsupported(&function.span, "functions without execution-mode information")
    })?;
    super::control::validate(body, modes)?;
    let mut analysis = Analysis {
        reservation_constant,
        fresh_span,
        worker_inputs: vec![],
        capture_views: Default::default(),
        evaluations: Default::default(),
        concurrency,
        current_worker: None,
        section_scopes: Vec::new(),
        flow: Default::default(),
        transitions: Default::default(),
        slots: HashMap::new(),
        produced: None,
        summaries,
        result_owner: None,
        budgets,
        layouts,
        functions,
        var_modes: modes.clone(),
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

    let capacities =
        super::inference::infer(function, layouts, summaries, functions, &analysis.bound, modes)?;
    let interface = analysis.bind_synchronization_inputs(function);
    analysis.transitions.holders =
        super::synchronization::holders::Bindings::bind(function, layouts);
    let mut input_vectors = HashMap::new();
    let worker_parameter = layouts.worker_parameter(function);
    for (index, param) in f.params.iter().enumerate() {
        analysis.var_modes.insert(param.x.name.clone(), param.x.mode);
        if param.x.mode == Mode::Exec {
            if !param.x.user_mut {
                analysis.record_immutable_binding(&param.x.name, &param.x.typ);
            }
            let descriptor = layouts.borrowed_descriptor(&param.x.typ);
            let borrowed = descriptor.as_ref();
            if borrowed.is_some() && param.x.user_mut && !layouts.owner(&param.x.typ) {
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
                    worker_parameter == Some(index),
                )?;
                if borrowed.is_some() && owner.contains_rw_cell() {
                    return Err(unsupported(
                        &param.span,
                        "a borrowed RwLock payload without a checked shared version",
                    ));
                }
                let separate_guard = borrowed.is_some() && layouts.owner(&param.x.typ);
                if separate_guard {
                    let mut guard = super::heap::Owner {
                        synchronization: interface.owned_input(index),
                        ..Default::default()
                    };
                    analysis.mark_input(&mut guard, index, &mut vec![]);
                    analysis.heap.owners.insert(param.x.name.clone(), guard);
                }
                analysis.bind_protected_input(
                    &mut owner,
                    index,
                    &interface,
                    &body.span,
                    separate_guard,
                );
                if worker_parameter == Some(index) {
                    analysis.transitions.worker_parameter =
                        Some((index, owner.vector.expect("worker vector input")));
                }
                owner.visit_paths(&mut vec![], &mut |path, node| {
                    if let Some(id) = node.vector {
                        input_vectors.insert((index, path.clone()), id);
                    }
                });
                let value =
                    SpannedTyped::new(&param.span, &param.x.typ, ExprX::Var(param.x.name.clone()));
                analysis.bind_collection_sources(&param.span, &mut owner, typ, value)?;
                owner.visit(&mut |node| {
                    if let Some(id) = node.vector
                        && node.source.is_some()
                    {
                        let length = analysis.owner_length(&param.span, node);
                        let entry = analysis.allocation_snapshot(&param.span, length);
                        analysis.growth.vectors[id].entry_length = Some(entry);
                    }
                });
                if borrowed.is_some() {
                    analysis.heap.borrowed.insert(layouts.borrowed_binder(param), owner);
                } else {
                    analysis.mark_input(&mut owner, index, &mut vec![]);
                    analysis.heap.owners.insert(param.x.name.clone(), owner);
                }
            }
            let mut value = analysis.fresh_value(&param.span, &param.x.typ)?;
            value.parameter = Some(index);
            value.synchronization_view = interface.input_view(index);
            analysis.slots.insert(param.x.name.clone(), value);
        }
    }
    analysis.mark_borrowed_origins(function)?;
    let symbolic_bound = super::symbolic::function_bound(function, budgets, functions, layouts)?;

    // Validate input ownership layouts before traversing them for proof demand.
    // Classification is needed at ownership interfaces, including an internal
    // collection from which a fixed owner is extracted, and at template calls.
    analysis.growth.runtime_classification =
        layouts.owner(&f.outer_ret.x.typ) || super::transfer::required(function, layouts)?;
    crate::ast_visitor::expr_visitor_check(body, &mut |_, value| {
        if let ExprX::Call { target: CallTarget::Fun(_, fun, _, _, _), .. } = &value.x {
            analysis.growth.runtime_classification |=
                summaries.get(fun).is_some_and(|summary| summary.transfer.is_some());
        }
        Ok::<(), VirErr>(())
    })?;

    let result = analysis.produce(body)?;
    analysis.check_indexed_exits(&body.span);
    analysis.drop_guard_parameters(function, &interface);
    analysis.check_populated_cell_exits(&function.span)?;
    analysis.prepare_guard_returns(function, &body.span)?;
    if analysis.flow.reachable {
        analysis.record_holder_return(body);
    }
    let result = analysis.finish_returns(&function.span, result)?;
    if let Some(site) = &analysis.growth.unreclaimed_cell {
        return Err(super::synchronization::rw_payload::unreclaimed(site));
    }
    let synchronized_result = analysis.finish_synchronization_interface(function, &interface)?;
    if !analysis.heap.temporaries.is_empty() || !analysis.evaluations.is_empty() {
        return Err(unsupported(&function.span, "unclosed compiler receiver-temporary scopes"));
    }
    analysis.heap.workers.check_closed(&function.span)?;
    analysis.check_worker_parameter_result(&function.span)?;
    analysis.check_checkpoints()?;
    let incomplete = analysis.check_worker_domain(function, &function.span)?;
    let mut worker_transfer = None;
    if let Some(error) = &incomplete {
        if analysis.transitions.retained_workers {
            // The global envelope remains unavailable, but population induction
            // must consume the coordinator's actual ownership transformation.
            let inferred = super::transfer::summarize(
                function,
                layouts,
                functions,
                summaries,
                modes,
                &analysis.transitions,
            )?;
            if let Some(inferred) = &inferred {
                analysis.apply_transfer_evidence(inferred)?;
            }
            worker_transfer = inferred;
        }
        let publications = std::mem::take(&mut analysis.growth.publications);
        for prefix in std::mem::take(&mut analysis.growth.captured_prefixes) {
            prefix.emit(&mut analysis.growth, &publications)?;
        }
        analysis.worker_obligations()?;
        // A closed consumer can export the destruction of a supplied payload.
        // Its caller must still pay for *all* original regions for the whole
        // declared call allowance, and the global concurrency error stays mandatory.
        let consumed_payload = worker_transfer.is_some()
            && super::model::unit(&f.outer_ret.x.typ)
            && analysis.heap.borrowed.is_empty()
            && analysis.result_owner.is_none()
            && analysis.heap.shared.is_empty()
            && (!analysis.transitions.carried_inputs.is_empty()
                || analysis.growth.indexed_shared.values().any(|c| !c.backing.inputs().is_empty()))
            && {
                // Scalar formals still occupy their inline argument slots at the
                // end of the body. They leave with the frame and own no backing.
                let scalars = f
                    .params
                    .iter()
                    .filter(|p| super::contracts::scalar(&p.x.typ))
                    .filter_map(|p| analysis.slots.get(&p.x.name))
                    .flat_map(|value| value.ids.iter().copied())
                    .collect();
                analysis.storage.only_frame_storage(&scalars, &analysis.transitions.carried_inputs)
            };
        if !analysis.transitions.carried_inputs.is_empty() && !consumed_payload {
            return Err(unsupported(
                &function.span,
                "transporting incoming Arc storage outside a closed worker consumer",
            ));
        }
        if !consumed_payload {
            let report = analysis.storage.finish_conditional();
            analysis.obligations.extend(report.points.iter().map(|point| Obligation {
                contributor: None,
                span: point.span.clone(),
                cost: point.cost.clone(),
                bound: super::footprint::MemoryBudget::total(analysis.bound.clone()),
                kind: CheckKind::Function,
            }));
            let effects = super::summary::BodyEffects::from_accounting(
                body.clone(),
                analysis.transitions,
                &report,
                analysis.calls,
                None,
            )?;
            effects.validate_call_points(summaries)?;
            return Ok(Some(FunctionAnalysis {
                report,
                summary: None,
                incomplete: Some(error.clone()),
                needs_mutex_caller: false,
                effects,
                symbolic_bound,
                obligations: analysis.obligations,
                checks: analysis.checks,
                growth: analysis.growth,
            }));
        }
    }
    let return_parameter = result.parameter;
    let zero_charges = analysis.growth.zero_charges();
    let zero_forests = analysis.growth.zero_forests();
    let mut profiles = analysis
        .storage
        .points()
        .iter()
        .map(|p| super::lifetime::Profile {
            condition: p.condition.clone(),
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
    if !analysis.transitions.packed_returns {
        analysis.transitions.returned =
            analysis.storage.returned_storage(result_owner.as_ref(), &analysis.growth.elements);
    }
    analysis.record_output_origins(function, result_owner.as_ref());
    let (returned, returned_capacities) = super::ownership::summarize(
        function,
        result_owner.as_ref(),
        &analysis.growth,
        &analysis.bound,
    )?;
    if !analysis.heap.shared.is_empty() {
        return Err(unsupported(
            &function.span,
            "shared backing surviving without a checked outgoing ownership descriptor",
        ));
    }
    let mut child_replacements = HashMap::new();
    for (name, path) in &analysis.heap.replaced {
        // Runtime positions belong to the collection effect, never to the
        // fixed-path ownership interface (their operation-local loans are gone).
        if super::paths::indexed(path) {
            continue;
        }
        let index = f.params.iter().position(|p| layouts.borrowed_binder(p) == *name).unwrap();
        let child = analysis.heap.borrowed[name].at(path).unwrap();
        let (owner, capacities) =
            super::ownership::summarize(function, Some(child), &analysis.growth, &analysis.bound)?;
        child_replacements.insert(
            (index, path.clone()),
            super::allocations::ChildReplacement { owner: owner.unwrap(), capacities },
        );
    }
    let inferred = if incomplete.is_some() {
        profiles.push(super::lifetime::Profile {
            condition: Default::default(),
            cost: super::footprint::Footprint::allowance(analysis.bound.clone()),
            result: false,
            inputs: (0..analysis.input_paths.len()).collect(),
        });
        worker_transfer
    } else {
        let inferred = super::transfer::summarize(
            function,
            layouts,
            functions,
            summaries,
            modes,
            &analysis.transitions,
        )?;
        if let Some(inferred) = &inferred {
            analysis.apply_transfer_evidence(inferred)?;
        }
        inferred
    };
    let report = if incomplete.is_some() || symbolic_bound.is_some() {
        analysis.storage.finish_conditional()
    } else {
        analysis.storage.finish(&function.span)
    };
    let bound =
        symbolic_bound.clone().unwrap_or_else(|| super::contracts::literal(&function.span, budget));
    analysis.obligations.extend(report.points.iter().map(|point| Obligation {
        contributor: point.contributor,
        span: point.span.clone(),
        cost: point.cost.clone(),
        bound: super::footprint::MemoryBudget::total(bound.clone()),
        kind: CheckKind::Function,
    }));
    let modified_parameters =
        super::transfer::modified_parameters(&function.x.params, layouts, &analysis.transitions);
    let payloads = function
        .x
        .params
        .iter()
        .enumerate()
        .filter_map(|(index, param)| layouts.borrowed_owner(&param.x.typ).map(|_| index))
        .collect();
    analysis
        .transitions
        .distinct_payload_inputs
        .extend(interface.require_distinct_payloads(&payloads, &modified_parameters));
    let summary = super::summary::FunctionSummary {
        effects: None,
        synchronized_result,
        closed_mutex: analysis.transitions.closed_mutex_output(
            function,
            &modified_parameters,
            &report.points,
            inferred.as_ref().map(|i| &i.template),
        ),
        modified_parameters,
        transfer_required: super::transfer::requires_summary(
            function,
            layouts,
            &analysis.transitions,
            summaries,
        )?,
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
                    if let Some(owner) = analysis.heap.borrowed.get(&layouts.borrowed_binder(param))
                    {
                        for (path, effect) in super::elements::additions(owner, &analysis.growth) {
                            if !analysis.heap.is_replaced(&layouts.borrowed_binder(param), &path) {
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
                    if let Some(owner) = analysis.heap.borrowed.get(&layouts.borrowed_binder(param))
                    {
                        for (path, charge) in super::ownership::replacements(
                            owner,
                            &analysis.growth,
                            function,
                            &analysis.bound,
                        ) {
                            if !analysis.heap.is_replaced(&layouts.borrowed_binder(param), &path) {
                                effects.insert((index, path), charge);
                            }
                        }
                    }
                }
                effects
            },
        },
    };
    let mut summary = summary;
    let effects = super::summary::BodyEffects::from_accounting(
        body.clone(),
        analysis.transitions,
        &report,
        analysis.calls,
        None,
    )?;
    effects.validate_call_points(summaries)?;
    let summary_has_lock = effects.ownership.locks_mutex();
    summary.effects = Some(effects.clone());
    super::transfer::validate(function, layouts, &summary)?;
    Ok(Some(FunctionAnalysis {
        report,
        summary: Some(summary),
        incomplete: incomplete.or_else(|| {
            worker_parameter.map(|_| super::workers::parameter_domain_error(&function.span))
        }),
        needs_mutex_caller: summary_has_lock,
        effects,
        symbolic_bound,
        obligations: analysis.obligations,
        checks: analysis.checks,
        growth: analysis.growth,
    }))
}
