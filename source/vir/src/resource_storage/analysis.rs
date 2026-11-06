//! Function entry and structural traversal of executable expressions/scopes.

use super::accounting::{Accounting, Peak, StorageReport};
use super::layout::Layouts;
use super::model::{arithmetic, eligible, unit, unsupported};
use crate::ast::*;
use crate::messages::{Span, error};
use crate::resolution_inference::ResolutionInfo;
use std::collections::HashMap;

pub(super) struct FunctionAnalysis {
    pub(super) report: StorageReport,
    pub(super) calls: Vec<(Fun, Span)>,
}

struct Checkpoint {
    span: Span,
    budget: u64,
    peak: Peak,
}

pub(super) struct Analysis<'a> {
    pub(super) budgets: &'a HashMap<Fun, u64>,
    pub(super) layouts: &'a Layouts,
    pub(super) functions: &'a HashMap<Fun, Function>,
    pub(super) var_modes: HashMap<VarIdent, Mode>,
    pub(super) storage: Accounting,
    pub(super) calls: Vec<(Fun, Span)>,
    checkpoints: Vec<Checkpoint>,
}

impl Analysis<'_> {
    pub(super) fn discard(&mut self, expr: &Expr) -> Result<(), VirErr> {
        let result = self.expr(expr)?;
        self.storage.release(&expr.span, result, "consumed expression result");
        Ok(())
    }

    fn block(&mut self, expr: &Expr, stmts: &Stmts, tail: &Option<Expr>) -> Result<(), VirErr> {
        if !unit(&expr.typ) {
            return Err(unsupported(&expr.span, "value-returning blocks"));
        }
        let entry = self.storage.live();
        let mut locals = Vec::new();
        self.storage.event(&expr.span, "enter lexical scope".into());
        for stmt in stmts.iter() {
            match &stmt.x {
                StmtX::Expr(e) => self.discard(e)?,
                StmtX::Decl { pattern, mode, init, els, .. } => {
                    if matches!(mode, Some((Mode::Spec | Mode::Proof, _))) {
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
                    let bytes = self.layouts.size(&binding.typ, &stmt.span)?;
                    self.storage.reserve(&stmt.span, bytes, "local slot")?;
                    locals.push((stmt.span.clone(), bytes));
                    if let Some(init) = init {
                        self.initialize(init, &binding.typ)?;
                    }
                }
            }
        }
        if let Some(tail) = tail {
            self.discard(tail)?;
        }
        for (span, bytes) in locals.into_iter().rev() {
            self.storage.release(&span, bytes, "local scope exit");
        }
        assert_eq!(self.storage.live(), entry);
        self.storage.event(&expr.span, "exit lexical scope".into());
        Ok(())
    }

    /// Evaluate source expressions. Only a standalone aggregate leaves a storage
    /// charge; scalar/reference operations introduce no implicit objects.
    pub(super) fn expr(&mut self, expr: &Expr) -> Result<u64, VirErr> {
        if let Some(bytes) = self.construction(expr, false)? {
            return Ok(bytes);
        }
        let mut operands = 0u64;
        match &expr.x {
            ExprX::ResourceAssert(budget) => {
                let budget = super::budget::evaluate_checkpoint(
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
            ExprX::Ghost { alloc_wrapper: false, .. }
            | ExprX::AssertAssume { .. }
            | ExprX::AssertBy { .. }
            | ExprX::AssertQuery { .. }
            | ExprX::AssertCompute(..)
            | ExprX::Fuel(..)
            | ExprX::RevealString(..)
            | ExprX::RevealByteString(..) => return Ok(0),
            ExprX::Block(stmts, tail) => {
                self.block(expr, stmts, tail)?;
                return Ok(0);
            }
            ExprX::Const(Constant::Bool(_) | Constant::Int(_)) => {}
            ExprX::Ctor(Dt::Tuple(0), _, fields, None) if fields.is_empty() => {}
            ExprX::ReadPlace(place, kind) if matches!(kind.preliminary_kind, ReadKind::Unused) => {
                if let PlaceX::Temporary(value) = &place.x {
                    // Rust-to-VIR wraps non-unit expression statements in an
                    // unused temporary place. It is the expression's result,
                    // not an additional copy or a reference with extended lifetime.
                    return self.expr(value);
                }
                return self.read(place, &expr.typ);
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
            ExprX::Binary(op, lhs, rhs) if arithmetic(op) => {
                if !crate::ast_util::types_equal(&lhs.typ, &expr.typ)
                    || !crate::ast_util::types_equal(&rhs.typ, &expr.typ)
                {
                    return Err(unsupported(&expr.span, "mixed-type arithmetic"));
                }
                operands = self.expr(lhs)? + self.expr(rhs)?;
            }
            ExprX::Call { .. } => return self.call_expr(expr),
            ExprX::Assign { place, rhs, op, typ, .. } => {
                if op.as_ref().is_some_and(|op| !arithmetic(op)) {
                    return Err(unsupported(&expr.span, "this compound assignment"));
                }
                // The destination owns the result, for every supported type.
                // Keep RHS-before-LHS evaluation and all ordinary validation.
                self.initialize_expr(rhs)?;
                self.access(place, typ)?;
                return Ok(0);
            }
            ExprX::If(cond, then_expr, else_expr) if unit(&expr.typ) => {
                self.discard(cond)?;
                let prefix_peak = self.storage.peak();
                self.storage.event(&expr.span, "analyze then alternative".into());
                self.discard(then_expr)?;
                let mut joined_peak = self.storage.peak();
                // A checkpoint in one alternative cannot have visited its sibling.
                self.storage.set_peak(prefix_peak);
                if let Some(else_expr) = else_expr {
                    self.storage.event(&expr.span, "analyze else alternative".into());
                    self.discard(else_expr)?;
                }
                joined_peak.merge(&self.storage.peak());
                self.storage.set_peak(joined_peak);
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
                let entry = self.storage.live();
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

    pub(super) fn result(&mut self, expr: &Expr, operands: u64) -> Result<u64, VirErr> {
        self.layouts.size(&expr.typ, &expr.span)?;
        self.storage.release(&expr.span, operands, "consumed aggregate operands");
        Ok(0)
    }
}

pub(super) fn check(
    function: &Function,
    modes: Option<&ResolutionInfo>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
    budgets: &HashMap<Fun, u64>,
) -> Result<Option<FunctionAnalysis>, VirErr> {
    let Some(&budget) = budgets.get(&function.x.name) else {
        if let Some(body) = &function.x.body {
            crate::ast_visitor::expr_visitor_check(body, &mut |_, expr| {
                if matches!(expr.x, ExprX::ResourceAssert(_)) {
                    Err(error(
                        &expr.span,
                        "peakmem checkpoints require a function-level peakmem contract",
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
        budgets,
        layouts,
        functions,
        var_modes: modes.var_modes.clone(),
        storage: Accounting::new(&function.span, budget),
        calls: Vec::new(),
        checkpoints: Vec::new(),
    };
    for param in f.params.iter() {
        analysis.var_modes.insert(param.x.name.clone(), param.x.mode);
        if param.x.mode == Mode::Exec {
            let bytes = layouts.size(&param.x.typ, &param.span)?;
            analysis.storage.reserve(&param.span, bytes, "parameter slot")?;
        }
    }
    analysis.discard(body)?;
    for checkpoint in &analysis.checkpoints {
        if checkpoint.peak.bytes > checkpoint.budget {
            return Err(error(
                &checkpoint.span,
                format!(
                    "peakmem assertion failed: peak {} bytes exceeds bound {} bytes",
                    checkpoint.peak.bytes, checkpoint.budget,
                ),
            )
            .secondary_span(&checkpoint.peak.span));
        }
    }
    let report = analysis.storage.finish(&function.span)?;
    Ok(Some(FunctionAnalysis { report, calls: analysis.calls }))
}
