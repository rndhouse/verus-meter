//! Declared memory formulas, instantiated with stable scalar call arguments.

use super::budget::{BudgetExpr, BudgetExprX};
use super::layout::Layouts;
use super::model::{ResourceContract, integer_type_size, negative_literal};
use crate::ast::*;
use crate::ast_util::*;
use crate::messages::{Span, error};
use num_traits::ToPrimitive;
use std::collections::{HashMap, HashSet};

pub(super) fn literal(span: &Span, bytes: u64) -> Expr {
    SpannedTyped::new(span, &int_typ(), ExprX::Const(const_int_from_u128(bytes as u128)))
}

pub(super) fn scalar(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Bool) || integer_type_size(typ).is_some()
}

pub(super) fn inputs(function: &Function) -> HashSet<VarIdent> {
    function
        .x
        .params
        .iter()
        .filter(|p| p.x.mode == Mode::Exec && !p.x.user_mut && scalar(&p.x.typ))
        .map(|p| p.x.name.clone())
        .collect()
}

pub(super) fn predicate(expr: &Expr, allowed: &HashSet<VarIdent>) -> Result<Expr, VirErr> {
    if let Some(value) = negative_literal(expr) {
        return Ok(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Const(value)));
    }
    let variable = match &expr.x {
        ExprX::Var(name) => Some(name),
        ExprX::ReadPlace(place, _) => match &place.x {
            PlaceX::Local(name) => Some(name),
            _ => None,
        },
        _ => None,
    };
    if let Some(name) = variable {
        if allowed.contains(name) {
            return Ok(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(name.clone())));
        }
        return Err(error(
            &expr.span,
            "memory budget predicates currently require immutable Boolean or native integer input parameters",
        ));
    }
    let x = match &expr.x {
        ExprX::Const(Constant::Bool(_) | Constant::Int(_)) => return Ok(expr.clone()),
        ExprX::Unary(UnaryOp::Not, e) => ExprX::Unary(UnaryOp::Not, predicate(e, allowed)?),
        ExprX::Binary(op @ (BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Inequality(_)), a, b) => {
            ExprX::Binary(*op, predicate(a, allowed)?, predicate(b, allowed)?)
        }
        ExprX::Logical(op, a, b) => {
            ExprX::Logical(*op, predicate(a, allowed)?, predicate(b, allowed)?)
        }
        _ => {
            return Err(error(
                &expr.span,
                "memory budget predicates currently support scalar input comparisons and Boolean operators",
            ));
        }
    };
    Ok(SpannedTyped::new(&expr.span, &expr.typ, x))
}

pub(super) fn add(span: &Span, a: Expr, b: Expr) -> Expr {
    simplify(&SpannedTyped::new(
        span,
        &int_typ(),
        ExprX::Binary(BinaryOp::Arith(ArithOp::Add(OverflowBehavior::Allow)), a, b),
    ))
}

// Folding is deliberately limited to pure constants. Unknown predicates remain
// proof expressions; no executable branch is removed from structural accounting.
fn simplify(expr: &Expr) -> Expr {
    if let Some(value) = negative_literal(expr) {
        return SpannedTyped::new(&expr.span, &expr.typ, ExprX::Const(value));
    }
    let x = match &expr.x {
        ExprX::If(c, a, Some(b)) => {
            let c = simplify(c);
            let a = simplify(a);
            let b = simplify(b);
            if let ExprX::Const(Constant::Bool(c)) = c.x {
                return if c { a } else { b };
            }
            ExprX::If(c, a, Some(b))
        }
        ExprX::Unary(UnaryOp::Not, a) => {
            let a = simplify(a);
            if let ExprX::Const(Constant::Bool(v)) = a.x {
                ExprX::Const(Constant::Bool(!v))
            } else {
                ExprX::Unary(UnaryOp::Not, a)
            }
        }
        ExprX::Logical(op, a, b) => {
            let a = simplify(a);
            let b = simplify(b);
            if let (ExprX::Const(Constant::Bool(a)), ExprX::Const(Constant::Bool(b))) = (&a.x, &b.x)
            {
                let value = match op {
                    LogicalOp::And => *a && *b,
                    LogicalOp::Or => *a || *b,
                    LogicalOp::Implies => !*a || *b,
                };
                ExprX::Const(Constant::Bool(value))
            } else {
                ExprX::Logical(*op, a, b)
            }
        }
        ExprX::Binary(op, a, b) => {
            let a = simplify(a);
            let b = simplify(b);
            match (&a.x, &b.x) {
                (ExprX::Const(Constant::Int(a)), ExprX::Const(Constant::Int(b))) => {
                    let value = match op {
                        BinaryOp::Arith(ArithOp::Add(_)) => {
                            return SpannedTyped::new(
                                &expr.span,
                                &expr.typ,
                                ExprX::Const(Constant::Int(a + b)),
                            );
                        }
                        BinaryOp::Arith(ArithOp::Sub(_)) => {
                            return SpannedTyped::new(
                                &expr.span,
                                &expr.typ,
                                ExprX::Const(Constant::Int(a - b)),
                            );
                        }
                        BinaryOp::Arith(ArithOp::Mul(_)) => {
                            return SpannedTyped::new(
                                &expr.span,
                                &expr.typ,
                                ExprX::Const(Constant::Int(a * b)),
                            );
                        }
                        BinaryOp::Eq(_) => a == b,
                        BinaryOp::Ne => a != b,
                        BinaryOp::Inequality(InequalityOp::Le) => a <= b,
                        BinaryOp::Inequality(InequalityOp::Lt) => a < b,
                        BinaryOp::Inequality(InequalityOp::Ge) => a >= b,
                        BinaryOp::Inequality(InequalityOp::Gt) => a > b,
                        _ => return expr.clone(),
                    };
                    ExprX::Const(Constant::Bool(value))
                }
                (ExprX::Const(Constant::Bool(a)), ExprX::Const(Constant::Bool(b))) => match op {
                    BinaryOp::Eq(_) => ExprX::Const(Constant::Bool(a == b)),
                    BinaryOp::Ne => ExprX::Const(Constant::Bool(a != b)),
                    _ => return expr.clone(),
                },
                _ => ExprX::Binary(*op, a, b),
            }
        }
        _ => return expr.clone(),
    };
    SpannedTyped::new(&expr.span, &expr.typ, x)
}

pub(super) fn constant(expr: &Expr) -> Option<u64> {
    if let ExprX::Const(Constant::Int(n)) = &expr.x { n.to_u64() } else { None }
}

pub(super) fn envelope(expr: &Expr) -> Result<u64, VirErr> {
    if let Some(n) = constant(expr) {
        return Ok(n);
    }
    match &expr.x {
        ExprX::Var(_) => Ok(u64::MAX),
        ExprX::If(_, a, Some(b)) => Ok(envelope(a)?.max(envelope(b)?)),
        ExprX::Binary(BinaryOp::Arith(op), a, b) => {
            let a = envelope(a)?;
            let b = envelope(b)?;
            let n = match op {
                ArithOp::Add(_) => a.checked_add(b),
                ArithOp::Mul(_) => a.checked_mul(b),
                _ => None,
            };
            if numeric_input(expr) {
                Ok(n.unwrap_or(u64::MAX))
            } else {
                n.ok_or_else(|| error(&expr.span, "memory budget arithmetic exceeds u64"))
            }
        }
        _ => Err(error(&expr.span, "memory budget arithmetic exceeds u64")),
    }
}

pub(super) fn function_bound(
    function: &Function,
    budgets: &HashMap<Fun, u64>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
) -> Result<Expr, VirErr> {
    let Some(ResourceContract::SourceValuesV7Expr { budget }) = &function.x.attrs.resource_contract
    else {
        return Err(error(&function.span, "mem_peak requires a declared resource contract"));
    };
    lower(budget, &inputs(function), budgets, functions, layouts)
}

pub(super) fn instantiate(
    function: &Function,
    args: &Exprs,
    allowed: &HashSet<VarIdent>,
    budgets: &HashMap<Fun, u64>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
    validate_all: bool,
) -> Result<Expr, VirErr> {
    if args.len() != function.x.params.len() {
        return Err(error(
            &function.span,
            "mem_peak call arguments must match the function parameters",
        ));
    }
    let bound = function_bound(function, budgets, functions, layouts)?;
    // Validate only selected parameters for executable calls: unrelated arguments
    // still follow normal executable accounting, including borrows and aggregates.
    if validate_all {
        for (arg, param) in args.iter().zip(function.x.params.iter()) {
            if param.x.mode != Mode::Exec
                || !scalar(&param.x.typ)
                || !types_equal(&arg.typ, &param.x.typ)
            {
                return Err(error(
                    &arg.span,
                    "mem_peak call queries currently require scalar executable arguments",
                ));
            }
            predicate(arg, allowed)?;
        }
    }
    substitute(&bound, function, args, allowed)
}

pub(super) fn substitute(
    expression: &Expr,
    function: &Function,
    args: &Exprs,
    allowed: &HashSet<VarIdent>,
) -> Result<Expr, VirErr> {
    let bound = crate::ast_visitor::map_expr_visitor(expression, &|expr| {
        if let ExprX::Var(name) = &expr.x {
            if let Some((arg, _)) =
                args.iter().zip(function.x.params.iter()).find(|(_, p)| p.x.name == *name)
            {
                return predicate(arg, allowed);
            }
            return Err(error(&expr.span, "unbound parameter in memory contract"));
        }
        Ok(expr.clone())
    })?;
    Ok(simplify(&bound))
}

pub(super) fn lower(
    expr: &BudgetExpr,
    allowed: &HashSet<VarIdent>,
    budgets: &HashMap<Fun, u64>,
    functions: &HashMap<Fun, Function>,
    layouts: &Layouts,
) -> Result<Expr, VirErr> {
    let x = match &expr.x {
        BudgetExprX::Quantity(value) => return quantity(value, allowed),
        BudgetExprX::Literal(n) => return Ok(literal(&expr.span, *n)),
        BudgetExprX::MemSize(typ) => {
            return Ok(literal(&expr.span, layouts.size(typ, &expr.span)?));
        }
        BudgetExprX::Function(name) => {
            return Ok(literal(
                &expr.span,
                *budgets.get(name).ok_or_else(|| {
                    error(&expr.span, "mem_peak requires a declared resource contract")
                })?,
            ));
        }
        BudgetExprX::FunctionCall(name, args) => {
            let function = functions
                .get(name)
                .ok_or_else(|| error(&expr.span, "mem_peak references outside this crate"))?;
            return instantiate(function, args, allowed, budgets, functions, layouts, true);
        }
        BudgetExprX::If(cond, a, b) => ExprX::If(
            predicate(cond, allowed)?,
            lower(a, allowed, budgets, functions, layouts)?,
            Some(lower(b, allowed, budgets, functions, layouts)?),
        ),
        BudgetExprX::Add(a, b) | BudgetExprX::Mul(a, b) => ExprX::Binary(
            BinaryOp::Arith(if matches!(expr.x, BudgetExprX::Add(..)) {
                ArithOp::Add(OverflowBehavior::Allow)
            } else {
                ArithOp::Mul(OverflowBehavior::Allow)
            }),
            lower(a, allowed, budgets, functions, layouts)?,
            lower(b, allowed, budgets, functions, layouts)?,
        ),
    };
    Ok(simplify(&SpannedTyped::new(&expr.span, &int_typ(), x)))
}

pub(super) fn quantity(expr: &Expr, allowed: &HashSet<VarIdent>) -> Result<Expr, VirErr> {
    if !matches!(&*expr.typ, TypX::Int(IntRange::U(8 | 16 | 32 | 64) | IntRange::USize)) {
        return Err(error(
            &expr.span,
            "memory quantities require immutable unsigned integers of at most 64 bits",
        ));
    }
    predicate(expr, allowed)
}

pub(super) fn numeric_input(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Var(_) => true,
        ExprX::If(_, a, Some(b)) | ExprX::Binary(_, a, b) => numeric_input(a) || numeric_input(b),
        _ => false,
    }
}

pub(super) fn multiply(span: &Span, a: Expr, b: Expr) -> Expr {
    simplify(&SpannedTyped::new(
        span,
        &int_typ(),
        ExprX::Binary(BinaryOp::Arith(ArithOp::Mul(OverflowBehavior::Allow)), a, b),
    ))
}

// Internal destination credit; source budget formulas remain addition/products.
pub(super) fn subtract(span: &Span, a: Expr, b: Expr) -> Expr {
    if constant(&b) == Some(0) {
        return a;
    }
    simplify(&SpannedTyped::new(
        span,
        &int_typ(),
        ExprX::Binary(BinaryOp::Arith(ArithOp::Sub(OverflowBehavior::Allow)), a, b),
    ))
}

pub(super) fn maximum(span: &Span, a: Expr, b: Expr) -> Expr {
    if let (Some(a), Some(b)) = (constant(&a), constant(&b)) {
        return literal(span, a.max(b));
    }
    SpannedTyped::new(
        span,
        &int_typ(),
        ExprX::If(mk_ineq(span, &a, &b, InequalityOp::Ge), a, Some(b)),
    )
}
pub(super) fn minimum(span: &Span, a: Expr, b: Expr) -> Expr {
    if let (Some(a), Some(b)) = (constant(&a), constant(&b)) {
        return literal(span, a.min(b));
    }
    SpannedTyped::new(
        span,
        &int_typ(),
        ExprX::If(mk_ineq(span, &a, &b, InequalityOp::Le), a, Some(b)),
    )
}
