//! Infer reservation requirements from length bounds and checked callees.
//!
//! These formulas are candidates, not logical facts: ordinary verification must
//! still prove every push fits. Callers then prove the inferred requirement from
//! their allocation state. Inference never assumes a bound on vector contents.

use super::{contracts, layout::Layouts, summary::FunctionSummary};
use crate::ast::*;
use crate::ast_util::int_typ;
use crate::ast_visitor::{VisitorControlFlow, ast_visitor_dfs, expr_visitor_check};
use std::collections::{HashMap, HashSet};

fn parameter(expr: &Expr, inputs: &HashSet<VarIdent>) -> Option<VarIdent> {
    let mut names = HashSet::new();
    let _: Result<(), VirErr> = expr_visitor_check(expr, &mut |_, e| {
        match &e.x {
            ExprX::Var(name) | ExprX::VarAt(name, _) if inputs.contains(name) => {
                names.insert(name.clone());
            }
            ExprX::ReadPlace(place, _) | ExprX::TwoPhaseBorrowMut(place) => {
                if let Some(name) = place_parameter(place, inputs) {
                    names.insert(name);
                }
            }
            _ => {}
        }
        Ok(())
    });
    if names.len() == 1 { names.into_iter().next() } else { None }
}

fn place_parameter(place: &Place, inputs: &HashSet<VarIdent>) -> Option<VarIdent> {
    match &place.x {
        PlaceX::Local(name) if inputs.contains(name) => Some(name.clone()),
        PlaceX::DerefMut(place) => place_parameter(place, inputs),
        PlaceX::Temporary(expr) => parameter(expr, inputs),
        _ => None,
    }
}

fn quantity(expr: &Expr, inputs: &HashSet<VarIdent>) -> Option<Expr> {
    match &expr.x {
        ExprX::Unary(UnaryOp::Clip { .. }, inner) => quantity(inner, inputs),
        ExprX::Const(Constant::Int(_)) if contracts::constant(expr).is_some() => {
            Some(SpannedTyped::new(&expr.span, &int_typ(), expr.x.clone()))
        }
        _ => contracts::quantity(expr, inputs).ok(),
    }
}

fn merge(requirements: &mut HashMap<VarIdent, Expr>, name: VarIdent, value: Expr) {
    let value = if let Some(old) = requirements.get(&name) {
        contracts::maximum(&value.span, old.clone(), value.clone())
    } else {
        value
    };
    requirements.insert(name, value);
}

/// Recognize an upper bound on length. Equality and inclusive comparisons need
/// one additional slot for a push. This only proposes an allocation requirement;
/// the original logical condition remains responsible for proving the length.
fn bounds(
    expression: &Expr,
    vectors: &HashSet<VarIdent>,
    scalars: &HashSet<VarIdent>,
) -> HashMap<VarIdent, Expr> {
    let mut result = HashMap::new();
    let _: Result<(), VirErr> = expr_visitor_check(expression, &mut |_, expr| {
        let ExprX::Binary(op, lhs, rhs) = &expr.x else { return Ok(()) };
        let extra = match op {
            BinaryOp::Inequality(InequalityOp::Lt) => 0,
            BinaryOp::Inequality(InequalityOp::Le) | BinaryOp::Eq(_) => 1,
            _ => return Ok(()),
        };
        let ExprX::Call { target: CallTarget::Fun(_, target, _, _, attrs), args, .. } = &lhs.x
        else {
            return Ok(());
        };
        if attrs.resource_intrinsic != Some(ResourceIntrinsic::VecLen)
            && *target != crate::fun!(CrateId::Vstd => "std_specs", "vec"; "spec_vec_len")
        {
            return Ok(());
        }
        if args.len() == 1 {
            if let (Some(name), Some(value)) =
                (parameter(&args[0], vectors), quantity(rhs, scalars))
            {
                merge(
                    &mut result,
                    name,
                    contracts::add(&expr.span, value, contracts::literal(&expr.span, extra)),
                );
            }
        }
        Ok(())
    });
    result
}

/// Infer entry reservations bottom-up over the acyclic checked call graph.
/// Fixed budgets that can cover the bounded replacement keep ordinary growth;
/// otherwise a length bound proposes a reservation checked at every caller.
pub(super) fn infer(
    function: &Function,
    layouts: &Layouts,
    summaries: &HashMap<Fun, FunctionSummary>,
    functions: &HashMap<Fun, Function>,
    bound: &Expr,
    modes: &HashMap<VarIdent, Mode>,
) -> Result<HashMap<VarIdent, Expr>, VirErr> {
    let vectors: HashSet<_> = function
        .x
        .params
        .iter()
        .filter(|p| layouts.vector(&p.x.typ) || layouts.borrowed_vector(&p.x.typ).is_some())
        .map(|p| p.x.name.clone())
        .collect();
    if vectors.is_empty() {
        return Ok(HashMap::new());
    }
    let scalars = contracts::inputs(function);
    let mut lengths = HashMap::new();
    for require in function.x.require.iter() {
        for (name, value) in bounds(require, &vectors, &scalars) {
            merge(&mut lengths, name, value);
        }
    }
    let parameters = function
        .x
        .params
        .iter()
        .filter(|p| p.x.mode == Mode::Exec)
        .try_fold(0u64, |total, p| {
            layouts.size(&p.x.typ, &p.span).map(|n| total.saturating_add(n))
        })?;
    let mut inference = Inference {
        function,
        layouts,
        summaries,
        functions,
        bound,
        vectors,
        scalars,
        parameters,
        modes,
        requirements: HashMap::new(),
    };
    if let Some(body) = &function.x.body {
        inference.walk(body, &lengths)?;
    }
    Ok(inference.requirements)
}

struct Inference<'a> {
    /// Input identities and types of the function being summarized.
    function: &'a Function,
    /// Model element and handle sizes used to select growth or reservation.
    layouts: &'a Layouts,
    /// Already analyzed callees, ordered before their callers.
    summaries: &'a HashMap<Fun, FunctionSummary>,
    /// Callee parameters for substituting inferred formulas at calls.
    functions: &'a HashMap<Fun, Function>,
    /// The declared allowance; inference never increases it.
    bound: &'a Expr,
    /// Vector parameters whose entry allocations belong to callers.
    vectors: HashSet<VarIdent>,
    /// Immutable executable inputs allowed in exported formulas.
    scalars: HashSet<VarIdent>,
    /// Entry parameter storage used to select an inference strategy.
    parameters: u64,
    /// Candidate entry minima, independently checked by body and caller proofs.
    requirements: HashMap<VarIdent, Expr>,
    /// Resolved modes keep inferred requirements out of erased declarations.
    modes: &'a HashMap<VarIdent, Mode>,
}

impl Inference<'_> {
    fn walk(&mut self, body: &Expr, lengths: &HashMap<VarIdent, Expr>) -> Result<(), VirErr> {
        let mut lengths = lengths.clone();
        let modes = self.modes;
        let result = ast_visitor_dfs(
            body,
            &mut air::scope_map::ScopeMap::new(),
            &mut (),
            &mut |_, _, expr| {
                if super::execution::ignored_expression(expr) {
                    return VisitorControlFlow::Return;
                }
                if let ExprX::If(condition, yes, no) = &expr.x {
                    let before = std::mem::take(&mut self.requirements);
                    let mut branch = lengths.clone();
                    branch.extend(bounds(condition, &self.vectors, &self.scalars));
                    if let Err(err) = self.walk(yes, &branch) {
                        return VisitorControlFlow::Stop(err);
                    }
                    let yes = std::mem::take(&mut self.requirements);
                    if let Some(no) = no {
                        if let Err(err) = self.walk(no, &lengths) {
                            return VisitorControlFlow::Stop(err);
                        }
                    }
                    let no = std::mem::replace(&mut self.requirements, before);
                    let guard = contracts::predicate(condition, &self.scalars).ok();
                    let names: HashSet<_> = yes.keys().chain(no.keys()).cloned().collect();
                    for name in names {
                        let zero = contracts::literal(&expr.span, 0);
                        let a = yes.get(&name).unwrap_or(&zero).clone();
                        let b = no.get(&name).unwrap_or(&zero).clone();
                        let required = if let Some(guard) = &guard {
                            super::growth::select(&expr.span, guard.clone(), a, b)
                        } else {
                            contracts::maximum(&expr.span, a, b)
                        };
                        merge(&mut self.requirements, name, required);
                    }
                    return VisitorControlFlow::Return;
                }
                if let ExprX::Loop { cond: Some(cond), body, .. } = &expr.x {
                    let mut local = lengths.clone();
                    local.extend(bounds(cond, &self.vectors, &self.scalars));
                    return match self.walk(body, &local) {
                        Ok(()) => VisitorControlFlow::Return,
                        Err(err) => VisitorControlFlow::Stop(err),
                    };
                }
                let ExprX::Call { target: CallTarget::Fun(_, target, _, _, attrs), args, .. } =
                    &expr.x
                else {
                    return VisitorControlFlow::Recurse;
                };
                if attrs.resource_intrinsic == Some(ResourceIntrinsic::VecPush) && !args.is_empty()
                {
                    if let Some(name) = parameter(&args[0], &self.vectors) {
                        if let Some(required) = lengths.get(&name) {
                            let param =
                                self.function.x.params.iter().find(|p| p.x.name == name).unwrap();
                            let typ =
                                self.layouts.borrowed_vector(&param.x.typ).unwrap_or(&param.x.typ);
                            let element = match self.layouts.vector_element(typ, &expr.span) {
                                Ok(n) => n,
                                Err(e) => return VisitorControlFlow::Stop(e),
                            };
                            let worst_length = contracts::subtract(
                                &expr.span,
                                required.clone(),
                                contracts::literal(&expr.span, 1),
                            );
                            let replacement =
                                super::growth::grown_capacity(&expr.span, worst_length, element);
                            // Select a candidate strategy, not a memory guarantee.
                            // Normal accounting still checks all locals, retained
                            // buffers, and dynamic budget expressions.
                            let fits = element == 0
                                || match (
                                    contracts::constant(self.bound),
                                    contracts::constant(&replacement),
                                ) {
                                    (Some(budget), Some(capacity)) => {
                                        u128::from(capacity) * u128::from(element)
                                            + u128::from(self.parameters)
                                            <= u128::from(budget)
                                    }
                                    (None, _) => true,
                                    _ => false,
                                };
                            if !fits {
                                merge(&mut self.requirements, name.clone(), required.clone());
                            }
                            lengths.insert(
                                name,
                                contracts::add(
                                    &expr.span,
                                    required.clone(),
                                    contracts::literal(&expr.span, 1),
                                ),
                            );
                        }
                    }
                } else if let Some(summary) = self.summaries.get(target) {
                    let callee = &self.functions[target];
                    for (index, required) in &summary.reservations {
                        if let Some(name) = parameter(&args[*index], &self.vectors) {
                            match contracts::substitute(required, callee, args, &self.scalars) {
                                Ok(required) => merge(&mut self.requirements, name, required),
                                Err(err) => return VisitorControlFlow::Stop(err),
                            }
                        }
                    }
                }
                VisitorControlFlow::Recurse
            },
            &mut |_, _, stmt| {
                if super::execution::ignored_statement(stmt, modes) {
                    VisitorControlFlow::Return
                } else {
                    VisitorControlFlow::Recurse
                }
            },
            &mut |_, _, _| VisitorControlFlow::Recurse,
            &mut |_, _, _, _| VisitorControlFlow::Recurse,
            &mut |_, _, _| VisitorControlFlow::Recurse,
        );
        if let VisitorControlFlow::Stop(err) = result { Err(err) } else { Ok(()) }
    }
}
