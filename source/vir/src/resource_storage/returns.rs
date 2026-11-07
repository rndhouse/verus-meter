//! Share a moved result's charge with the value it comes from.
//!
//! The result remains a destination in the model, but a parameter or local
//! handed into it does not introduce a second value. Copies and newly
//! constructed results keep independent charges. This is source-level value
//! accounting, not a claim about compiler return-slot optimization.

use super::model::unsupported;
use crate::ast::*;
use std::collections::{HashMap, HashSet};

/// Find a single source slot handed to the result on every supported tail path.
/// Forwarding calls use the callee's checked parameter/result sharing summary.
/// A join without a common source retains the conservative separate destination.
pub(super) fn source(expr: &Expr, parameters: &HashMap<Fun, usize>) -> Option<VarIdent> {
    match &expr.x {
        ExprX::Block(_, Some(tail)) => source(tail, parameters),
        ExprX::ReadPlace(place, kind) => match &place.x {
            PlaceX::Local(name)
                if matches!(kind.preliminary_kind, ReadKind::Move(_))
                    && crate::ast_util::types_equal(&place.typ, &expr.typ) =>
            {
                Some(name.clone())
            }
            PlaceX::Temporary(value) if crate::ast_util::types_equal(&value.typ, &expr.typ) => {
                source(value, parameters)
            }
            _ => None,
        },
        ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, fun, typs, impls, _),
            args,
            post_args: None,
            body: None,
        } if typs.is_empty() && impls.is_empty() => {
            let arg = args.get(*parameters.get(fun)?)?;
            if crate::ast_util::types_equal(&arg.typ, &expr.typ) {
                source(arg, parameters)
            } else {
                None
            }
        }
        ExprX::If(_, yes, Some(no)) => {
            let name = source(yes, parameters)?;
            (source(no, parameters).as_ref() == Some(&name)).then_some(name)
        }
        ExprX::Match(_, arms, _) => {
            let name = source(&arms.first()?.x.body, parameters)?;
            arms.iter()
                .all(|arm| source(&arm.x.body, parameters).as_ref() == Some(&name))
                .then_some(name)
        }
        _ => None,
    }
}

/// Results require callee summaries before checking the caller: allocation
/// ownership and parameter/result sharing are both composed through calls.
/// Ordinary call cycles are still rejected by the complete checked call graph.
pub(super) fn order(functions: &[Function]) -> Result<Vec<Function>, VirErr> {
    fn visit(
        function: &Function,
        functions: &HashMap<Fun, Function>,
        active: &mut HashSet<Fun>,
        done: &mut HashSet<Fun>,
        ordered: &mut Vec<Function>,
    ) -> Result<(), VirErr> {
        if done.contains(&function.x.name) {
            return Ok(());
        }
        if !active.insert(function.x.name.clone()) {
            return Err(unsupported(
                &function.span,
                "recursive storage contracts (including mutual recursion)",
            ));
        }
        if function.x.attrs.resource_contract.is_some() {
            if let Some(body) = &function.x.body {
                crate::ast_visitor::expr_visitor_check(body, &mut |_, expr| {
                    if let ExprX::Call {
                        target: CallTarget::Fun(CallTargetKind::Static, target, _, _, _),
                        ..
                    } = &expr.x
                    {
                        if let Some(callee) = functions.get(target) {
                            if !super::model::unit(&callee.x.outer_ret.x.typ)
                                && callee.x.attrs.resource_contract.is_some()
                            {
                                visit(callee, functions, active, done, ordered)?;
                            }
                        }
                    }
                    Ok::<(), VirErr>(())
                })?;
            }
        }
        active.remove(&function.x.name);
        done.insert(function.x.name.clone());
        ordered.push(function.clone());
        Ok(())
    }
    let map = functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    let mut active = HashSet::new();
    let mut done = HashSet::new();
    let mut ordered = Vec::new();
    for function in functions {
        visit(function, &map, &mut active, &mut done, &mut ordered)?;
    }
    Ok(ordered)
}
