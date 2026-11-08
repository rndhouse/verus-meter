//! Check callees before callers so lifetime summaries are derived from verified bodies.

use super::model::unsupported;
use crate::ast::*;
use std::collections::{HashMap, HashSet};

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
                            if callee.x.attrs.resource_contract.is_some() {
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
