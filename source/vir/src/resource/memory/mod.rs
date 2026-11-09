//! Memory budgets on mode-checked, unsimplified VIR.
//!
//! `model` defines the policy; `layout` checks concrete type sizes and struct
//! fields; `budget` resolves declared budget expressions and their dependencies;
//! `accounting` owns live/peak totals and traces; `sections` checks nested
//! workspace contracts and composes their bounds with the parent.
//! `heap` tracks allocation lifetimes; `ownership` derives transfer summaries
//! for checked helpers; `allocations` shares byte-size, transfer, replacement, and
//! retained-storage effects across containers. `vector_calls` adapts vector facts
//! at call boundaries; `vectors` handles operations and `growth` maintains erased
//! capacity/retained-byte state; `inference` derives checked entry reservations.
//! `contracts`
//! specializes declared formulas with stable scalar arguments. `symbolic`
//! turns conditional contracts into ordinary Verus proof obligations.
//! `call_graph` discovers executable edges, orders callees, and rejects cycles;
//! `execution` shares proof/spec boundaries with accounting; `summary` keeps
//! checked call facts together; `lifetime` tracks moved values;
//! `values` handles Option arms;
//! `construction` accounts for aggregate initialization; `analysis`, `places`,
//! and `calls` interpret other supported executable VIR. This
//! module validates the crate-wide call graph before publishing any reports.
//! Unsupported operations are rejected, never assigned a zero cost.
//!
//! The authoritative model is documented in `docs/verus-meter/model.md`.

mod accounting;
mod allocations;
mod analysis;
mod budget;
mod call_graph;
mod calls;
mod construction;
mod contracts;
mod execution;
mod footprint;
mod growth;
mod heap;
mod inference;
mod layout;
mod lifetime;
mod model;
mod ownership;
mod places;
mod sections;
mod spec_budget;
mod summary;
mod symbolic;
mod values;
mod vector_calls;
mod vectors;

pub use accounting::{MemoryEvent, MemoryReport};
pub use budget::{BudgetExpr, BudgetExprX};
pub use footprint::{Footprint, MemoryBudget, MemoryKind, MemorySelection};
pub(crate) use growth::resolution_modes;
pub use model::ResourceContract;

use crate::ast::*;
use crate::messages::Span;
use crate::resolution_inference::ResolutionInfo;
use std::collections::HashMap;
use std::sync::Arc;

/// Check structural rules and generate conditional obligations before export.
/// Call accounting uses declared bounds; together with the function proofs,
/// their validity follows over this acyclic executable call graph. Never rely
/// on functional termination to bound storage.
pub fn check_crate(
    functions: &mut [Function],
    datatypes: &[Datatype],
    modes: &HashMap<Fun, Arc<ResolutionInfo>>,
    global_allocator: Option<Dt>,
    vector: Option<Dt>,
    option: Option<Dt>,
    fresh_span: &dyn Fn(&Span) -> Span,
) -> Result<Vec<(Span, MemoryReport)>, VirErr> {
    let function_map = functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    let layouts = layout::Layouts::new(datatypes, global_allocator, vector, option);
    let budgets = budget::resolve(functions, &function_map, &layouts)?;
    let graph = call_graph::CallGraph::new(&function_map, modes)?;
    let mut reports = Vec::new();
    let mut summaries = HashMap::new();
    for function in &graph.order(functions)? {
        if let Some(checked) = analysis::check(
            function,
            modes.get(&function.x.name).map(Arc::as_ref),
            &function_map,
            &layouts,
            &budgets,
            &summaries,
        )? {
            summaries.insert(function.x.name.clone(), checked.summary.clone());
            graph.validate_calls(function, &checked.calls)?;
            reports.push((function.clone(), checked));
        }
    }
    // Materialize ordinary proof obligations only after checking all structural
    // rules and call cycles. No user-controlled memory counter is introduced.
    for (function, checked) in &reports {
        if checked.symbolic_bound.is_some()
            || !checked.obligations.is_empty()
            || !checked.checks.is_empty()
        {
            let updated = symbolic::instrument(
                function,
                checked.symbolic_bound.as_ref(),
                &checked.obligations,
                &checked.checks,
                &checked.growth,
                fresh_span,
            )?;
            let target = functions.iter_mut().find(|f| f.x.name == function.x.name).unwrap();
            *target = updated;
        }
    }
    Ok(reports.into_iter().map(|(f, checked)| (f.span.clone(), checked.report)).collect())
}

/// Erase metadata after the crate's structural checks and instrumentation succeed.
/// Generated conditional assertions remain in the body for normal verification;
/// metadata must never become unchecked logical assumptions.
pub fn erase_annotations(functions: &mut [Function]) -> Result<(), VirErr> {
    for function in functions {
        // Unannotated functions were checked for forbidden annotations above.
        if function.x.attrs.resource_contract.is_none() {
            continue;
        }
        if let Some(body) = &function.x.body {
            let body = crate::ast_visitor::map_expr_visitor(body, &|expr| {
                if matches!(expr.x, ExprX::ResourceAssert(_) | ExprX::ResourceSection(_)) {
                    Ok(SpannedTyped::new(
                        &expr.span,
                        &expr.typ,
                        ExprX::Block(Arc::new(vec![]), None),
                    ))
                } else {
                    Ok(expr.clone())
                }
            })?;
            Arc::make_mut(function).x.body = Some(body);
        }
    }
    Ok(())
}

/// Replace specification type queries with constants from the source memory model.
/// This runs before ordinary function checking; only compiler-tagged queries qualify.
pub fn resolve_sizes(
    function: &Function,
    datatypes: &[Datatype],
    global_allocator: Option<Dt>,
    vector: Option<Dt>,
    option: Option<Dt>,
) -> Result<Function, VirErr> {
    let layouts = layout::Layouts::new(datatypes, global_allocator, vector, option);
    crate::ast_visitor::map_function_visitor_env(
        function,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_, _, expr| resolve_size_node(expr, &layouts),
        &|_, _, stmt| Ok(vec![stmt.clone()]),
        &|_, typ| Ok(typ.clone()),
        &|_, _, place| Ok(place.clone()),
        &|_, _, pattern| Ok(pattern.clone()),
    )
}

/// Fold compiler-tagged size queries in bodies and erased budget expressions.
fn resolve_size_expression(expr: &Expr, layouts: &layout::Layouts) -> Result<Expr, VirErr> {
    crate::ast_visitor::map_expr_visitor(expr, &|expr| resolve_size_node(expr, layouts))
}

fn resolve_size_node(expr: &Expr, layouts: &layout::Layouts) -> Result<Expr, VirErr> {
    if let ExprX::Call { target: CallTarget::Fun(_, _, types, _, attrs), .. } = &expr.x {
        if attrs.resource_intrinsic == Some(ResourceIntrinsic::MemSize) {
            let bytes = layouts.size(&types[0], &expr.span)?;
            return Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Const(crate::ast_util::const_int_from_u128(bytes as u128)),
            ));
        }
    }
    Ok(expr.clone())
}
