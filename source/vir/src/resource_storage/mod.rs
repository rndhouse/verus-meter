//! Structural storage bounds on mode-checked, unsimplified VIR.
//!
//! `model` defines the policy; `layout` checks concrete type sizes and struct
//! fields; `budget` resolves declared budget expressions and their dependencies;
//! `accounting` owns live/peak totals and traces; `sections` checks nested
//! workspace contracts and composes their bounds with the parent.
//! `heap` tracks allocation lifetimes; `ownership` derives transfer summaries
//! for checked helpers; `vectors` checks reserved capacity. `contracts`
//! specializes declared formulas with stable scalar arguments. `symbolic`
//! turns conditional contracts into ordinary Verus proof obligations.
//! `returns` shares moved result charges; `values` handles Option arms;
//! `construction` accounts for aggregate initialization; `analysis`, `places`,
//! and `calls` interpret other supported executable VIR. This
//! module validates the crate-wide call graph before publishing any reports.
//! Unsupported operations are rejected, never assigned a zero cost.
//!
//! The authoritative model is documented in `docs/verus-meter/model.md`.

mod accounting;
mod analysis;
mod budget;
mod calls;
mod construction;
mod contracts;
mod heap;
mod layout;
mod model;
mod ownership;
mod places;
mod returns;
mod sections;
mod symbolic;
mod values;
mod vectors;

pub use accounting::{StorageEvent, StorageReport};
pub use budget::{BudgetExpr, BudgetExprX};
pub use model::ResourceContract;

use crate::ast::*;
use crate::messages::Span;
use crate::resolution_inference::ResolutionInfo;
use model::unsupported;
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
) -> Result<Vec<(Span, StorageReport)>, VirErr> {
    let function_map = functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    let layouts = layout::Layouts::new(datatypes, global_allocator, vector, option);
    let budgets = budget::resolve(functions, &function_map, &layouts)?;
    let mut graph = crate::scc::Graph::new();
    let mut reports = Vec::new();
    let mut returned = HashMap::new();
    let mut return_parameters = HashMap::new();
    for function in &returns::order(functions)? {
        if let Some(checked) = analysis::check(
            function,
            modes.get(&function.x.name).map(Arc::as_ref),
            &function_map,
            &layouts,
            &budgets,
            &returned,
            &return_parameters,
        )? {
            if let Some(summary) = &checked.returned {
                returned.insert(function.x.name.clone(), summary.clone());
            }
            if let Some(index) = checked.return_parameter {
                return_parameters.insert(function.x.name.clone(), index);
            }
            graph.add_node(function.x.name.clone());
            for (callee, _) in &checked.calls {
                graph.add_edge(function.x.name.clone(), callee.clone());
            }
            reports.push((function.clone(), checked));
        }
    }
    graph.compute_sccs();
    for (function, checked) in &reports {
        for (callee, span) in &checked.calls {
            if graph.in_same_scc(&function.x.name, callee) {
                return Err(unsupported(
                    span,
                    "recursive storage contracts (including mutual recursion)",
                )
                .secondary_span(&function.span));
            }
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
                &checked.report,
                checked.return_parameter,
                &layouts,
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
