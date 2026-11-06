//! Structural storage bounds on mode-checked, unsimplified VIR.
//!
//! `model` defines the policy; `layout` checks concrete type sizes and struct
//! fields; `budget` resolves declared budget expressions and their dependencies;
//! `accounting` owns live/peak totals and traces; `sections` checks nested
//! workspace contracts and composes their bounds with the parent.
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
mod layout;
mod model;
mod places;
mod sections;

pub use accounting::{StorageEvent, StorageReport};
pub use budget::{BudgetExpr, BudgetExprX};
pub use model::ResourceContract;

use crate::ast::*;
use crate::messages::Span;
use crate::resolution_inference::ResolutionInfo;
use model::unsupported;
use std::collections::HashMap;
use std::sync::Arc;

/// Check every local contract before exporting any summary. Call accounting
/// uses declared bounds, whose validity follows by induction over this acyclic
/// executable call graph. Never rely on functional termination to bound storage.
pub fn check_crate(
    functions: &[Function],
    datatypes: &[Datatype],
    modes: &HashMap<Fun, Arc<ResolutionInfo>>,
) -> Result<Vec<(Span, StorageReport)>, VirErr> {
    let function_map = functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    let layouts = layout::Layouts::new(datatypes);
    let budgets = budget::resolve(functions, &function_map, &layouts)?;
    let mut graph = crate::scc::Graph::new();
    let mut reports = Vec::new();
    for function in functions {
        if let Some(checked) = analysis::check(
            function,
            modes.get(&function.x.name).map(Arc::as_ref),
            &function_map,
            &layouts,
            &budgets,
        )? {
            graph.add_node(function.x.name.clone());
            for (callee, _) in &checked.calls {
                graph.add_edge(function.x.name.clone(), callee.clone());
            }
            reports.push((function, checked));
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
    Ok(reports.into_iter().map(|(f, checked)| (f.span.clone(), checked.report)).collect())
}

/// Erase resource annotations only after the entire crate's storage checks succeed.
/// They cannot be exported as unchecked claims or become logical assumptions.
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
