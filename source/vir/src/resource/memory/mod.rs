//! Memory budgets on mode-checked, unsimplified VIR.
//!
//! `model` defines the policy; `layout` checks concrete type sizes and struct
//! fields; `budget` resolves declared budget expressions and their dependencies;
//! `accounting` owns live/peak totals and traces; `sections` checks nested
//! workspace contracts and composes their bounds with the parent.
//! `heap` tracks allocation lifetimes; `shared` retains canonical strong backing
//! independently of inline handles; `ownership` derives transfer summaries
//! for checked helpers; `allocations` shares byte-size, transfer, replacement, and
//! retained-storage effects across containers. `vector_calls` adapts vector facts
//! at call boundaries; `vectors` handles operations and `growth` maintains erased
//! capacity/retained-byte state; `inference` derives checked entry reservations.
//! `children` transfers and replaces fixed child ownership without copying allocations.
//! `paths` resolves fixed child owners for operations, reservations, and call effects.
//! `elements` maintains runtime child-footprint sums and ownership capture across calls.
//! `projections` borrows indexed child shapes and returns their allocation effects to those sums.
//! `loops` shares loop structure and boundaries between inductive body proofs
//! and the ownership summaries consumed by callers.
//! `contracts`
//! specializes declared formulas with stable scalar arguments. `symbolic`
//! turns conditional contracts into ordinary Verus proof obligations.
//! `call_graph` discovers executable edges, orders callees, and rejects cycles;
//! `execution` shares proof/spec boundaries with accounting; `summary` keeps
//! checked call facts together; `lifetime` tracks moved values;
//! `control` propagates lexical exits with detached results and path histories;
//! `values` handles Option arms;
//! `construction` accounts for aggregate initialization; `analysis`, `places`,
//! and `calls` interpret other supported executable VIR. This
//! module validates the crate-wide call graph before publishing any reports.
//! Unsupported operations are rejected, never assigned a zero cost.
//!
//! The authoritative model is documented in `docs/model.md`.

mod accounting;
mod allocations;
mod analysis;
mod boxed_slices;
mod budget;
mod call_graph;
mod calls;
mod children;
mod closures;
pub mod concurrency;
mod construction;
mod contracts;
mod control;
mod elements;
mod execution;
mod extraction;
mod footprint;
mod for_loops;
mod growth;
mod heap;
mod inference;
mod iterators;
mod layout;
mod lifetime;
mod loops;
mod metadata;
mod model;
mod ownership;
mod paths;
mod places;
mod projections;
mod provenance;
mod sections;
mod shared;
mod spec_budget;
mod summary;
mod symbolic;
pub mod synchronization;
mod temporaries;
mod transfer;
mod values;
mod vector_calls;
mod vectors;
mod workers;

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
    synchronization: &synchronization::CompilerEvidence,
    fresh_span: &dyn Fn(&Span) -> Span,
) -> Result<Vec<(Span, MemoryReport)>, VirErr> {
    for function in functions.iter_mut() {
        let empty = HashMap::new();
        let modes = modes.get(&function.x.name).map(|modes| &modes.var_modes).unwrap_or(&empty);
        *function = for_loops::prepare(function, modes, fresh_span)?;
    }
    let function_map = functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    let graph = call_graph::CallGraph::new(&function_map, modes, &synchronization.concurrency)?;
    let ordered = graph.order(functions)?;
    for function in functions.iter().filter(|f| f.x.attrs.resource_contract.is_some()) {
        let empty = HashMap::new();
        let resolution = modes.get(&function.x.name).map(Arc::as_ref);
        let modes = resolution.map(|modes| &modes.var_modes).unwrap_or(&empty);
        if synchronization::needs_cleanup(function, resolution, &synchronization.types, datatypes)
            && !synchronization.cleanup.contains_key(&function.x.name)
        {
            return Err(model::unsupported(
                &function.span,
                "runtime synchronization without compiler-derived guard cleanup evidence",
            ));
        }
        synchronization::reject_unaccounted(function, modes, &synchronization.types, datatypes)?;
        concurrency::sites::validate(function, modes, functions, synchronization)?;
    }
    let layouts = layout::Layouts::new(datatypes, global_allocator, vector, option)
        .with_synchronization_types(&synchronization.types)
        .with_closures(&synchronization.concurrency);
    let budgets = budget::resolve(functions, &function_map, &layouts)?;
    let mut reports = Vec::new();
    let mut summaries = HashMap::new();
    for function in &ordered {
        if let Some(checked) = analysis::check(
            function,
            modes.get(&function.x.name).map(Arc::as_ref),
            &function_map,
            &layouts,
            &budgets,
            &summaries,
            &synchronization.concurrency,
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
            || !checked.growth.single_visit_loops.is_empty()
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
                if matches!(
                    expr.x,
                    ExprX::ResourceAssert(_)
                        | ExprX::ResourceAssertCurrent(_)
                        | ExprX::ResourceSection(_)
                ) {
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
    synchronization_types: &synchronization::LibraryTypes,
) -> Result<Function, VirErr> {
    let layouts = layout::Layouts::new(datatypes, global_allocator, vector, option)
        .with_synchronization_types(synchronization_types);
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
        if let Some(query @ (ResourceIntrinsic::ValueSize | ResourceIntrinsic::RefSize)) =
            attrs.resource_intrinsic
        {
            let bytes = match query {
                ResourceIntrinsic::ValueSize => layouts.value_size(&types[0], &expr.span)?,
                ResourceIntrinsic::RefSize => layouts.ref_size(&types[0], &expr.span)?,
                _ => unreachable!(),
            };
            return Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Const(crate::ast_util::const_int_from_u128(bytes as u128)),
            ));
        }
    }
    Ok(expr.clone())
}
