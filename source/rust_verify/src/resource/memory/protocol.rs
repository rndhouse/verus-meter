//! Reviewed verified vstd helpers request a body-derived workspace. Only their
//! resolved definitions may consume that workspace from an imported crate.
use crate::context::Context;
use rustc_span::Symbol;
use std::collections::HashSet;
use std::sync::Arc;
use vir::ast::{Fun, FunX, Krate, KrateX};
use vir::resource::memory::{BudgetExprX, ResourceContract, synchronization::CompilerEvidence};

pub(super) fn bind_leaf_workspaces(
    ctxt: &Context<'_>,
    krate: &mut KrateX,
    imports: &[Krate],
    evidence: &mut CompilerEvidence,
) {
    let tcx = ctxt.tcx;
    let mut reviewed = HashSet::<Fun>::new();
    let mut record = |id| {
        reviewed.insert(Arc::new(FunX { path: ctxt.def_id_to_vir_path(id) }));
    };
    if let Some(id) = tcx
        .get_diagnostic_item(Symbol::intern("verus::vstd::invariant::spend_open_invariant_credit"))
    {
        record(id);
    }
    if let Some(id) = tcx.get_diagnostic_item(Symbol::intern("verus::vstd::atomic::PAtomicUsize")) {
        for imp in tcx.inherent_impls(id) {
            for item in tcx.associated_items(*imp).in_definition_order() {
                if matches!(tcx.item_name(item.def_id).as_str(), "fetch_add" | "fetch_sub") {
                    record(item.def_id);
                }
            }
        }
    }
    for function in imports.iter().flat_map(|krate| &krate.functions) {
        if let Some(leaf) = function.x.attrs.resource_leaf
            && reviewed.contains(&function.x.name)
        {
            evidence.imported_leaves.insert(function.x.name.clone(), leaf);
        }
    }
    for function in &mut krate.functions {
        if reviewed.contains(&function.x.name) {
            evidence.measure_leaves.insert(function.x.name.clone());
            let budget =
                vir::def::Spanned::new(function.span.clone(), BudgetExprX::Literal(u64::MAX));
            Arc::make_mut(&mut Arc::make_mut(function).x.attrs).resource_contract =
                Some(ResourceContract { budget });
        }
    }
}
