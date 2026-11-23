//! Resolve protocol proof dependencies and the reviewed vstd helpers whose
//! verified bodies supply importable workspace measurements.
use crate::context::Context;
use rustc_span::Symbol;
use std::collections::HashSet;
use std::sync::Arc;
use vir::ast::{Fun, FunX, Krate, KrateX};
use vir::resource::memory::{BudgetExprX, ResourceContract, synchronization::CompilerEvidence};

/// Record which obligation would justify a bound for this concrete witness.
/// A method body can still fail verification. Discovery does not certify it.
pub(super) fn bind_holder_proofs(
    ctxt: &Context<'_>,
    krate: &KrateX,
    evidence: &mut CompilerEvidence,
) {
    use vir::ast::{FunctionKind, Mode, TypX};
    let Some(id) = ctxt
        .tcx
        .get_diagnostic_item(Symbol::intern("verus::vstd::resource::holder::BoundedHolder"))
    else {
        return;
    };
    let Some(method) = ctxt
        .tcx
        .associated_items(id)
        .in_definition_order()
        .find(|item| ctxt.tcx.item_name(item.def_id).as_str() == "population_bound")
    else {
        return;
    };
    let declaration = ctxt.def_id_to_vir_path(method.def_id);
    for f in &krate.functions {
        let FunctionKind::TraitMethodImpl {
            method, trait_typ_args, inherit_body_from: None, ..
        } = &f.x.kind
        else {
            continue;
        };
        if method.path != declaration
            || f.x.mode != Mode::Proof
            || f.x.body.is_none()
            || f.x.attrs.is_external_body
            || !f.x.typ_params.is_empty()
            || !f.x.typ_bounds.is_empty()
        {
            continue;
        }
        if let [ty] = trait_typ_args.as_slice()
            && let TypX::Datatype(dt, args, _) = &**ty
            && args.is_empty()
        {
            evidence.holder_proofs.insert(dt.clone(), f.x.name.clone());
        }
    }
}

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
