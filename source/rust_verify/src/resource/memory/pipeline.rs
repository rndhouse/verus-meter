//! Prepare the memory pass and erase its metadata before crate export.
//!
//! This requires mode-checked local bodies in their original VIR form, before
//! resolution inference or simplification rewrites places and control flow.

use crate::context::Context;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Dt, Fun, KrateX, VirErr, VirErrAs};
use vir::resolution_inference::ResolutionInfo;

/// Prepare a crate's memory guarantees for verification alongside its other proofs.
///
/// The memory analysis checks supported operations and accounting rules, then adds
/// assertions for bounds that need proof. Remove memory-only annotations afterward,
/// leaving those assertions for Verus to verify. Optional traces explain the
/// accounting; they do not change the checks.
pub(crate) fn check(
    ctxt: &Context<'_>,
    krate: &mut KrateX,
    modes: &HashMap<Fun, Arc<ResolutionInfo>>,
    trace: bool,
) -> Result<Vec<VirErrAs>, VirErr> {
    let (global_allocator, vector, option) = identities(ctxt);
    let synchronization_types = synchronization_types(ctxt);
    let reports = vir::resource::memory::check_crate(
        &mut krate.functions,
        &krate.datatypes,
        modes,
        global_allocator,
        vector,
        option,
        &synchronization_types,
        &|span| {
            let mut span = span.clone();
            span.id = ctxt.spans.get_next_span_id();
            span
        },
    )?;
    vir::resource::memory::erase_annotations(&mut krate.functions)?;
    Ok(if trace {
        reports.into_iter().flat_map(|(span, report)| report.diagnostics(&span)).collect()
    } else {
        Vec::new()
    })
}

/// Identify the standard library types whose memory behavior the model understands.
///
/// Use compiler identities so a user-defined type named `Vec` or `Option` cannot
/// accidentally receive the standard library's accounting rules.
fn identities(ctxt: &Context<'_>) -> (Option<Dt>, Option<Dt>, Option<Dt>) {
    let global_allocator =
        ctxt.tcx.lang_items().global_alloc_ty().map(|id| Dt::Path(ctxt.def_id_to_vir_path(id)));
    let diagnostic_type = |name| {
        ctxt.tcx
            .get_diagnostic_item(rustc_span::Symbol::intern(name))
            .map(|id| Dt::Path(ctxt.def_id_to_vir_path(id)))
    };
    (global_allocator, diagnostic_type("Vec"), diagnostic_type("Option"))
}

/// Turn memory-size queries into numbers that ordinary Verus proofs can use.
///
/// Sizes come from the source-level memory model, not machine layout. Resolving
/// them before ordinary function checks lets specifications use `value_size` and
/// `ref_size` without teaching the rest of Verus about memory accounting.
pub(crate) fn resolve_sizes(
    ctxt: &Context<'_>,
    krate: &KrateX,
    function: &vir::ast::Function,
) -> Result<vir::ast::Function, VirErr> {
    let (global_allocator, vector, option) = identities(ctxt);
    vir::resource::memory::resolve_sizes(
        function,
        &krate.datatypes,
        global_allocator,
        vector,
        option,
        &synchronization_types(ctxt),
    )
}

/// Register the library definitions even when a type appears only in a budget.
/// `name_def_id_map` is not exhaustive: nested type translation can intentionally
/// avoid registering paths there. Acquire signatures identify the poison wrappers
/// without trusting source names or relying on a runtime use of those types.
fn synchronization_types(
    ctxt: &Context<'_>,
) -> vir::resource::memory::synchronization::LibraryTypes {
    use rustc_middle::ty::{Ty, TyKind};
    use vir::resource::memory::synchronization::LibraryTypes;
    fn record<'tcx>(ctxt: &Context<'tcx>, typ: Ty<'tcx>, types: &mut LibraryTypes) {
        if let TyKind::Adt(adt, arguments) = typ.kind() {
            if let Some(kind) = super::intrinsics::synchronization_type(ctxt.tcx, adt.did()) {
                types.insert(Dt::Path(ctxt.def_id_to_vir_path(adt.did())), kind);
            }
            for argument in arguments.types() {
                record(ctxt, argument, types);
            }
        }
    }
    let tcx = ctxt.tcx;
    let mut types = LibraryTypes::new();
    for name in ["Mutex", "MutexGuard", "Result"] {
        if let Some(id) = tcx.get_diagnostic_item(rustc_span::Symbol::intern(name))
            && let Some(kind) = super::intrinsics::synchronization_type(tcx, id)
        {
            types.insert(Dt::Path(ctxt.def_id_to_vir_path(id)), kind);
            if name == "Mutex" {
                for imp in tcx.inherent_impls(id) {
                    for method in tcx.associated_items(*imp).in_definition_order() {
                        if matches!(tcx.item_name(method.def_id).as_str(), "lock" | "try_lock") {
                            record(
                                ctxt,
                                tcx.fn_sig(method.def_id).skip_binder().output().skip_binder(),
                                &mut types,
                            );
                        }
                    }
                }
            }
        }
    }
    types
}
