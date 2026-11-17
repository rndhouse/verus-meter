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
    erasure: &HashMap<Fun, Arc<crate::context::ErasureInfo>>,
    trace: bool,
    lifetime_checks: bool,
) -> Result<Vec<VirErrAs>, VirErr> {
    let (global_allocator, vector, option) = identities(ctxt);
    let synchronization_types = synchronization_types(ctxt);
    let synchronization = synchronization_evidence(
        ctxt,
        krate,
        modes,
        erasure,
        synchronization_types,
        lifetime_checks,
    )?;
    if trace {
        let mut closures: Vec<_> = synchronization.concurrency.closures.values().collect();
        closures.sort_by_key(|closure| closure.id);
        for closure in closures {
            let storage = vir::resource::memory::concurrency::capture_storage(
                closure,
                &krate.datatypes,
                global_allocator.clone(),
                vector.clone(),
                option.clone(),
                &synchronization.types,
            );
            // Tracing cannot strengthen the acceptance boundary. Unsupported
            // capture layouts are diagnosed by accounting when consumed.
            let storage = match storage {
                Ok(bytes) => format!("{bytes} inline source bytes"),
                Err(_) => "inline source size unresolved".to_owned(),
            };
            ctxt.diagnostics.borrow_mut().push(vir::ast::VirErrAs::Note(vir::messages::note(
                &closure.span,
                format!(
                    "memory closure captures: {} executable fields, {storage}",
                    closure.captures.len()
                ),
            )));
            if let Some(adapter) = &closure.once_adapter {
                use vir::resource::memory::concurrency::invocation::Invocation;
                use vir::resource::memory::synchronization::flow::{Call, Terminator};
                let body_calls = adapter
                    .blocks
                    .iter()
                    .filter(|block| {
                        matches!(&block.terminator,
                        Terminator::Call { call: Call::Closure(body), .. }
                            if *body == closure.function)
                    })
                    .count();
                let checked = Invocation::checked(closure, !closure.copy, &closure.span).is_ok();
                ctxt.diagnostics.borrow_mut().push(vir::ast::VirErrAs::Note(vir::messages::note(
                    &closure.span,
                    format!(
                        "memory FnOnce adapter: {body_calls} resolved body call(s), {} arguments; checked invocation: {checked}",
                        adapter.arguments,
                    ),
                )));
            }
        }
        let mut operations: Vec<_> = synchronization.concurrency.erased_operations.iter().collect();
        operations.sort_by_key(|(id, _)| *id);
        for operation in operations.into_iter().flat_map(|(_, operations)| operations) {
            ctxt.diagnostics.borrow_mut().push(vir::ast::VirErrAs::Note(vir::messages::note(
                &operation.span,
                format!("memory executable effect: {:?}", operation.operation),
            )));
        }
        for function in krate.functions.iter().filter(|f| f.x.attrs.resource_contract.is_some()) {
            if let Some(modes) = modes.get(&function.x.name) {
                ctxt.diagnostics.borrow_mut().extend(super::sites::diagnostics(
                    function,
                    modes,
                    &krate.functions,
                    &synchronization,
                ));
            }
        }
    }
    let reports = vir::resource::memory::check_crate(
        &mut krate.functions,
        &krate.datatypes,
        modes,
        global_allocator,
        vector,
        option,
        &synchronization,
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

/// Obtain cleanup only for actual runtime synchronization. Ordinary sequential
/// proofs and type-size queries do not force additional MIR/borrow-check queries.
/// The lifetime-check MIR also retains tracked proof bookkeeping; only mode-
/// checked executable source bindings may root native synchronization identities.
/// Tracked bindings remain available for the checked custom-protocol interface.
fn synchronization_evidence(
    ctxt: &Context<'_>,
    krate: &KrateX,
    modes: &HashMap<Fun, Arc<ResolutionInfo>>,
    erasure: &HashMap<Fun, Arc<crate::context::ErasureInfo>>,
    types: vir::resource::memory::synchronization::LibraryTypes,
    lifetime_checks: bool,
) -> Result<vir::resource::memory::synchronization::CompilerEvidence, VirErr> {
    use vir::resource::memory::synchronization::{CompilerEvidence, needs_cleanup};
    let mut evidence = CompilerEvidence { types, ..Default::default() };
    for function in krate.functions.iter().filter(|f| f.x.attrs.resource_contract.is_some()) {
        let modes = modes.get(&function.x.name).map(Arc::as_ref);
        if !needs_cleanup(function, modes, &evidence.types, &krate.datatypes) {
            continue;
        }
        if !lifetime_checks {
            return Err(vir::messages::error(
                &function.span,
                "runtime synchronization memory analysis requires lifetime checking; remove --no-lifetime",
            ));
        }
        let owner = ctxt
            .name_def_id_map
            .borrow()
            .get(&function.x.name.path)
            .and_then(|id| id.as_local())
            .filter(|id| ctxt.tcx.hir_maybe_body_owned_by(*id).is_some())
            .ok_or_else(|| {
                vir::messages::error(
                    &function.span,
                    "runtime synchronization requires a local compiler body for guard cleanup",
                )
            })?;
        let mut graph = super::cleanup::lower(
            ctxt.tcx,
            owner,
            &|id| Arc::new(vir::ast::FunX { path: ctxt.def_id_to_vir_path(id) }),
            &|span| ctxt.spans.to_air_span(span),
        );
        vir::resource::memory::synchronization::attach_binding_modes(&mut graph, function, modes);
        if let Some(erasure) = erasure.get(&function.x.name) {
            evidence.concurrency.erased_operations.extend(erasure.resource_operations.clone());
            for (span, closure) in &erasure.resource_closures {
                let info = super::concurrency::closure(ctxt, *closure, span)?;
                evidence.concurrency.closures.insert(info.id, info);
            }
            super::temporaries::resolve(
                function,
                &erasure.resource_operations,
                &mut evidence.concurrency,
            );
        }
        evidence.cleanup.insert(function.x.name.clone(), graph);
    }
    for function in krate.functions.iter().filter(|f| f.x.attrs.resource_contract.is_some()) {
        if let Some(modes) = modes.get(&function.x.name) {
            super::sites::resolve(function, modes, &krate.functions, &mut evidence);
        }
    }
    Ok(evidence)
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
    for id in [
        super::concurrency::standard_join_handle(tcx),
        tcx.get_diagnostic_item(rustc_span::Symbol::intern("verus::vstd::thread::JoinHandle")),
    ]
    .into_iter()
    .flatten()
    {
        if let Some(kind) = super::intrinsics::synchronization_type(tcx, id) {
            types.insert(Dt::Path(ctxt.def_id_to_vir_path(id)), kind);
        }
    }
    types
}
