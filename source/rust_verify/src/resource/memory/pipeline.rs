//! Prepare the memory pass and erase its metadata before crate export.
//!
//! This requires mode-checked local bodies in their original VIR form, before
//! resolution inference or simplification rewrites places and control flow.

pub(crate) use super::protocol::layout_definitions;
use crate::context::Context;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Dt, Fun, KrateX, VirErr, VirErrAs};
use vir::resolution_inference::ResolutionInfo;

/// Memory diagnostics and the time at which the crate can safely be exported.
pub(crate) struct Checks {
    /// Optional source accounting traces.
    pub(crate) diagnostics: Vec<VirErrAs>,
    /// Structural proof gaps that still prevent acceptance and export.
    pub(crate) incomplete: Vec<VirErr>,
    /// Earliest publication point if every structural obligation is covered.
    pub(crate) export: crate::import_export::ExportTiming,
}

/// Prepare a crate's memory guarantees for verification alongside its other proofs.
///
/// The memory analysis checks supported operations and accounting rules, then adds
/// assertions for bounds that need proof. Remove memory-only annotations afterward,
/// leaving those assertions for Verus to verify. Optional traces explain the
/// accounting; they do not change the checks.
pub(crate) fn check(
    ctxt: &Context<'_>,
    krate: &mut KrateX,
    imports: &[vir::ast::Krate],
    memory_datatypes: &[vir::ast::Datatype],
    modes: &HashMap<Fun, Arc<ResolutionInfo>>,
    erasure: &HashMap<Fun, Arc<crate::context::ErasureInfo>>,
    args: &crate::config::Args,
) -> Result<Checks, VirErr> {
    let (global_allocator, vector, option) = identities(ctxt);
    let synchronization_types = synchronization_types(ctxt);
    let mut synchronization = synchronization_evidence(
        ctxt,
        krate,
        modes,
        erasure,
        synchronization_types,
        !args.no_lifetime,
    )?;
    super::protocol::bind_holder_proofs(krate, imports, &mut synchronization);
    super::protocol::bind_leaf_workspaces(ctxt, krate, imports, &mut synchronization);
    super::protocol::bind_workspaces(ctxt, krate, imports, modes, &mut synchronization);
    super::protocol::bind_issuers(krate, imports, &mut synchronization);
    if args.trace {
        let mut closures: Vec<_> = synchronization.concurrency.closures.values().collect();
        closures.sort_by_key(|closure| closure.id);
        for closure in closures {
            let storage = vir::resource::memory::concurrency::capture_storage(
                closure,
                memory_datatypes,
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
            use vir::resource::memory::concurrency::invocation::Invocation;
            if let Ok(invocation) = Invocation::checked(closure, &closure.span) {
                ctxt.diagnostics.borrow_mut().push(vir::ast::VirErrAs::Note(vir::messages::note(
                    &closure.span,
                    format!(
                        "memory worker invocation: {invocation:?}; remaining capture cleanup after body: {}; implicit capture order: unspecified",
                        invocation.cleans_up_after_body(),
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
    let mut incomplete = Vec::new();
    let reports = vir::resource::memory::check_crate(
        &mut krate.functions,
        memory_datatypes,
        modes,
        global_allocator,
        vector,
        option,
        &synchronization,
        &|name| reservation_constant(ctxt, name),
        &|span| {
            let mut span = span.clone();
            span.id = ctxt.spans.get_next_span_id();
            span
        },
        &mut incomplete,
    )?;
    vir::resource::memory::erase_annotations(&mut krate.functions)?;
    let export = if let Some((span, _)) = reports.iter().find(|(_, report)| report.covers_workers) {
        if args.no_verify || args.no_erasure_check || args.no_trait_conflicts {
            return Err(vir::messages::error(
                span,
                "concurrent memory bounds require verification of worker bodies and erased Rust code",
            ));
        }
        crate::import_export::ExportTiming::AfterVerification
    } else {
        crate::import_export::ExportTiming::Ordinary
    };
    let diagnostics = if args.trace && incomplete.is_empty() {
        reports.into_iter().flat_map(|(span, report)| report.diagnostics(&span)).collect()
    } else if args.trace {
        reports.into_iter().flat_map(|(_, report)| report.synchronization_diagnostics()).collect()
    } else {
        Vec::new()
    };
    Ok(Checks { diagnostics, incomplete, export })
}

/// Read the target's compile-time value only when a checked reservation uses
/// a resolved constant. Runtime calls, statics and generic substitutions do
/// not denote a single unsigned constant through this interface.
fn reservation_constant(ctxt: &Context<'_>, name: &Fun) -> Option<u64> {
    use rustc_hir::def::DefKind;
    use rustc_middle::ty::TyKind;

    let id = *ctxt.name_def_id_map.borrow().get(&name.path)?;
    let tcx = ctxt.tcx;
    if !matches!(tcx.def_kind(id), DefKind::Const { .. } | DefKind::AssocConst { .. })
        || tcx.generics_of(id).count() != 0
        || !matches!(tcx.type_of(id).skip_binder().kind(), TyKind::Uint(_))
    {
        return None;
    }
    let scalar = tcx.const_eval_poly(id).ok()?.try_to_scalar_int()?;
    scalar.to_uint(scalar.size()).try_into().ok()
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
    memory_datatypes: &[vir::ast::Datatype],
    function: &vir::ast::Function,
) -> Result<vir::ast::Function, VirErr> {
    let (global_allocator, vector, option) = identities(ctxt);
    vir::resource::memory::resolve_sizes(
        function,
        memory_datatypes,
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
    for name in [
        "Mutex",
        "MutexGuard",
        "Result",
        "verus::vstd::atomic::PAtomicBool",
        "verus::vstd::atomic::PAtomicUsize",
        "verus::vstd::atomic_ghost::AtomicBool",
        "verus::vstd::atomic_ghost::AtomicUsize",
    ] {
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
