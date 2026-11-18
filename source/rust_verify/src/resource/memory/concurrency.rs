//! Identify native concurrent operations by their defining library and trait.

use crate::verus_items::{RustItem, get_rust_item};
use rustc_middle::ty::{GenericArgsRef, TyCtxt, TyKind};
use rustc_span::{Symbol, def_id::DefId};
use vir::resource::memory::concurrency::Operation;

/// Resolve the public standard join type even when it appears only in a size
/// query. The real Mutex diagnostic item anchors the standard library crate;
/// the final resolved type must also match its reviewed Rust item identity.
pub(super) fn standard_join_handle(tcx: TyCtxt<'_>) -> Option<DefId> {
    let mutex = tcx.get_diagnostic_item(Symbol::intern("Mutex"))?;
    let root = DefId { krate: mutex.krate, index: rustc_span::def_id::CRATE_DEF_INDEX };
    let thread = tcx
        .module_children(root)
        .iter()
        .find(|item| item.ident.name.as_str() == "thread")?
        .res
        .opt_def_id()?;
    let handle = tcx
        .module_children(thread)
        .iter()
        .find(|item| item.ident.name.as_str() == "JoinHandle")?
        .res
        .opt_def_id()?;
    (get_rust_item(tcx, handle) == Some(RustItem::ThreadJoinHandle)).then_some(handle)
}

pub(crate) fn operation<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: DefId,
    arguments: GenericArgsRef<'tcx>,
) -> Option<Operation> {
    let diagnostic = |name| tcx.is_diagnostic_item(Symbol::intern(name), id);
    if diagnostic("verus::vstd::thread::spawn") {
        return Some(Operation::VstdSpawn);
    }
    if diagnostic("verus::vstd::thread::JoinHandle::join") {
        return Some(Operation::VstdJoin);
    }
    if get_rust_item(tcx, id) == Some(RustItem::ThreadSpawn) {
        return Some(Operation::StdSpawn);
    }
    let (receiver, defining_trait) = if let Some(imp) = tcx.impl_of_assoc(id) {
        (
            tcx.type_of(imp).skip_binder(),
            tcx.trait_impl_of_assoc(id).map(|imp| tcx.impl_trait_ref(imp).skip_binder().def_id),
        )
    } else {
        (arguments.types().next()?, Some(tcx.trait_of_assoc(id)?))
    };
    let TyKind::Adt(adt, _) = receiver.kind() else { return None };
    let name = tcx.item_name(id);
    if get_rust_item(tcx, adt.did()) == Some(RustItem::ThreadJoinHandle)
        && defining_trait.is_none()
        && name.as_str() == "join"
    {
        return Some(Operation::StdJoin);
    }
    if !tcx.is_diagnostic_item(Symbol::intern("Arc"), adt.did()) {
        return None;
    }
    match (defining_trait, name.as_str()) {
        (None, "new") => Some(Operation::ArcNew),
        (None, "into_inner") => Some(Operation::ArcIntoInner),
        (Some(tr), "clone") if Some(tr) == tcx.lang_items().clone_trait() => {
            Some(Operation::ArcClone)
        }
        (Some(tr), "deref") if Some(tr) == tcx.lang_items().deref_trait() => {
            Some(Operation::ArcBorrow)
        }
        (Some(tr), "drop") if Some(tr) == tcx.lang_items().drop_trait() => Some(Operation::ArcDrop),
        _ => None,
    }
}

/// Recompute executable captures with rustc's existing minimal-capture analysis.
/// Lifetime MIR deliberately forges the original capture shape for checking
/// tracked code; those synthetic fields are not a runtime closure layout.
pub(super) fn closure(
    ctxt: &crate::context::Context<'_>,
    owner: rustc_span::def_id::LocalDefId,
    span: &vir::messages::Span,
) -> Result<vir::resource::memory::concurrency::Closure, vir::ast::VirErr> {
    use rustc_hir::{ExprKind, Node};
    use rustc_middle::ty;
    use vir::resource::memory::{
        concurrency::{Capture, CaptureMode, Closure},
        synchronization::flow,
    };
    let tcx = ctxt.tcx;
    let Node::Expr(expr) = tcx.hir_node_by_def_id(owner) else {
        return Err(vir::messages::error(span, "worker capture analysis requires a closure body"));
    };
    let ExprKind::Closure(source) = expr.kind else {
        return Err(vir::messages::error(
            span,
            "worker capture analysis requires a closure expression",
        ));
    };
    let typeck = tcx.typeck(owner);
    let ty::Closure(_, args) = typeck.expr_ty(expr).kind() else {
        return Err(vir::messages::error(span, "worker requires a concrete synchronous closure"));
    };
    let analysis = rustc_mir_build_verus::upvar::compute_captures_accounting_for_ghost(
        tcx,
        tcx.param_env(owner),
        expr,
        owner,
        typeck,
        rustc_mir_build_verus::upvar::CapturePurpose::Runtime,
    );
    let original = tcx.closure_captures(owner);
    let capture_paths = |place: &rustc_middle::hir::place::Place<'_>| {
        use rustc_middle::hir::place::{PlaceBase, ProjectionKind};
        let PlaceBase::Upvar(root) = place.base else { return None };
        let mut typ = place.base_ty;
        let mut path = Vec::new();
        for projection in &place.projections {
            match projection.kind {
                ProjectionKind::Deref => path.push(flow::Projection::Deref),
                ProjectionKind::Field(field, variant) => {
                    if matches!(typ.kind(), ty::Adt(adt, _) if adt.is_enum()) {
                        path.push(flow::Projection::Variant(variant.index()));
                    }
                    path.push(flow::Projection::Field(field.index()));
                }
                _ => return None,
            }
            typ = projection.ty;
        }
        Some((root.var_path.hir_id, path))
    };
    let runtime: Vec<_> =
        analysis.closure_min_captures.values().flat_map(|caps| caps.iter()).collect();
    if runtime.len() != analysis.upvar_tys.len() {
        return Err(vir::messages::error(span, "incomplete compiler capture type information"));
    }
    let mut captures = Vec::new();
    for (capture, typ) in runtime.into_iter().zip(analysis.upvar_tys) {
        if let ty::Adt(adt, _) = typ.peel_refs().kind()
            && tcx
                .is_diagnostic_item(Symbol::intern("verus::verus_builtin::DummyCapture"), adt.did())
        {
            // The macro inserts this cfg(verus_keep_ghost) lifetime sentinel;
            // it is absent from executable Rust after proof erasure.
            continue;
        }
        let (root, path) = capture_paths(&capture.place).ok_or_else(|| {
            vir::messages::error(span, "unsupported executable capture projection")
        })?;
        let source = crate::rust_to_vir_base::local_to_var(&capture.var_ident, root.local_id);
        let body_place = original.iter().enumerate().find_map(|(index, original)| {
            let (original_root, original_path) = capture_paths(&original.place)?;
            if root != original_root || !path.starts_with(&original_path) {
                return None;
            }
            let mut projection = Vec::new();
            if args.as_closure().kind() != ty::ClosureKind::FnOnce {
                projection.push(flow::Projection::Deref);
            }
            projection.push(flow::Projection::Field(index));
            projection.extend_from_slice(&path[original_path.len()..]);
            Some(flow::Place { local: 1, projection })
        });
        let mode = match capture.info.capture_kind {
            ty::UpvarCapture::ByValue
                if tcx
                    .type_is_copy_modulo_regions(ty::TypingEnv::post_analysis(tcx, owner), typ) =>
            {
                CaptureMode::Copy
            }
            ty::UpvarCapture::ByValue => CaptureMode::Move,
            ty::UpvarCapture::ByRef(_) => CaptureMode::Borrow,
            _ => return Err(vir::messages::error(span, "unsupported worker capture kind")),
        };
        let convert = |typ| {
            crate::rust_to_vir_base::mid_ty_to_vir(
                tcx,
                &ctxt.verus_items,
                None::<&mut std::collections::HashMap<_, _>>,
                owner.to_def_id(),
                expr.span,
                typ,
                None,
            )
        };
        let source_typ = convert(&capture.place.base_ty)?;
        let typ = convert(&typ)?;
        captures.push(Capture { source, source_typ, projection: path, typ, mode, body_place });
    }
    let function = |id| std::sync::Arc::new(vir::ast::FunX { path: ctxt.def_id_to_vir_path(id) });
    let body = super::cleanup::lower(tcx, owner, &function, &|span| ctxt.spans.to_air_span(span));
    Ok(Closure {
        id: owner.local_def_index.index(),
        function: function(owner.to_def_id()),
        kind: match args.as_closure().kind() {
            ty::ClosureKind::Fn => vir::ast::ClosureKind::Fn,
            ty::ClosureKind::FnMut => vir::ast::ClosureKind::FnMut,
            ty::ClosureKind::FnOnce => vir::ast::ClosureKind::FnOnce,
        },
        span: span.clone(),
        captures,
        by_move: matches!(source.capture_clause, rustc_hir::CaptureBy::Value { .. }),
        copy: tcx.type_is_copy_modulo_regions(
            ty::TypingEnv::post_analysis(tcx, owner),
            typeck.expr_ty(expr),
        ),
        body,
    })
}
