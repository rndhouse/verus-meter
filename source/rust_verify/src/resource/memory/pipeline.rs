//! Prepare the memory pass and erase its metadata before crate export.
//!
//! This requires mode-checked local bodies in their original VIR form, before
//! resolution inference or simplification rewrites places and control flow.

use crate::context::Context;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Dt, Fun, KrateX, VirErr, VirErrAs};
use vir::resolution_inference::ResolutionInfo;

pub(crate) fn check(
    ctxt: &Context<'_>,
    krate: &mut KrateX,
    modes: &HashMap<Fun, Arc<ResolutionInfo>>,
    trace: bool,
) -> Result<Vec<VirErrAs>, VirErr> {
    let global_allocator =
        ctxt.tcx.lang_items().global_alloc_ty().map(|id| Dt::Path(ctxt.def_id_to_vir_path(id)));
    let diagnostic_type = |name| {
        ctxt.tcx
            .get_diagnostic_item(rustc_span::Symbol::intern(name))
            .map(|id| Dt::Path(ctxt.def_id_to_vir_path(id)))
    };
    let reports = vir::resource::memory::check_crate(
        &mut krate.functions,
        &krate.datatypes,
        modes,
        global_allocator,
        diagnostic_type("Vec"),
        diagnostic_type("Option"),
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
