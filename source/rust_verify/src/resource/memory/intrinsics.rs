//! Identify supported operations using compiler identities, including through aliases.

use crate::verus_items::RustItem;
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use vir::ast::ResourceIntrinsic;

pub(crate) fn call(
    tcx: TyCtxt<'_>,
    id: DefId,
    rust_item: Option<RustItem>,
) -> Option<ResourceIntrinsic> {
    if let Some(intrinsic) = option_intrinsic(tcx, id) {
        Some(intrinsic)
    } else if let Some(intrinsic) = vec_intrinsic(tcx, id) {
        Some(intrinsic)
    } else if rust_item == Some(RustItem::BoxNew) {
        Some(ResourceIntrinsic::BoxNew)
    } else if tcx.is_diagnostic_item(rustc_span::Symbol::intern("mem_drop"), id) {
        Some(ResourceIntrinsic::HeapDrop)
    } else {
        (tcx.lang_items().slice_len_fn() == Some(id)).then_some(ResourceIntrinsic::SliceLen)
    }
}

// Identify inherent Vec operations by the compiler's Vec identity, so aliases
// work and unrelated methods with the same names cannot acquire resource rules.
fn vec_intrinsic(tcx: TyCtxt<'_>, id: DefId) -> Option<vir::ast::ResourceIntrinsic> {
    let imp = tcx.impl_of_assoc(id)?;
    if tcx.trait_impl_of_assoc(imp).is_some() {
        return None;
    }
    let TyKind::Adt(adt, _) = tcx.type_of(imp).skip_binder().kind() else {
        return None;
    };
    if !tcx.is_diagnostic_item(rustc_span::Symbol::intern("Vec"), adt.did()) {
        return None;
    }
    use vir::ast::ResourceIntrinsic::*;
    match tcx.item_name(id).as_str() {
        "new" => Some(VecNew),
        "with_capacity" => Some(VecWithCapacity),
        "push" => Some(VecPush),
        "pop" => Some(VecPop),
        "len" => Some(VecLen),
        "as_slice" => Some(VecAsSlice),
        "as_mut_slice" => Some(VecAsMutSlice),
        _ => None,
    }
}

fn option_intrinsic(tcx: TyCtxt<'_>, id: DefId) -> Option<vir::ast::ResourceIntrinsic> {
    let imp = tcx.impl_of_assoc(id)?;
    if tcx.trait_impl_of_assoc(imp).is_some() {
        return None;
    }
    let TyKind::Adt(adt, _) = tcx.type_of(imp).skip_binder().kind() else {
        return None;
    };
    if !tcx.is_diagnostic_item(rustc_span::Symbol::intern("Option"), adt.did()) {
        return None;
    }
    use vir::ast::ResourceIntrinsic::*;
    match tcx.item_name(id).as_str() {
        "is_some" => Some(OptionIsSome),
        "is_none" => Some(OptionIsNone),
        "unwrap" => Some(OptionUnwrap),
        _ => None,
    }
}
