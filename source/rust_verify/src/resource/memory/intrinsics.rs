//! Identify supported operations using compiler identities, including through aliases.

use crate::verus_items::RustItem;
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use vir::ast::ResourceIntrinsic;

/// Connect a standard library call to the memory rule that describes its effects.
///
/// Recognized calls receive a tag for the later accounting pass, which handles
/// their effects without analyzing the library implementation. An unrecognized
/// call is left to normal call handling; it is not assumed to be free.
pub(crate) fn call(
    tcx: TyCtxt<'_>,
    id: DefId,
    rust_item: Option<RustItem>,
) -> Option<ResourceIntrinsic> {
    if let Some(intrinsic) = iterator_intrinsic(tcx, id, rust_item) {
        Some(intrinsic)
    } else if let Some(intrinsic) = option_intrinsic(tcx, id) {
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

/// Resolve iterator operations by their defining trait or concrete wrapper.
/// A method with the same source spelling on a different type is not intrinsic.
fn iterator_intrinsic(
    tcx: TyCtxt<'_>,
    id: DefId,
    rust_item: Option<RustItem>,
) -> Option<ResourceIntrinsic> {
    use ResourceIntrinsic::*;
    if rust_item == Some(RustItem::IntoIterFn) {
        return Some(IteratorInto);
    }
    if tcx.trait_of_assoc(id) == tcx.get_diagnostic_item(rustc_span::Symbol::intern("Iterator"))
        && tcx.trait_of_assoc(id).is_some()
    {
        return match tcx.item_name(id).as_str() {
            "rev" => Some(IteratorRev),
            "take" => Some(IteratorTake),
            "skip" => Some(IteratorSkip),
            _ => None,
        };
    }
    let imp = tcx.impl_of_assoc(id)?;
    if tcx.trait_impl_of_assoc(imp).is_some() {
        return None;
    }
    let TyKind::Adt(adt, _) = tcx.type_of(imp).skip_binder().kind() else {
        return None;
    };
    if crate::verus_items::def_id_to_stable_rust_path(tcx, adt.did()).as_deref()
        != Some("vstd::std_specs::iter::VerusForLoopWrapper")
    {
        return None;
    }
    match tcx.item_name(id).as_str() {
        "new" => Some(IteratorWrap),
        "next" => Some(IteratorNext),
        _ => None,
    }
}

/// Recognize vector operations that the memory checker knows how to account for.
///
/// Confirm that the method belongs to the standard vector type before selecting
/// its rule. Type aliases still work, while unrelated types and trait methods
/// with matching names cannot accidentally receive vector accounting rules.
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
        "remove" => Some(VecRemove),
        "len" => Some(VecLen),
        "as_slice" => Some(VecAsSlice),
        "as_mut_slice" => Some(VecAsMutSlice),
        "into_boxed_slice" => Some(VecIntoBoxedSlice),
        _ => None,
    }
}

/// Recognize operations that inspect or extract an optional value.
///
/// These tags let the memory checker account for the result without analyzing
/// the library method's body. Only methods on the standard `Option` type qualify;
/// an unrelated method with the same name does not inherit these rules.
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
