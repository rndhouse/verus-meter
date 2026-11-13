//! Canonical VSTD identities for the ownership algebra.
//!
//! Generated calls and recognition share this registry. Modules expose their
//! actual definitions; no compatibility paths or facade aliases are synthesized.

use crate::ast::*;
use std::sync::Arc;

pub(super) fn record() -> Dt {
    Dt::Path(crate::path!(CrateId::Vstd => "std_specs", "resource", "memory", "forest", "Record"))
}

fn module(name: &str) -> Option<&'static str> {
    Some(match name {
        "block_bounds"
        | "block_bounds_add"
        | "block_bounds_empty_selection"
        | "block_bounds_generate"
        | "block_bounds_prefix"
        | "block_bounds_repeat"
        | "block_bounds_shift"
        | "block_bounds_tile"
        | "block_bounds_weaken"
        | "generate_children"
        | "generate_children_at"
        | "generate_children_facts"
        | "generate_children_outside"
        | "generate_children_views"
        | "generated_cost"
        | "generated_cost_affine"
        | "tile_children"
        | "tile_children_at"
        | "tile_children_facts"
        | "tile_children_outside"
        | "tile_children_views" => "blocks",
        "cost"
        | "cost_add"
        | "cost_empty"
        | "cost_partition"
        | "cost_prefix"
        | "cost_push"
        | "cost_repeat"
        | "cost_runtime_partition"
        | "reverse_children_cost" => "cost",
        "allocated"
        | "contains"
        | "descendants"
        | "descendants_facts"
        | "empty_record"
        | "lookup"
        | "nonruntime"
        | "prefix"
        | "replace"
        | "runtime"
        | "runtime_add"
        | "runtime_class"
        | "runtime_prefix"
        | "runtime_push"
        | "runtime_without_facts"
        | "subtree"
        | "well_formed"
        | "well_formed_add"
        | "well_formed_prefix"
        | "well_formed_push"
        | "well_formed_record"
        | "with_root"
        | "with_root_facts"
        | "without" => "forest",
        "group_metadata_algebra" | "group_metadata_loop_algebra" | "group_runtime_shape" => {
            "groups"
        }
        "iterate"
        | "iterate_closed"
        | "iterate_closed_facts"
        | "iterate_facts"
        | "product_bounds" => "iteration",
        "repeat"
        | "repeat_facts"
        | "reverse_children"
        | "reverse_children_add"
        | "reverse_children_facts"
        | "reverse_children_prefix"
        | "reverse_children_push"
        | "reverse_children_views"
        | "shift_children"
        | "shift_children_facts"
        | "shift_children_select"
        | "take_children"
        | "take_children_add"
        | "take_children_empty"
        | "take_children_facts"
        | "take_children_prefix"
        | "take_children_repeat"
        | "take_children_root"
        | "take_children_runtime" => "ranges",
        "partition_remove"
        | "remove_add"
        | "remove_index"
        | "remove_index_requested_views"
        | "remove_index_views"
        | "remove_partition"
        | "remove_prefix"
        | "remove_root" => "removal",
        "contains_add" | "contains_prefix" | "contains_runtime" | "contains_without"
        | "descendants_add" | "descendants_prefix" | "descendants_push" | "inspect"
        | "lookup_add" | "lookup_empty" | "lookup_prefix" | "lookup_push" | "lookup_runtime"
        | "lookup_subtree" | "lookup_without" | "partition_without" | "runtime_frame"
        | "runtime_presence" | "select_add" | "select_descendants" | "select_empty"
        | "select_prefix" | "select_push" | "select_remove" | "select_replacement"
        | "select_root" | "select_runtime" | "select_without" | "singleton_prefix"
        | "skip_prefix" | "slot_prefix" => "selection",
        "request_add"
        | "request_descendants"
        | "request_generate"
        | "request_nonruntime"
        | "request_path"
        | "request_prefix"
        | "request_push"
        | "request_reverse"
        | "request_runtime"
        | "request_shift"
        | "request_subtree"
        | "request_take"
        | "request_tile"
        | "request_without"
        | "view_requested" => "views",
        _ => return None,
    })
}

/// Resolve a compiler-generated algebra call to its defining module.
pub(super) fn function(name: &str) -> Fun {
    let module = module(name).unwrap_or_else(|| panic!("unknown memory algebra function: {name}"));
    let mut path =
        crate::path!(CrateId::Vstd => "std_specs", "resource", "memory").as_ref().clone();
    Arc::make_mut(&mut path.segments)
        .extend([Segment::T(Arc::new(module.into()), 0), Segment::V(Arc::new(name.into()), 0)]);
    Arc::new(FunX { path: Arc::new(path) })
}

/// Unrelated functions and unregistered names cannot supply algebra operations.
pub(super) fn is_function(value: &Fun, name: &str) -> bool {
    module(name).is_some() && *value == function(name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_calls_use_the_definitions_module_namespace() {
        let definition =
            crate::fun!(CrateId::Vstd => "std_specs", "resource", "memory", "forest"; "allocated");
        assert_eq!(function("allocated"), definition);
        assert!(is_function(&definition, "allocated"));
        let different =
            crate::fun!(CrateId::Vstd => "std_specs", "resource", "memory", "forest"; "lookup");
        assert!(!is_function(&different, "allocated"));
        assert!(!is_function(&definition, "unregistered"));
    }
}
