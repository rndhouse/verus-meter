//! Scoped broadcast groups used by compiler-generated ownership proofs.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::cost::{cost_add, cost_empty, cost_prefix, cost_push, cost_repeat};
#[cfg(verus_keep_ghost)]
use super::forest::{runtime_add, runtime_class, runtime_prefix, runtime_push};
#[cfg(verus_keep_ghost)]
use super::removal::{partition_remove, remove_add, remove_prefix};
#[cfg(verus_keep_ghost)]
use super::selection::{
    contains_add, contains_prefix, contains_runtime, contains_without, lookup_add, lookup_empty,
    lookup_prefix, lookup_push, lookup_runtime, lookup_subtree, lookup_without, partition_without,
    select_add, select_empty, select_prefix, select_push, select_replacement, select_runtime,
    select_without, singleton_prefix, skip_prefix,
};
#[cfg(verus_keep_ghost)]
use super::views::{
    request_add, request_descendants, request_generate, request_nonruntime, request_prefix,
    request_push, request_reverse, request_runtime, request_shift, request_subtree, request_take,
    request_tile, request_without,
};

verus! {

broadcast use crate::seq::group_seq_axioms;
// Keep lookup_subtree explicit: flattening every composed ownership path can
// multiply matching terms across a sequence of operations.

pub broadcast group group_metadata_algebra {
    Seq::add_empty_left,
    Seq::add_empty_right,
    cost_empty,
    lookup_empty,
    select_empty,
    singleton_prefix,
    skip_prefix,
    select_add,
    select_prefix,
    cost_add,
    cost_push,
    cost_prefix,
    cost_repeat,
    request_add,
    request_push,
    request_runtime,
    request_nonruntime,
    request_descendants,
    request_without,
    request_subtree,
    request_prefix,
    request_shift,
    request_tile,
    request_generate,
    request_reverse,
    request_take,
    remove_add,
    remove_prefix,
    lookup_add,
    lookup_push,
    lookup_runtime,
    select_without,
    select_replacement,
}

/// Reusable ownership proofs also need views of arbitrary sibling indices.
/// Keep these rules separate from ordinary finite element transfers.
pub broadcast group group_metadata_loop_algebra {
    select_push,
    lookup_without,
    lookup_prefix,
    select_runtime,
    contains_add,
    contains_without,
    contains_prefix,
    contains_runtime,
}

/// Descriptor-class rewrites for local shape proofs. Keep these scoped to
/// shape assertions rather than activating them throughout budget queries.
pub broadcast group group_runtime_shape {
    runtime_add,
    runtime_push,
    runtime_prefix,
    runtime_class,
    partition_without,
    partition_remove,
}

} // verus!
