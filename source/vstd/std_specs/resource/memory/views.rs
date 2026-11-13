//! Demand-driven indexed-view requests and their propagation through forest operations.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::blocks::{generate_children, tile_children};
#[cfg(verus_keep_ghost)]
use super::forest::{Record, descendants, nonruntime, prefix, runtime, subtree, without};
#[cfg(verus_keep_ghost)]
use super::ranges::{reverse_children, shift_children, take_children};

verus! {

broadcast use crate::seq::group_seq_axioms;

/// A verified matching gate for precise indexed views. It is always true, but
/// remains opaque so constructor facts activate only for requested paths.
#[verifier::opaque]
pub open spec fn view_requested(memory: Seq<Record>, index: int) -> bool {
    true
}

/// Request the outer indexed view needed by a concrete projection.
pub proof fn request_path(memory: Seq<Record>, path: Seq<int>)
    ensures
        path.len() > 0 ==> view_requested(memory, path[0]),
{
    reveal(view_requested);
}

/// Requests follow the two operands of a composed forest.
pub broadcast proof fn request_add(left: Seq<Record>, right: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(left + right, index) ==> view_requested(left, index)
            && view_requested(right, index),
{
    reveal(view_requested);
}

/// A root descriptor does not hide its descendants' indexed views.
pub broadcast proof fn request_push(memory: Seq<Record>, value: Record, index: int)
    ensures
        #[trigger] view_requested(memory.push(value), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Runtime filtering preserves indexed requests.
pub broadcast proof fn request_runtime(memory: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(runtime(memory), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Fixed filtering preserves the source of a projected view.
pub broadcast proof fn request_nonruntime(memory: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(nonruntime(memory), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Descendant filtering preserves the source of a projected view.
pub broadcast proof fn request_descendants(memory: Seq<Record>, index: int)
    ensures
        #[trigger] view_requested(descendants(memory), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// Excluding a subtree retains the original forest's sibling views.
pub broadcast proof fn request_without(memory: Seq<Record>, path: Seq<int>, index: int)
    ensures
        #[trigger] view_requested(without(memory, path), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// A nested projection first needs the selected enclosing child.
pub broadcast proof fn request_subtree(memory: Seq<Record>, path: Seq<int>, index: int)
    ensures
        #[trigger] view_requested(subtree(memory, path), index) ==> if path.len() > 0 {
            view_requested(memory, path[0])
        } else {
            view_requested(memory, index)
        },
{
    reveal(view_requested);
}

/// Prefixing a forest retains requests for the underlying descriptors.
pub broadcast proof fn request_prefix(memory: Seq<Record>, path: Seq<int>, index: int)
    ensures
        #[trigger] view_requested(prefix(memory, path), index) ==> view_requested(memory, index),
{
    reveal(view_requested);
}

/// A shifted slot requests its original index.
pub broadcast proof fn request_shift(memory: Seq<Record>, base: int, index: int)
    ensures
        #[trigger] view_requested(shift_children(memory, base), index) ==> view_requested(
            memory,
            index - base,
        ),
{
    reveal(view_requested);
}

/// A tiled slot requests the corresponding position inside its block.
pub broadcast proof fn request_tile(
    block: Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    ensures
        #[trigger] view_requested(tile_children(block, width, count, start), index) ==> (width > 0
            ==> view_requested(block, (index - start) % width)),
{
    reveal(view_requested);
}

/// A generated slot requests the corresponding child in its iteration block.
pub broadcast proof fn request_generate(
    builder: spec_fn(int) -> Seq<Record>,
    width: int,
    count: int,
    start: int,
    index: int,
)
    ensures
        #[trigger] view_requested(generate_children(builder, width, count, start), index) ==> (width
            > 0 ==> view_requested(builder((index - start) / width), (index - start) % width)),
{
    reveal(view_requested);
}

/// Reversed slots request their source child through the inverse range map.
pub broadcast proof fn request_reverse(
    memory: Seq<Record>,
    start: int,
    end: int,
    base: int,
    index: int,
)
    ensures
        #[trigger] view_requested(reverse_children(memory, start, end, base), index)
            ==> view_requested(memory, base + end - 1 - index),
{
    reveal(view_requested);
}

/// Prefix retention keeps the original child views.
pub broadcast proof fn request_take(memory: Seq<Record>, length: int, index: int)
    ensures
        #[trigger] view_requested(take_children(memory, length), index) ==> view_requested(
            memory,
            index,
        ),
{
    reveal(view_requested);
}

} // verus!
