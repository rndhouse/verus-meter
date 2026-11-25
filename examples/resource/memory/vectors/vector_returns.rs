// This example shows how a vector reservation survives a return and covers later
// pushes.
//
// The caller receives an empty vector, fills two slots, then passes ownership to a
// helper that reads the length.

use vstd::prelude::*;

verus! {

/// `vector_storage` counts the vector header and its reserved integer slots.
///
/// Both functions use the same formula for the handle and reserved elements.
spec fn vector_storage(capacity: nat) -> nat {
    value_size(Vec<u32>) + capacity * value_size(u32)
}

/// `make_buffer` returns an empty vector with the requested reservation.
///
/// The memory budget scales with the capacity supplied by the caller.
fn make_buffer(capacity: usize) -> (buffer: Vec<u32>)
    requires capacity <= 16,
    ensures buffer.len() == 0,
    resources peak(memory) <= value_size(capacity) + vector_storage(capacity as nat),
{
    Vec::with_capacity(capacity)
}

/// `count` consumes the vector and returns its length.
///
/// The caller keeps its allocation charged while this helper runs. The
/// allocation is released when the call finishes; this helper needs only
/// its parameter and result slots.
fn count(buffer: Vec<u32>) -> (length: usize)
    ensures length == buffer.len(),
    resources peak(memory) <= value_size(buffer) + value_size(usize),
{
    buffer.len()
}

/// `use_buffer` fills two reserved slots before handing the vector to the counting
/// helper.
///
/// The shared formula keeps the producer and caller using the same allowance.
/// The allocation remains live through both calls and the intervening pushes.
fn use_buffer(capacity: usize)
    requires 2 <= capacity <= 16,
    resources peak(memory) <= value_size(capacity) + vector_storage(capacity as nat) + peak(count),
{
    let mut buffer = make_buffer(capacity);
    buffer.push(3);
    buffer.push(7);
    let length = count(buffer);
    assert(length == 2);
}

/// `main` uses the bound for a two-slot reservation.
fn main()
    resources peak(memory) <= peak(use_buffer(2)),
{
    use_buffer(2);
}

}
