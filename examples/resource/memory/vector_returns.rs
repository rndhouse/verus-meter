// Let a helper create a vector while keeping its memory allowance visible to the caller.
//
// The reservation follows the returned vector, so the caller can prove that
// its pushes fit and account for the allocation during later helper calls.

use vstd::prelude::*;

verus! {

// Describe the storage that follows a vector from its producer to its caller.
//
// Both functions use the same formula for the handle and reserved elements.
spec fn vector_storage(capacity: nat) -> nat {
    mem_size(Vec<u32>) + capacity * mem_size(u32)
}

// Supply an empty buffer with room for the requested number of values.
//
// The memory budget scales with the capacity supplied by the caller.
fn make_buffer(capacity: usize) -> (buffer: Vec<u32>)
    requires capacity <= 16,
    ensures buffer.len() == 0,
    resources mem_peak <= mem_size(capacity) + vector_storage(capacity as nat),
{
    Vec::with_capacity(capacity)
}

// Finish with a buffer and report how many values it held.
//
// The caller keeps its allocation charged while this helper runs. The
// allocation is released when the call finishes; this helper needs only
// its parameter and result slots.
fn count(buffer: Vec<u32>) -> (length: usize)
    ensures length == buffer.len(),
    resources mem_peak <= mem_size(buffer) + mem_size(usize),
{
    buffer.len()
}

// Use a returned reservation and then hand it over for final processing.
//
// The shared formula keeps the producer and caller using the same allowance.
// The allocation remains live through both calls and the intervening pushes.
fn use_buffer(capacity: usize)
    requires 2 <= capacity <= 16,
    resources mem_peak <= mem_size(capacity) + vector_storage(capacity as nat) + mem_peak(count),
{
    let mut buffer = make_buffer(capacity);
    buffer.push(3);
    buffer.push(7);
    let length = count(buffer);
    assert(length == 2);
}

// Run the whole operation within the allowance for two values.
fn main()
    resources mem_peak <= mem_peak(use_buffer(2)),
{
    use_buffer(2);
}

}
