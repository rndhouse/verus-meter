// Keep related heap data within one budget as ownership passes between helpers.
//
// Releasing the outer owner also releases the data it owns.

use vstd::prelude::*;

verus! {

// Group a collection and its marker under one owner.
struct Buffer {
    values: Vec<u32>,
    marker: Box<u32>,
}

// Create the related data within an allowance that follows the requested capacity.
//
// Count the capacity input, outer box handle, owned struct, marker value, and
// vector elements. The struct's size already includes its vector and marker handles.
fn make(n: usize) -> (b: Box<Buffer>)
    requires n <= 4,
    ensures b.values.len() == 0, *b.marker == 42,
    resources peak(memory) <= mem_size(n) + mem_size(Box<Buffer>) + mem_size(Buffer)
        + mem_size(u32) + n * mem_size(u32),
{
    Box::new(Buffer { values: Vec::with_capacity(n), marker: Box::new(42) })
}

// Transfer ownership while preserving the data and its memory cost.
fn forward(b: Box<Buffer>) -> (r: Box<Buffer>)
    ensures r == b,
    resources peak(memory) <= mem_size(b),
{
    b
}

// Use the data after a handoff, then free it before the next task.
//
// The allowance covers the saved length alongside the later byte workspace.
fn main()
    resources peak(memory) <= mem_size(usize) + mem_size([u8; 88]),
{
    let first = make(4);
    let second = forward(first);
    let length = second.values.len();
    assert(length == 0);
    assert(*second.marker == 42);
    drop(second);
    let scratch = [0u8; 88];
}

}
