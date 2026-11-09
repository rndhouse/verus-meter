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
fn make(n: usize) -> (b: Box<Buffer>)
    requires n <= 4,
    ensures b.values.len() == 0, *b.marker == 42,
    mem_peak <= 52 + 4 * n,
{
    Box::new(Buffer { values: Vec::with_capacity(n), marker: Box::new(42) })
}

// Transfer ownership while preserving the data and its memory cost.
fn forward(b: Box<Buffer>) -> (r: Box<Buffer>)
    ensures r == b,
    mem_peak <= 8,
{
    b
}

// Use the data after a handoff, then free it before the next task.
fn main()
    mem_peak <= 96,
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
