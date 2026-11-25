// This example shows how a bound follows the allocations owned by a boxed struct.
//
// The struct owns a vector reservation and a boxed marker. Moving the outer box
// preserves both allocations, and dropping it releases them together.

use vstd::prelude::*;

verus! {

type FinalScratch = [u8; 88];

// Group a collection and its marker under one owner.
struct Buffer {
    values: Vec<u32>,
    marker: Box<u32>,
}

/// `make` constructs the boxed struct, marker, and requested vector reservation.
///
/// Count the capacity input, outer box handle, owned struct, marker value, and
/// vector elements. The struct's size already includes its vector and marker handles.
fn make(n: usize) -> (b: Box<Buffer>)
    requires n <= 4,
    ensures b.values.len() == 0, *b.marker == 42,
    resources peak(memory) <= value_size(n) + value_size(Box<Buffer>) + value_size(Buffer)
        + value_size(u32) + n * value_size(u32),
{
    Box::new(Buffer { values: Vec::with_capacity(n), marker: Box::new(42) })
}

/// `forward` passes on the outer box and everything it owns.
fn forward(b: Box<Buffer>) -> (r: Box<Buffer>)
    ensures r == b,
    resources peak(memory) <= value_size(b),
{
    b
}

/// `main` uses both fields after the handoff and drops the box before allocating
/// scratch.
///
/// The allowance covers the saved length alongside the later byte workspace.
fn main()
    resources peak(memory) <= value_size(usize) + value_size(FinalScratch),
{
    let first = make(4);
    let second = forward(first);
    let length = second.values.len();
    assert(length == 0);
    assert(*second.marker == 42);
    drop(second);
    let scratch: FinalScratch = [0; 88];
}

}
