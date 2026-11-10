// Grow one buffer while keeping the memory reserved for another available.

use vstd::prelude::*;

verus! {

// Keep two buffers together while allowing them to grow independently.
struct Buffers {
    values: Vec<u32>,
    spare: Vec<u32>,
}

// Add a value while preserving the other buffer's contents and reservation.
//
// The caller accounts for the existing buffers; the helper allows for growth.
fn append(buffers: &mut Buffers)
    requires old(buffers).values.len() == 0,
    ensures
        final(buffers).values@ == seq![7u32],
        final(buffers).spare@ == old(buffers).spare@,
    resources mem_peak <= 24,
{
    buffers.values.push(7);
}

// Use both buffers, then release them to make room for another task.
fn main()
    resources mem_peak <= 160,
{
    let mut buffers = Box::new(Buffers {
        values: Vec::new(),
        spare: Vec::with_capacity(4),
    });
    append(&mut *buffers);
    // Growing one buffer leaves the other's reservation available.
    buffers.spare.push(9);
    assert(buffers.values[0] == 7);
    assert(buffers.spare[0] == 9);
    drop(buffers);
    let scratch = [0u8;160];
}

} // verus!
