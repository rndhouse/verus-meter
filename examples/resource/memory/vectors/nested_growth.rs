// This example shows how to grow one vector field while preserving another field's
// reservation.
//
// A helper pushes into the empty first vector. The caller can still use the spare
// vector's four slots and release both buffers before allocating scratch.

use vstd::prelude::*;

verus! {

type FinalScratch = [u8; 160];

// Keep two buffers together while allowing them to grow independently.
struct Buffers {
    values: Vec<u32>,
    spare: Vec<u32>,
}

/// `append` pushes into the first field while preserving the spare vector.
///
/// The caller accounts for the existing buffers. The helper allows for its
/// reference and one additional u32 slot.
fn append(buffers: &mut Buffers)
    requires old(buffers).values.len() == 0,
    ensures
        final(buffers).values@ == seq![7u32],
        final(buffers).spare@ == old(buffers).spare@,
    resources peak(memory) <= ref_size(buffers) + value_size(u32),
{
    buffers.values.push(7);
}

/// `main` uses both fields, then drops their owner before allocating scratch.
///
/// The later byte workspace sets the allowance for the complete operation.
fn main()
    resources peak(memory) <= value_size(FinalScratch),
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
    let scratch: FinalScratch = [0; 160];
}

} // verus!
