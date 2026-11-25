// This example shows how to account for a buffer that outlives the struct that owned
// it.
//
// Replacing one field preserves the other. Moving the replacement out keeps its
// allocation live until its new owner drops it.

use vstd::prelude::*;

verus! {

type FinalScratch = [u8; 256];

struct Buffers {
    active: Vec<u32>,
    spare: Box<[u8; 16]>,
}

/// `replace` installs a new four-slot reservation in the active field.
///
/// The caller retains the old allocation during the call; this allowance covers
/// the reference and the four-element replacement buffer.
fn replace(buffers: &mut Buffers)
    ensures final(buffers).active.len() == 0,
    resources peak(memory) <= ref_size(buffers) + value_size([u32; 4]),
{
    buffers.active = Vec::with_capacity(4);
}

/// `main` moves the active buffer out, drops its former owner, and uses the surviving
/// reservation.
///
/// The later byte workspace sets the allowance for the complete operation.
fn main()
    resources peak(memory) <= value_size(FinalScratch),
{
    let mut buffers = Buffers {
        active: Vec::with_capacity(2),
        spare: Box::new([0u8; 16]),
    };
    replace(&mut buffers);
    // Transfer one child's allocations and refill its now-empty field.
    let mut active = buffers.active;
    buffers.active = Vec::new();
    drop(buffers);
    active.push(1);
    drop(active);
    let scratch: FinalScratch = [0; 256];
}

} // verus!
