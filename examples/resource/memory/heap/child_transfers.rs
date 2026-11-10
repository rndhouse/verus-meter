use vstd::prelude::*;

verus! {

struct Buffers {
    active: Vec<u32>,
    spare: Box<[u8; 16]>,
}

// Replace a child buffer while preserving the rest of its owner.
//
// The caller retains the old allocation during the call; this allowance covers
// the reference and the four-element replacement buffer.
fn replace(buffers: &mut Buffers)
    ensures final(buffers).active.len() == 0,
    resources peak(memory) <= ref_size(buffers) + owned_size([u32; 4]),
{
    buffers.active = Vec::with_capacity(4);
}

// Move a child out, then release its storage before the next task.
//
// The later byte workspace sets the allowance for the complete operation.
fn main()
    resources peak(memory) <= owned_size([u8; 256]),
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
    let scratch = [0u8; 256];
}

} // verus!
