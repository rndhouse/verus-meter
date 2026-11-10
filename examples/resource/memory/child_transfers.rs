use vstd::prelude::*;

verus! {

struct Buffers {
    active: Vec<u32>,
    spare: Box<[u8; 16]>,
}

// The old backing allocation remains live while the new buffer is allocated.
fn replace(buffers: &mut Buffers)
    ensures final(buffers).active.len() == 0,
    resources memory <= 24,
{
    buffers.active = Vec::with_capacity(4);
}

fn main()
    resources memory <= 256,
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
