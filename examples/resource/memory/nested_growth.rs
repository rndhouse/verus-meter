use vstd::prelude::*;

verus! {

struct Buffers {
    values: Vec<u32>,
    spare: Vec<u32>,
}

// The caller retains the incoming allocations. This helper's 8-byte reference
// and a possible 16-byte replacement for values fit within 24 model bytes.
fn append(buffers: &mut Buffers)
    requires old(buffers).values.len() == 0,
    ensures
        final(buffers).values@ == seq![7u32],
        final(buffers).spare@ == old(buffers).spare@,
    mem_peak <= 24,
{
    buffers.values.push(7);
}

fn main()
    mem_peak <= 160,
{
    let mut buffers = Box::new(Buffers {
        values: Vec::new(),
        spare: Vec::with_capacity(4),
    });
    append(&mut *buffers);
    // The sibling retains its own capacity; growing values cannot consume it.
    buffers.spare.push(9);
    assert(buffers.values[0] == 7);
    assert(buffers.spare[0] == 9);
    drop(buffers);
    let scratch = [0u8;160];
}

} // verus!
