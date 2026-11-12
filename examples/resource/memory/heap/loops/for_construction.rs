// Collect heap buffers with a finite iterator instead of an explicit counter.
//
// This example shows how a `for` loop uses the same ownership and peak-memory
// model as a counted while loop. Its range and yielded values have their own
// inline storage; the collection retains each buffer's separate heap storage.

use vstd::prelude::*;

verus! {

// A fixed heap allocation, carried by an owning handle.
type Buffer = Box<BufferStorage>;

// The payload allocated for each collected buffer.
type BufferStorage = [u8; 16];

// Cover the collection and retained buffers, plus range setup, advancement,
// and the pending buffer handle before it moves into the collection.
spec fn construction_budget(count: u16) -> nat {
    let backing = (count as nat) * value_size(Buffer);
    let allocations = (count as nat) * value_size(BufferStorage);
    let temporary = 2 * value_size(core::ops::Range<u16>)
        + value_size(Option<u16>) + value_size(u16)
        + ref_size(&core::ops::Range<u16>) + value_size(Buffer);
    value_size(count) + value_size(Vec<Buffer>) + backing + allocations + temporary
}

// Return one buffer per range element, keeping every retained allocation within
// the input-dependent allowance. No explicit counter or length invariant is needed.
fn build_buffers(count: u16) -> Vec<Buffer>
    resources peak(memory) <= construction_budget(count),
{
    let mut buffers = Vec::with_capacity(count as usize);
    for _ in 0u16..count {
        let buffer = Box::new([0u8; 16]);
        buffers.push(buffer);
    }
    buffers
}

// Receive the collection within the builder's allowance for this input.
fn main()
    resources peak(memory) <= peak(build_buffers(2)),
{
    let buffers = build_buffers(2);
}

} // verus!
