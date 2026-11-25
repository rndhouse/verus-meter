// This example shows how to bound a collection built by a Rust range loop.
//
// The count determines the number of box handles and heap arrays. The bound also
// includes the range and the values used to advance it.

use vstd::prelude::*;

verus! {

// A fixed heap allocation, carried by an owning handle.
type Buffer = Box<BufferStorage>;

// The payload allocated for each collected buffer.
type BufferStorage = [u8; 16];

/// `construction_budget` combines the storage retained per buffer with the loop's
/// temporary workspace.
spec fn construction_budget(count: u16) -> nat {
    // Each reserved slot in the outer vector holds one owning handle.
    let backing = (count as nat) * value_size(Buffer);
    // Each handle points to a separately allocated buffer.
    let allocations = (count as nat) * value_size(BufferStorage);
    // Allow for constructing and advancing the range, receiving its next index,
    // and holding a new box before it moves into a slot.
    let temporary = 2 * value_size(core::ops::Range<u16>)
        + value_size(Option<u16>) + value_size(u16)
        + ref_size(&core::ops::Range<u16>) + value_size(Buffer);
    value_size(count) + value_size(Vec<Buffer>) + backing + allocations + temporary
}

/// `build_buffers` returns one boxed array for each element of the range.
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

/// `main` requests two buffers within the builder's bound for that range.
fn main()
    resources peak(memory) <= peak(build_buffers(2)),
{
    let buffers = build_buffers(2);
}

} // verus!
