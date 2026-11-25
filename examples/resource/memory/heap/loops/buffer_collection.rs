// This example shows how to bound one heap copy per loop iteration while the source
// array stays live.
//
// The requested count determines both the vector's reserved handle slots and the number
// of separate boxed payloads.

use vstd::prelude::*;

verus! {

// The payload used by both the local array and each heap allocation.
type Buffer = [u8; 16];

/// `collection_budget` counts the retained boxes and the workspace needed to build
/// them.
spec fn collection_budget(count: u16) -> nat {
    // Each reserved slot in the outer vector holds one owning handle.
    let backing = (count as nat) * value_size(Box<Buffer>);
    // Each handle points to a separately allocated buffer.
    let allocations = (count as nat) * value_size(Buffer);
    // The local source array, count input, loop counter, and pending box handle
    // before it moves into the collection. Heap payloads are counted above.
    let temporary = value_size(Buffer) + value_size(count) + value_size(u16)
        + value_size(Box<Buffer>);
    value_size(Vec<Box<Buffer>>) + backing + allocations + temporary
}

/// `collect_buffers` returns one independently allocated copy of the source array per
/// iteration.
#[verifier::exec_allows_no_decreases_clause]
fn collect_buffers(count: u16) -> Vec<Box<Buffer>>
    resources peak(memory) <= collection_budget(count),
{
    let local = [7u8; 16];
    let mut buffers = Vec::with_capacity(count as usize);
    let mut iteration = 0u16;
    while iteration < count {
        let buffer = Box::new(local);
        buffers.push(buffer);
        iteration += 1;
    }
    buffers
}

/// `main` uses the collector's bound for three buffers.
fn main()
    resources peak(memory) <= peak(collect_buffers(3)),
{
    let buffers = collect_buffers(3);
}

} // verus!
