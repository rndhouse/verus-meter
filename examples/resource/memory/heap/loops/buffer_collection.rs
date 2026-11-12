// Collect one heap buffer per iteration while retaining a local source array.
// The memory budget grows with the requested number of buffers.

use vstd::prelude::*;

verus! {

// The payload used by both the local array and each heap allocation.
type Buffer = [u8; 16];

// Cover the local array, collection, input and counter, all retained buffers,
// and the pending box handle before it moves into the collection.
spec fn collection_budget(count: u16) -> nat {
    let backing = (count as nat) * value_size(Box<Buffer>);
    let allocations = (count as nat) * value_size(Buffer);
    // The local source array, count input, loop counter, and pending box handle
    // before it moves into the collection. Heap payloads are counted above.
    let temporary = value_size(Buffer) + value_size(count) + value_size(u16)
        + value_size(Box<Buffer>);
    value_size(Vec<Box<Buffer>>) + backing + allocations + temporary
}

// Return one independently allocated copy of the local array per iteration.
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

// Use the collector's declared allowance for this particular input.
fn main()
    resources peak(memory) <= peak(collect_buffers(3)),
{
    let buffers = collect_buffers(3);
}

} // verus!
