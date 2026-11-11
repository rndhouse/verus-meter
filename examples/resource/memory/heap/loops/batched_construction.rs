// Collect heap buffers while keeping every live allocation within one budget.
//
// This example shows how to prove a memory bound for a loop that calls a helper
// to allocate buffers and collects them. The bound includes all of those
// allocations as the collection grows.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// An owning buffer handle; its heap storage is counted separately.
type Buffer = Vec<u32>;

// Every buffer reserves space for eight integers.
type BufferStorage = [u32; 8];

// Capacity determines the collection's backing storage; the maximum live
// buffer count determines its separate allocations. Also count the collection
// handle and loop counter. The helper's temporary storage is added by the caller.
spec fn construction_budget(capacity: usize, max_live_buffers: usize) -> nat {
    let backing = (capacity as nat) * value_size(Buffer);
    let allocations = (max_live_buffers as nat) * value_size(BufferStorage);
    value_size(Vec<Buffer>) + backing + allocations + value_size(usize)
}

// Allocate one buffer within an allowance for its handle and heap storage.
fn allocate_buffer() -> Buffer
    resources peak(memory) <= value_size(Buffer) + value_size(BufferStorage),
{
    Vec::with_capacity(8)
}

// Build four buffers in two batches within the construction budget.
// The length bound connects loop progress to the amount of live heap storage.
fn main()
    resources peak(memory) <= construction_budget(4, 4) + peak(allocate_buffer),
{
    let mut buffers = Vec::<Buffer>::with_capacity(4);
    let mut batch = 0usize;
    while batch < 2
        invariant
            buffers.len() == 2 * batch,
    {
        let first = allocate_buffer();
        buffers.push(first);
        let second = allocate_buffer();
        buffers.push(second);
        batch += 1;
    }
}

} // verus!
