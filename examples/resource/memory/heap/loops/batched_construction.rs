// Collect heap buffers while keeping every live allocation within one budget.
//
// Each iteration calls the same helper twice. Moving its buffers into the
// collection keeps their heap storage charged until the collection is dropped.
// Termination checking is disabled to keep this example focused on memory.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// An owning buffer handle; its heap storage is counted separately.
type Buffer = Vec<u32>;

// Every buffer reserves space for eight integers.
type BufferStorage = [u32; 8];

// Count the collection handle, four buffer slots, four buffer allocations,
// and the loop counter. The helper's temporary storage is added at the call site.
spec fn construction_budget() -> nat {
    let backing = 4 * value_size(Buffer);
    let allocations = 4 * value_size(BufferStorage);
    value_size(Vec<Buffer>) + backing + allocations + value_size(usize)
}

// Allocate one buffer within an allowance for its handle and heap storage.
fn allocate_buffer() -> Buffer
    resources peak(memory) <= value_size(Buffer) + value_size(BufferStorage),
{
    Vec::with_capacity(8)
}

// Build four buffers in two batches, then release all their allocations.
// The length bound connects loop progress to the amount of live heap storage.
fn main()
    resources peak(memory) <= construction_budget() + peak(allocate_buffer),
{
    let mut buffers = Vec::<Buffer>::with_capacity(4);
    let mut batch = 0usize;
    while batch < 2
        invariant
            batch <= 2,
            buffers.len() == 2 * batch,
    {
        let first = allocate_buffer();
        buffers.push(first);
        let second = allocate_buffer();
        buffers.push(second);
        batch += 1;
    }
    drop(buffers);
}

} // verus!
