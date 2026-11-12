// Collect heap buffers while keeping every live allocation within one budget.
//
// This example shows how to prove an input-dependent memory bound for a loop
// that allocates and collects two buffers per batch. The bound includes every
// retained allocation as the collection grows.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// An owning buffer handle; its heap storage is counted separately.
type Buffer = Vec<u32>;

// Every buffer reserves space for eight integers.
type BufferStorage = [u32; 8];

// Cover two buffer slots and allocations per batch, plus the collection handle,
// input, reserved-capacity local, and loop counter. Add helper storage separately.
spec fn construction_budget(batch_count: u16) -> nat {
    let buffer_count = 2 * (batch_count as nat);
    let backing = buffer_count * value_size(Buffer);
    let allocations = buffer_count * value_size(BufferStorage);
    let scalars = value_size(batch_count) + value_size(usize) + value_size(u16);
    value_size(Vec<Buffer>) + backing + allocations + scalars
}

// Allocate one buffer within an allowance for its handle and heap storage.
fn allocate_buffer() -> Buffer
    resources peak(memory) <= value_size(Buffer) + value_size(BufferStorage),
{
    Vec::with_capacity(8)
}

// Return two buffers per requested batch. The narrower count type keeps the
// doubled capacity within usize. The checker derives the collection length
// from the two appends in each completed batch.
fn build_buffers(batch_count: u16) -> Vec<Buffer>
    resources peak(memory) <= construction_budget(batch_count) + peak(allocate_buffer),
{
    let capacity = 2 * (batch_count as usize);
    let mut buffers = Vec::<Buffer>::with_capacity(capacity);
    let mut batch = 0u16;
    while batch < batch_count {
        let first = allocate_buffer();
        buffers.push(first);
        let second = allocate_buffer();
        buffers.push(second);
        batch += 1;
    }
    buffers
}

// Receive a collection within the builder's allowance for this input.
fn main()
    resources peak(memory) <= peak(build_buffers(2)),
{
    let buffers = build_buffers(2);
}

} // verus!
