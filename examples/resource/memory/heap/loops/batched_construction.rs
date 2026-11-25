// This example shows how to prove a symbolic peak for a loop that retains two buffers
// per batch.
//
// Each batch adds two vector headers and two eight-element reservations. The caller
// also allows for the helper that constructs the next buffer.

#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// An owning buffer handle; its heap storage is counted separately.
type Buffer = Vec<u32>;

// Every buffer reserves space for eight integers.
type BufferStorage = [u32; 8];

/// `construction_budget` counts both retained buffers per batch and the caller's
/// construction state.
spec fn construction_budget(batch_count: u16) -> nat {
    let buffer_count = 2 * (batch_count as nat);
    // Each reserved slot in the outer vector holds one owning handle.
    let backing = buffer_count * value_size(Buffer);
    // Each handle points to a separately allocated buffer.
    let allocations = buffer_count * value_size(BufferStorage);
    // The input, doubled capacity, and current batch index stay live during construction.
    let scalars = value_size(batch_count) + value_size(usize) + value_size(u16);
    value_size(Vec<Buffer>) + backing + allocations + scalars
}

/// `allocate_buffer` returns a vector with eight reserved integer slots.
fn allocate_buffer() -> Buffer
    resources peak(memory) <= value_size(Buffer) + value_size(BufferStorage),
{
    Vec::with_capacity(8)
}

/// `build_buffers` appends two independently allocated buffers per batch.
///
/// The u16 batch count leaves room to double it for the capacity. Each completed
/// iteration adds two buffers, so the verifier can track the length from the pushes.
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

/// `main` requests two batches using the builder's bound for that input.
fn main()
    resources peak(memory) <= peak(build_buffers(2)),
{
    let buffers = build_buffers(2);
}

} // verus!
