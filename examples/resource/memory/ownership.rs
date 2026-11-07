// Pass a heap buffer between helpers without losing track of its memory cost.
//
// The factory creates the allocation, a helper hands it back, and the caller
// keeps responsibility for its storage until the buffer is dropped.

use vstd::prelude::*;

verus! {

type Buffer = Box<[u32; 4]>;

// Provide a fresh buffer whose storage becomes the caller's responsibility.
//
// The budget includes both the owning handle and its heap allocation.
fn make_buffer() -> Buffer
    mem_peak <= mem_size(Buffer) + mem_size([u32; 4]),
{
    Box::new([0u32; 4])
}

// Hand a buffer back without allocating a second copy.
//
// The caller keeps the incoming allocation charged throughout this call.
// This helper budgets its input and result handles.
fn hand_back(buffer: Buffer) -> Buffer
    mem_peak <= 2 * mem_size(Buffer),
{
    buffer
}

// Keep a single allocation alive through a change of owner.
//
// Both local handle slots remain charged until scope exit. The helper needs
// another handle while it runs, but the heap buffer is counted only once.
fn main()
    mem_peak <= 3 * mem_size(Buffer) + mem_size([u32; 4]),
{
    let original = make_buffer();
    let received = hand_back(original);
    drop(received);
}

}
