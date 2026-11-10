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
    resources peak(memory) <= owned_size(Buffer) + owned_size([u32; 4]),
{
    Box::new([0u32; 4])
}

// Hand a buffer back without allocating a second copy.
//
// The caller keeps the incoming allocation charged throughout this call.
// Moving the handle into the result transfers its charge too.
fn hand_back(buffer: Buffer) -> Buffer
    resources peak(memory) <= owned_size(Buffer),
{
    buffer
}

// Keep a single allocation alive through a change of owner.
//
// Each handoff transfers the existing handle and allocation. Renaming the owner
// does not create another buffer or require another handle allowance.
fn main()
    resources peak(memory) <= mem_peak(make_buffer),
{
    let original = make_buffer();
    let received = hand_back(original);
    drop(received);
}

}
