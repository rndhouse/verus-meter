// This example shows how one heap allocation remains accounted for across an ownership
// transfer.
//
// The factory creates the box, a second helper returns it, and the caller drops it. The
// peak covers one handle and one array.

use vstd::prelude::*;

verus! {

type Buffer = Box<[u32; 4]>;

/// `make_buffer` returns a new box and counts both its handle and its payload.
fn make_buffer() -> Buffer
    resources peak(memory) <= value_size(Buffer) + value_size([u32; 4]),
{
    Box::new([0u32; 4])
}

/// `hand_back` returns the original box with its allocation intact.
///
/// The caller keeps the incoming allocation charged throughout this call.
/// Moving the handle into the result transfers its charge too.
fn hand_back(buffer: Buffer) -> Buffer
    resources peak(memory) <= value_size(Buffer),
{
    buffer
}

/// `main` receives the same allocation through two calls within the factory's bound.
///
/// Each handoff transfers the existing handle and allocation. Renaming the owner
/// does not create another buffer or require another handle allowance.
fn main()
    resources peak(memory) <= peak(make_buffer),
{
    let original = make_buffer();
    let received = hand_back(original);
    drop(received);
}

}
