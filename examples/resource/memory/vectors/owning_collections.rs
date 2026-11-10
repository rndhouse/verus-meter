// Bound a collection's memory use, including the buffers owned by its elements.

use vstd::prelude::*;

verus! {

// Build a collection of buffers within a budget that grows with their number.
//
// The allowance covers both the collection and the storage each buffer owns.
fn build(n: usize) -> (buffers: Vec<Vec<u32>>)
    requires n <= 4,
    ensures buffers.len() == n,
    resources peak(memory) <= 64 + 36*n,
{
    let mut buffers = Vec::<Vec<u32>>::with_capacity(n);
    let mut i = 0usize;
    while i < n
        invariant i <= n, buffers.len() == i,
        decreases n - i,
    {
        let child = Vec::<u32>::with_capacity(3);
        buffers.push(child);
        i += 1;
    }
    buffers
}

// Release the whole collection before reusing its memory allowance.
fn main()
    resources peak(memory) <= 512,
{
    let buffers = build(3);
    // Making the collection fixed-length preserves the buffers it owns.
    let fixed = buffers.into_boxed_slice();
    drop(fixed);
    let scratch = [0u8;512];
}

} // verus!
