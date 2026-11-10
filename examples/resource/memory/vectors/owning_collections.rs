// Bound a collection's memory use, including the buffers owned by its elements.

use vstd::prelude::*;

verus! {

// Build a collection of buffers within a budget that grows with their number.
//
// The fixed allowance covers the input, collection handle, loop index, and a
// child being prepared. Each entry adds a child handle and its three-element
// buffer; moved children remain charged through the collection.
fn build(n: usize) -> (buffers: Vec<Vec<u32>>)
    requires n <= 4,
    ensures buffers.len() == n,
    resources peak(memory) <= mem_size(n) + mem_size(Vec<Vec<u32>>) + mem_size(usize)
        + mem_size(Vec<u32>) + n * (mem_size(Vec<u32>) + mem_size([u32; 3])),
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
//
// The later byte workspace sets the allowance for the complete operation.
fn main()
    resources peak(memory) <= mem_size([u8; 512]),
{
    let buffers = build(3);
    // Making the collection fixed-length preserves the buffers it owns.
    let fixed = buffers.into_boxed_slice();
    drop(fixed);
    let scratch = [0u8;512];
}

} // verus!
