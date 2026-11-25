// This example shows how to bound a vector whose elements own buffers of their own.
//
// Each additional child contributes a header in the outer vector and a three-element
// reservation. Dropping the final owner releases them together.

use vstd::prelude::*;

verus! {

type FinalScratch = [u8; 512];

/// `build` constructs the requested number of child vectors with three reserved slots
/// each.
///
/// The fixed allowance covers the input, collection handle, loop index, and a
/// child being prepared. Each entry adds a child handle and its three-element
/// buffer; moved children remain charged through the collection.
fn build(n: usize) -> (buffers: Vec<Vec<u32>>)
    requires n <= 4,
    ensures buffers.len() == n,
    resources peak(memory) <= value_size(n) + value_size(Vec<Vec<u32>>) + value_size(usize)
        + value_size(Vec<u32>) + n * (value_size(Vec<u32>) + value_size([u32; 3])),
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

/// `main` moves the children into a boxed slice and releases it before allocating
/// scratch.
///
/// The later byte workspace sets the allowance for the complete operation.
fn main()
    resources peak(memory) <= value_size(FinalScratch),
{
    let buffers = build(3);
    // Making the collection fixed-length preserves the buffers it owns.
    let fixed = buffers.into_boxed_slice();
    drop(fixed);
    let scratch: FinalScratch = [0; 512];
}

} // verus!
