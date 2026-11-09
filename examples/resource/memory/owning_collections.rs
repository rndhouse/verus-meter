use vstd::prelude::*;

verus! {

// Each element owns a heap buffer. The outer buffer contains only 24-byte
// handles; the child-footprint sum accounts for each 12-byte inner allocation.
fn build(n: usize) -> (buffers: Vec<Vec<u32>>)
    requires n <= 4,
    ensures buffers.len() == n,
    mem_peak <= 64 + 36*n,
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

fn main()
    mem_peak <= 512,
{
    let buffers = build(3);
    // Conversion replaces the outer buffer and keeps its children's allocations.
    let fixed = buffers.into_boxed_slice();
    drop(fixed);
    let scratch = [0u8;512];
}

} // verus!
