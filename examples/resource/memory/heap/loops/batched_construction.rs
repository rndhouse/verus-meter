// Construct batches of owning buffers through helpers and nested loops.
//
// Each batch contains two pairs of empty buffers with different reservations.
// The returned collection preserves those reservations and allocation sizes,
// so its caller can keep one buffer and release the rest independently.
use vstd::prelude::*;

verus! {

// Append a pair while preserving the earlier rows and their allocations.
// The allowance covers new row buffers, handles, and possible collection growth.
fn append_pair(rows: &mut Vec<Vec<u32>>)
    requires
        old(rows).len() <= 6,
        forall|i: int| 0 <= i < old(rows).len() ==> old(rows)[i].len() == 0,
    ensures
        final(rows).len() == old(rows).len() + 2,
        forall|i: int| 0 <= i < final(rows).len() ==> final(rows)[i].len() == 0,
    resources peak(memory) <= 1024,
{
    let small = Vec::<u32>::with_capacity(4);
    rows.push(small);
    let large = Vec::<u32>::with_capacity(8);
    rows.push(large);
}

// Build up to two batches, each containing two pairs.
// The outer reservation holds all eight possible rows. The budget also covers
// the helper's workspace while previously constructed rows remain allocated.
fn batches(n: usize) -> (rows: Vec<Vec<u32>>)
    requires
        n <= 2,
    ensures
        rows.len() == 4 * n,
        forall|i: int| 0 <= i < rows.len() ==> rows[i].len() == 0,
    resources peak(memory) <= 2048,
{
    let mut rows = Vec::<Vec<u32>>::with_capacity(8);
    let mut i = 0usize;
    while i < n
        invariant
            i <= n,
            n <= 2,
            rows.len() == 4 * i,
            forall|k: int| 0 <= k < rows.len() ==> rows[k].len() == 0,
        decreases n - i,
    {
        let mut j = 0usize;
        while j < 2
            invariant
                j <= 2,
                i < n,
                n <= 2,
                rows.len() == 4 * i + 2 * j,
                forall|k: int| 0 <= k < rows.len() ==> rows[k].len() == 0,
            decreases 2 - j,
        {
            append_pair(&mut rows);
            j += 1;
        }
        i += 1;
    }
    rows
}

// Reuse the last row's reservation after releasing the collection and siblings.
// The final peak is its 24-byte handle, 32-byte buffer, and 4096-byte workspace.
fn main()
    resources peak(memory) <= 4152,
{
    let mut rows = batches(2);
    let mut last = rows.pop().unwrap();
    drop(rows);
    last.push(7);
    let scratch = [0u8;4096];
}

} // verus!
