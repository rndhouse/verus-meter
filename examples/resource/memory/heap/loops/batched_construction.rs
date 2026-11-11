// Construct batches of owning buffers through helpers and nested loops.
//
// Named storage types and memory formulas describe the allowance. The length
// bounds limit live collection storage; no buffer contents are specified.
// Termination checking is disabled to keep this example focused on memory.
#![verifier::exec_allows_no_decreases_clause]

use vstd::prelude::*;

verus! {

// One owning row handle; its buffer allocation is counted separately.
type Row = Vec<u32>;

// Buffer reservation returned by the small-row constructor.
type SmallBuffer = [u32; 4];

// Buffer reservation returned by the large-row constructor.
type LargeBuffer = [u32; 8];

// Workspace used after the returned collection has been released.
type Workspace = [u8; 4096];

// Keep the collection's backing, up to eight large row buffers, both loop
// counters, and the row being prepared live at the same time.
spec fn construction_workspace() -> nat {
    let backing = 8 * value_size(Row);
    let children = 8 * value_size(LargeBuffer);
    let locals = 2 * value_size(usize) + value_size(Row);
    value_size(Vec<Row>) + backing + children + locals
}

// Return a small buffer with its owning handle and allocation both budgeted.
fn small_row() -> Row
    resources peak(memory) <= value_size(Row) + value_size(SmallBuffer),
{
    Vec::with_capacity(4)
}

// Return a larger buffer using the same ownership rules.
fn large_row() -> Row
    resources peak(memory) <= value_size(Row) + value_size(LargeBuffer),
{
    Vec::with_capacity(8)
}

// Build two batches, each containing two pairs of buffers.
// The length bounds connect progress to the amount of allocated row storage.
fn batches() -> Vec<Row>
    resources peak(memory) <= construction_workspace() + peak(large_row),
{
    let mut rows = Vec::<Row>::with_capacity(8);
    let mut i = 0usize;
    while i < 2
        invariant
            i <= 2,
            rows.len() == 4 * i,
    {
        let mut j = 0usize;
        while j < 2
            invariant
                j <= 2,
                i < 2,
                rows.len() == 4 * i + 2 * j,
        {
            let small = small_row();
            rows.push(small);
            let large = large_row();
            rows.push(large);
            j += 1;
        }
        i += 1;
    }
    rows
}

// Release all returned child allocations before using the workspace allowance.
fn main()
    resources peak(memory) <= value_size(Workspace),
{
    let rows = batches();
    drop(rows);
    let scratch: Workspace = [0u8;4096];
}

} // verus!
