// Update individual buffers while keeping the whole collection within budget.
//
// Each buffer's memory use contributes to the collection's bound. Individual
// child metadata lets removal and replacement release the displaced allocations;
// dropping the collection releases every remaining child.

use vstd::prelude::*;

verus! {

struct Row {
    cells: Vec<u32>,
}

// Grow one row while preserving the other rows' memory allowances.
//
// The caller keeps paying for the row's original allocation. This helper's
// allowance covers its reference and a possible replacement buffer. The
// model's minimum u32 buffer holds four elements.
fn add(row: &mut Row)
    requires old(row).cells.len() <= 1,
    ensures final(row).cells.len() == old(row).cells.len() + 1,
    resources peak(memory) <= ref_size(row) + value_size([u32; 4]),
{
    row.cells.push(7);
}

// Borrow a child of a collection supplied by the caller. The same ownership
// rules apply inside this helper as at a direct indexing operation in main.
fn add_at(rows: &mut Vec<Row>, index: usize)
    requires index < old(rows).len(), old(rows)[index as int].cells.len() <= 1,
    ensures
        final(rows).len() == old(rows).len(),
        final(rows)[index as int].cells.len() == old(rows)[index as int].cells.len() + 1,
        forall|j: int| 0 <= j < old(rows).len() && j != index ==> final(rows)[j] == old(rows)[j],
    resources peak(memory) <= ref_size(rows) + value_size(index) + peak(add),
{
    add(&mut rows[index]);
}

// Update individual buffers, then reuse their storage for another task.
//
// Only the saved length remains live alongside the later byte workspace.
fn main()
    resources peak(memory) <= value_size(usize) + value_size([u8; 248]),
{
    let mut rows = Vec::<Row>::with_capacity(2);
    let first = Row { cells: Vec::new() };
    rows.push(first);
    let second = Row { cells: Vec::new() };
    rows.push(second);

    add_at(&mut rows, 0);
    rows[1].cells.push(9);

    // Bind the replacement before assigning it. Its footprint replaces the
    // old child's footprint when Rust drops that child.
    let replacement = Row { cells: Vec::with_capacity(2) };
    rows[0] = replacement;
    rows.pop();

    // Boxed slices use the same indexed child metadata and allocation sums.
    let frozen = rows.into_boxed_slice();
    let count = frozen[0].cells.len();
    assert(count == 0);
    drop(frozen);

    // Dropping the whole collection releases all retained child charges.
    // Only the saved count remains alongside this scratch space.
    let scratch = [0u8; 248];
}

}
