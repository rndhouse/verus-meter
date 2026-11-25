// This example shows how to track the storage of individual rows in a vector.
//
// Replacing a row releases the displaced buffer. Removing a row transfers its buffer to
// the caller, while the other rows keep theirs.

use vstd::prelude::*;

verus! {

type FinalScratch = [u8; 248];

struct Row {
    cells: Vec<u32>,
}

/// `add` adds one value to a borrowed row.
///
/// The caller keeps paying for the row's original allocation. This helper's
/// allowance covers its reference and one additional slot.
fn add(row: &mut Row)
    requires old(row).cells.len() <= 1,
    ensures final(row).cells.len() == old(row).cells.len() + 1,
    resources peak(memory) <= ref_size(row) + value_size(u32),
{
    row.cells.push(7);
}

/// `add_at` grows the selected row and preserves the other rows.
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

/// `remove_at` removes one row and returns ownership of its buffer.
fn remove_at(rows: &mut Vec<Row>, index: usize) -> (row: Row)
    requires index < old(rows).len(),
    ensures row == old(rows)[index as int], final(rows)@ == old(rows)@.remove(index as int),
    resources peak(memory) <= ref_size(rows) + value_size(index) + value_size(Row),
{
    rows.remove(index)
}

/// `main` updates, replaces, and removes rows before reusing the released storage for
/// scratch.
///
/// Only the saved length remains live alongside the later byte workspace.
fn main()
    resources peak(memory) <= value_size(usize) + value_size(FinalScratch),
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
    let removed = remove_at(&mut rows, 1);
    drop(removed);

    // Boxed slices use the same indexed child metadata and allocation sums.
    let frozen = rows.into_boxed_slice();
    let count = frozen[0].cells.len();
    assert(count == 0);
    drop(frozen);

    // Dropping the whole collection releases all retained child charges.
    // Only the saved count remains alongside this scratch space.
    let scratch: FinalScratch = [0; 248];
}

}
