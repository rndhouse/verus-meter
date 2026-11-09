use vstd::prelude::*;

verus! {

struct Row {
    cells: Vec<u32>,
}

// The caller keeps paying for the row's original allocation. This helper's
// allowance covers its reference and a possible replacement buffer.
fn add(row: &mut Row)
    requires old(row).cells.len() <= 1,
    ensures final(row).cells.len() == old(row).cells.len() + 1,
    mem_peak <= 24,
{
    row.cells.push(7);
}

fn main()
    mem_peak <= 256,
{
    let mut rows = Vec::<Row>::with_capacity(2);
    let first = Row { cells: Vec::new() };
    rows.push(first);
    let second = Row { cells: Vec::new() };
    rows.push(second);

    add(&mut rows[0]);
    rows[1].cells.push(9);

    // Bind the replacement before assigning it. The old child's allocation
    // stays in the conservative sum, even though Rust drops it here.
    let replacement = Row { cells: Vec::with_capacity(2) };
    rows[0] = replacement;
    rows.pop();

    // Boxed slices use the same indexed child rules and retain the same sum.
    let frozen = rows.into_boxed_slice();
    let count = frozen[0].cells.len();
    assert(count == 0);
    drop(frozen);

    // Dropping the whole collection releases all retained child charges.
    // Only the eight-byte count remains alongside this scratch space.
    let scratch = [0u8; 248];
}

}
