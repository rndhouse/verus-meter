use vstd::prelude::*;

verus! {

type Row = Vec<u32>;
type Rows = Vec<Row>;
type Scratch = [u8; 200];

/// `construction_budget` counts the outer vector, its reserved row headers,
/// and four reserved elements per row. The row count parameter, loop index, and the
/// row header being moved into a slot also occupy storage.
spec fn construction_budget(row_count: usize) -> nat {
    let collection = value_size(Rows) + (row_count as nat) * value_size(Row);
    let row_buffers = (row_count as nat) * 4 * value_size(u32);
    let locals = value_size(row_count) + value_size(usize) + value_size(Row);
    collection + row_buffers + locals
}

/// `rows` returns empty rows whose four-element reservations survive the call.
fn rows(row_count: usize) -> (rows: Rows)
    requires row_count <= 2,
    ensures rows.len() == row_count,
        forall|row_index: int| 0 <= row_index < row_count ==> rows[row_index].len() == 0,
    resources peak(memory) <= construction_budget(row_count),
{
    let mut rows = Rows::with_capacity(row_count);
    let mut rows_created = 0usize;
    while rows_created < row_count
        invariant rows_created <= row_count, row_count <= 2, rows.len() == rows_created,
            forall|entry_index: int| 0 <= entry_index < rows.len() ==> rows[entry_index].len() == 0,
        decreases row_count - rows_created,
    {
        let row = Row::with_capacity(4);
        rows.push(row);
        rows_created += 1;
    }
    rows
}

/// `main` keeps the outer vector and both row slots after the pop. Only the
/// surviving row's four elements remain reserved alongside the scratch array.
fn main()
    resources peak(memory) <= value_size(Rows) + 2 * value_size(Row)
        + 4 * value_size(u32) + value_size(Scratch),
{
    let mut rows = rows(2);
    // The helper's summary preserves each row's allocation and reservation.
    // Discarding the popped row releases its buffer. The surviving row's
    // reservation lets the following push reuse its existing buffer.
    rows.pop();
    rows[0].push(7);
    let scratch: Scratch = [0; 200];
}

}
