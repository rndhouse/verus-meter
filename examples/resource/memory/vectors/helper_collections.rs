use vstd::prelude::*;

verus! {

// A counted helper returns each row's reservation, independently of row data.
// Its peak budget also covers the outer buffer, handles and loop temporaries.
fn rows(n: usize) -> (rows: Vec<Vec<u32>>)
    requires n <= 2,
    ensures rows.len() == n,
        forall|i: int| 0 <= i < n ==> rows[i].len() == 0,
    resources peak(memory) <= 200,
{
    let mut rows = Vec::<Vec<u32>>::with_capacity(n);
    let mut i = 0usize;
    while i < n
        invariant i <= n, n <= 2, rows.len() == i,
            forall|j: int| 0 <= j < rows.len() ==> rows[j].len() == 0,
        decreases n - i,
    {
        let row = Vec::<u32>::with_capacity(4);
        rows.push(row);
        i += 1;
    }
    rows
}

fn main()
    resources peak(memory) <= 288,
{
    let mut rows = rows(2);
    // The helper's summary preserves each row's allocation and reservation.
    // Discarding the popped row releases its buffer. The surviving row's
    // reservation lets the following push reuse its existing buffer.
    rows.pop();
    rows[0].push(7);
    // 24-byte handle + 48-byte outer buffer + 16-byte surviving row + scratch.
    let scratch = [0u8; 200];
}

}
