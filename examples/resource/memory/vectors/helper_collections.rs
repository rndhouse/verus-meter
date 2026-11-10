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

// Removing rows releases their child buffers and retains the surviving row's
// reservation. The outer vector keeps its own backing allocation.
fn keep_first(rows: &mut Vec<Vec<u32>>)
    requires old(rows).len() == 2, old(rows)[0].len() == 0,
    ensures final(rows).len() == 1, final(rows)[0].len() == 0,
    resources peak(memory) <= 40,
{
    while rows.len() > 1
        invariant 1 <= rows.len() <= 2, rows[0].len() == 0,
        decreases rows.len(),
    {
        rows.pop();
    }
}

fn main()
    resources peak(memory) <= 288,
{
    let mut rows = rows(2);
    keep_first(&mut rows);
    rows[0].push(7);
    // 24-byte handle + 48-byte outer buffer + 16-byte surviving row + scratch.
    let scratch = [0u8; 200];
}

}
