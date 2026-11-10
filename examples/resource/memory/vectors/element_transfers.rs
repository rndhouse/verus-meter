use vstd::prelude::*;

verus! {

// The helper exports the selected allocation's metadata. Its caller retains
// the original storage charge during the call, then owns the result separately.
fn take(rows: &mut Vec<Box<[u8; 32]>>) -> (row: Option<Box<[u8; 32]>>)
    requires old(rows).len() > 0,
    ensures row.is_some(), final(rows).len() == old(rows).len() - 1,
    resources peak(memory) <= 17,
{
    rows.pop()
}

// The vector buffer holds handles. Each handle separately owns 32 heap bytes.
// A popped child keeps those bytes charged until that child is dropped.
fn main()
    resources peak(memory) <= 176,
{
    let mut rows = Vec::<Box<[u8; 32]>>::with_capacity(2);
    let first = Box::new([0u8; 32]);
    rows.push(first);
    let second = Box::new([0u8; 32]);
    rows.push(second);

    while rows.len() > 0
        invariant rows.len() <= 2,
        decreases rows.len(),
    {
        let row = take(&mut rows).unwrap();
        // The buffer, remaining rows, extracted row and scratch overlap here.
        let scratch = [0u8; 64];
        drop(row);
    }

    drop(rows);
    // After all owners are dropped, the whole allowance is reusable.
    let scratch = [0u8; 176];
}

}
