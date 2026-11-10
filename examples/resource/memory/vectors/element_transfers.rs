use vstd::prelude::*;

verus! {

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
        let row = rows.pop().unwrap();
        // The buffer, remaining rows, extracted row and scratch overlap here.
        let scratch = [0u8; 64];
        drop(row);
    }

    drop(rows);
    // After all owners are dropped, the whole allowance is reusable.
    let scratch = [0u8; 176];
}

}
