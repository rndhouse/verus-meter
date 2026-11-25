use vstd::prelude::*;

verus! {

type RowPayload = [u8; 32];
type Row = Box<RowPayload>;
type RowScratch = [u8; 64];
type FinalScratch = [u8; 176];

/// `work_budget` takes the larger of the two successive workspaces.
spec fn work_budget() -> nat {
    // On the first pop both payloads are still live. The vector keeps its
    // two reserved handle slots, and the extracted handle occupies a local.
    let collection = value_size(Vec<Row>) + 2 * value_size(Row);
    let payloads = 2 * value_size(RowPayload);
    let processing = collection + payloads + value_size(Row) + value_size(RowScratch);

    // The final scratch array is allocated after the collection is dropped.
    let final_task = value_size(FinalScratch);
    if processing >= final_task { processing } else { final_task }
}

/// `main` drops the collection before starting the final task. The two phases
/// can reuse the same bytes, so their larger requirement bounds the whole run.
fn main()
    resources peak(memory) <= work_budget(),
{
    let mut rows = Vec::<Row>::with_capacity(2);
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
        let scratch: RowScratch = [0; 64];
        drop(row);
    }

    drop(rows);
    // After all owners are dropped, the whole allowance is reusable.
    let scratch: FinalScratch = [0; 176];
}

}
