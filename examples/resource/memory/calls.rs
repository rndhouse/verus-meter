// Shows how to bound memory use across several function calls.
//
// A helper's verified guarantees let its caller reason about the complete
// operation without repeating the helper's proof. The memory bound includes
// data kept by the caller while the helper works, as well as the helper's needs.
// Correctness and abstract storage costs are checked together.

use vstd::prelude::*;

// Reuse the sorter's implementation, functional specification, and budget.
#[path = "insertion_sort.rs"]
mod sorting;

verus! {

// Shows how a caller can rely on a helper for both correctness and memory bounds.
//
// The array remains owned here while sorting borrows it, so its storage
// overlaps the helper's workspace. Referencing the helper's declared budget
// lets this caller follow changes to that contract automatically.
// The checker also verifies that construction and argument handoff fit.
pub fn sort_local_array()
    peakmem <= sizeof([u32; 8]) + peakmem(sorting::insertion_sort),
{
    let mut values = [9u32, 3, 7, 3, 0, 8, 1, 5];
    // Remember the input for the preservation proof without retaining a runtime
    // copy. The @ notation exposes its mathematical sequence.
    let ghost original = values@;
    // The slice parameter borrows the existing array. Its storage is already
    // included in the helper's budget; the array remains charged to this caller.
    sorting::insertion_sort(&mut values);
    // These proof assertions follow from the callee's postconditions. A multiset
    // comparison checks element counts, so losing or inventing duplicates fails.
    assert(sorting::sorted_prefix(values@, values@.len() as int));
    assert(values@.to_multiset() == original.to_multiset());
}

// Carries the memory guarantee through to the program's entry point.
//
// There is no additional local data here, so the caller's bound is sufficient.
fn main()
    peakmem <= peakmem(sort_local_array),
{
    sort_local_array();
}

}
