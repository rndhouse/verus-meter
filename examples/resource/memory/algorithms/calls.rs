// This example shows how to bound a sort while the caller's array stays live.
//
// The caller counts the array once and adds the sorter's declared workspace. The same
// call proves that the result is sorted and preserves every input element.

use vstd::prelude::*;

// Reuse the sorter's implementation, functional specification, and budget.
#[path = "insertion_sort.rs"]
mod sorting;

verus! {

/// `sort_local_array` sorts a local array within the combined allowance for the array
/// and the sorter.
///
/// The array remains owned here while sorting borrows it, so its storage
/// overlaps the helper's workspace. Referencing the helper's declared budget
/// lets this caller follow changes to that contract automatically.
pub fn sort_local_array()
    resources peak(memory) <= value_size([u32; 8]) + peak(sorting::insertion_sort),
{
    let mut values = [9u32, 3, 7, 3, 0, 8, 1, 5];
    // Remember the input for the preservation proof without retaining a runtime
    // copy. The @ notation exposes its mathematical sequence.
    let ghost original = values@;
    // The sorter counts its slice reference. This caller still owns the array.
    sorting::insertion_sort(&mut values);
    // These proof assertions follow from the callee's postconditions. A multiset
    // comparison checks element counts, so losing or inventing duplicates fails.
    assert(sorting::sorted_prefix(values@, values@.len() as int));
    assert(values@.to_multiset() == original.to_multiset());
}

/// `main` uses the same bound to run the complete sort.
///
/// There is no additional local data here, so the caller's bound is sufficient.
fn main()
    resources peak(memory) <= peak(sort_local_array),
{
    sort_local_array();
}

}
