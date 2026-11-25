// This example shows how to bound the cost of sorting an array held inside a struct.
//
// The caller counts the whole struct once. The sorting helper borrows its array field
// and supplies a separate bound for its workspace.

use vstd::prelude::*;

// The same verified sorter is used by the plain-array caller example.
#[path = "insertion_sort.rs"]
mod sorting;

verus! {

// Keeps the data and its completion status together.
//
// The memory budget follows the fields, so it keeps up with changes to the buffer.
pub struct SortBuffer {
    pub values: [u32; 8],
    pub ready: bool,
}

/// `sort_buffer` sorts the array field and marks the buffer ready.
///
/// The contract lets callers rely on the completed result without repeating the
/// sorting proof. Borrowing the array field keeps ownership with the caller,
/// which remains responsible for counting the buffer's storage.
///
/// The budget follows the parameter type and the sorter's declared bound, so
/// changes to either are picked up automatically. The parameter contributes
/// only its reference; the owning caller accounts for the backing data.
pub fn sort_buffer(buffer: &mut SortBuffer)
    ensures
        final(buffer).ready,
        sorting::sorted_prefix(final(buffer).values@, 8),
        final(buffer).values@.to_multiset() == old(buffer).values@.to_multiset(),
    resources peak(memory) <= ref_size(buffer) + peak(sorting::insertion_sort),
{
    // Working through a field borrow avoids a second array-sized workspace.
    sorting::insertion_sort(&mut buffer.values);
    // Completion status is part of the helper's guarantee to its caller.
    buffer.ready = true;
}

/// `sort_local_struct` counts the owned struct alongside the workspace needed to sort
/// it.
///
/// The owned buffer remains live while the helper works, so the budget covers
/// both together. The type-based query follows changes to the buffer's fields
/// and can be used before its local variable is in scope.
pub fn sort_local_struct()
    resources peak(memory) <= value_size(SortBuffer) + peak(sort_buffer),
{
    let mut buffer = SortBuffer {
        values: [9u32, 3, 7, 3, 0, 8, 1, 5],
        ready: false,
    };
    // Keep the original contents available to the proof without a runtime copy.
    let ghost original = buffer.values@;
    sort_buffer(&mut buffer);
    // These are the guarantees a caller obtains from the helper's contract.
    assert(buffer.ready);
    assert(sorting::sorted_prefix(buffer.values@, 8));
    assert(buffer.values@.to_multiset() == original.to_multiset());
}

/// `main` runs the struct example within the caller's declared bound.
///
/// With no additional local data at this level, the same memory bound suffices.
fn main()
    resources peak(memory) <= peak(sort_local_struct),
{
    sort_local_struct();
}

}
