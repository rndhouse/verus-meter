// Shows how to sort data inside a struct with a proven memory bound.
//
// The proof checks that the result is sorted, no values are lost or added, and
// the operation stays within its memory budget. That budget includes both the
// stored data and the temporary workspace used to process it.

use vstd::prelude::*;

// The same verified sorter is used by the plain-array caller example.
#[path = "resource_insertion_sort.rs"]
mod sorting;

verus! {

// Keeps the data and its completion status together.
//
// Its model size follows the field types automatically, excluding ABI padding.
// Initializing nested fields uses their storage within the owning struct.
pub struct SortBuffer {
    pub values: [u32; 8],
    pub ready: bool,
}

// Makes an existing buffer sorted and ready to use within a fixed memory budget.
//
// The contract lets callers rely on the completed result without repeating the
// sorting proof. Borrowing the array field keeps ownership with the caller,
// which remains responsible for counting the buffer's storage.
//
// The budget follows the parameter type and the sorter's declared bound, so
// changes to either are picked up automatically. The parameter contributes
// only its reference; the owning caller accounts for the backing data.
pub fn sort_buffer(buffer: &mut SortBuffer)
    ensures
        final(buffer).ready,
        sorting::sorted_prefix(final(buffer).values@, 8),
        final(buffer).values@.to_multiset() == old(buffer).values@.to_multiset(),
    peakmem <= sizeof(buffer) + peakmem(sorting::insertion_sort),
{
    // Working through a field borrow avoids a second array-sized workspace.
    sorting::insertion_sort(&mut buffer.values);
    // Completion status is part of the helper's guarantee to its caller.
    buffer.ready = true;
}

// Demonstrates a complete memory bound for owned data and the helpers using it.
//
// The owned buffer remains live while the helper works, so the budget covers
// both together. The type-based query follows changes to the buffer's fields
// and can be used before its local variable is in scope.
// The checker also verifies that constructing the buffer fits this bound.
pub fn sort_local_struct()
    peakmem <= sizeof(SortBuffer) + peakmem(sort_buffer),
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

// Extends the buffer's guarantees to the complete example program.
//
// With no additional local data at this level, the same memory bound suffices.
fn main()
    peakmem <= peakmem(sort_local_struct),
{
    sort_local_struct();
}

}
