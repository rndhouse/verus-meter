// Sorts a list of numbers while proving correctness and a fixed memory bound.
//
// The proof connects small, local changes to a global guarantee: the final list
// is ordered and contains exactly the original values, including duplicates.
// It also shows that longer inputs do not require more temporary workspace.
// Budgets describe abstract storage costs, not physical stack layout. Companion
// examples show how callers can use both the correctness and memory guarantees.

use vstd::prelude::*;
use vstd::seq_lib::to_multiset_update;

verus! {

// Defines the progress that each sorting pass must preserve.
//
// Describing just the completed prefix lets the proof grow from no sorted
// elements to the whole list. Seq is a mathematical view, with no runtime copy.
pub open spec fn sorted_prefix(s: Seq<u32>, end: int) -> bool {
    forall|a: int, b: int| 0 <= a < b < end ==> #[trigger] s[a] <= #[trigger] s[b]
}

// Lets the proof describe a nearly sorted region during an insertion.
//
// One position is reserved for the saved value, so order need only hold elsewhere.
// This logical "hole" is bookkeeping; the actual array still has a value there.
pub open spec fn ordered_except(s: Seq<u32>, end: int, hole: int) -> bool {
    forall|a: int, b: int| 0 <= a < b < end && a != hole && b != hole
        ==> #[trigger] s[a] <= #[trigger] s[b]
}

// Proves that making room for an insertion preserves the original collection.
//
// A shift temporarily duplicates a neighbor in the actual array. To account for
// the saved value correctly, compare states with the logical hole filled in.
// Equal multisets then establish that every value keeps its original count.
proof fn shift_preserves_elements(s: Seq<u32>, j: int, key: u32)
    requires 0 < j < s.len(),
    ensures
        s.update(j, s[j - 1]).update(j - 1, key).to_multiset()
            == s.update(j, key).to_multiset(),
{
    // The solver needs library facts connecting sequence edits to element counts.
    broadcast use {
        to_multiset_update,
        vstd::seq_lib::to_multiset_contains,
        vstd::multiset::group_multiset_axioms,
    };
    assert(s.contains(s[j]));
    assert(s.to_multiset().count(s[j]) > 0);
    // These are mathematical states after and before the shift, with the key
    // restored in each. Equal multisets mean equal counts, including duplicates.
    let left = s.update(j, s[j - 1]).update(j - 1, key);
    let right = s.update(j, key);
    assert(left.to_multiset() =~= right.to_multiset());
}

// Establishes correct sorting without workspace that grows with the input.
//
// Each pass inserts one value into the already sorted prefix. The proof must
// preserve both order and element counts while that value is temporarily saved
// outside the array. Proof snapshots are erased and add no runtime storage.
//
// The budget covers the workspace that remains live during an insertion:
// - The slice parameter, which borrows the caller's data.
// - The length and two indices that track progress.
// - The saved element while its insertion position is found.
// These needs stay fixed regardless of how many elements the slice contains.
pub fn insertion_sort(values: &mut [u32])
    // old(values) is the input state; final(values) is the state after return.
    // The @ notation exposes the slice's mathematical sequence for the proof.
    ensures
        final(values)@.len() == old(values)@.len(),
        sorted_prefix(final(values)@, final(values)@.len() as int),
        final(values)@.to_multiset() == old(values)@.to_multiset(),
    resources peakmem <= sizeof(values) + 3 * sizeof(usize) + sizeof(u32),
{
    let n = values.len();
    let mut i: usize = 0;
    // The outer invariant is the induction step: preserve all elements while
    // extending the region known to be sorted. An initially empty prefix makes
    // the same argument cover empty input.
    while i < n
        invariant
            n == values@.len(),
            n == old(values)@.len(),
            i <= n,
            sorted_prefix(values@, i as int),
            values@.to_multiset() == old(values)@.to_multiset(),
        decreases n - i,
    {
        let key = values[i];
        let mut j = i;
        // Initially the key is still in its original slot, so filling the
        // logical hole changes nothing. This establishes the inner invariant.
        proof { assert(values@.update(j as int, key) =~= values@); }
        // While searching left, positions right of the hole contain values
        // larger than key. The multiset invariant fills the hole conceptually
        // because a shift temporarily duplicates a neighbor in the actual slice.
        while j > 0 && values[j - 1] > key
            invariant
                n == values@.len(),
                n == old(values)@.len(),
                j <= i < n,
                ordered_except(values@, i + 1, j as int),
                forall|k: int| j < k <= i ==> key < #[trigger] values@[k],
                values@.update(j as int, key).to_multiset() == old(values)@.to_multiset(),
            decreases j,
        {
            // The lemma needs the state before the write to justify preservation.
            let ghost before = values@;
            values[j] = values[j - 1];
            proof {
                shift_preserves_elements(before, j as int, key);
            }
            j -= 1;
        }
        proof {
            // The loop stopped at the front or just after a value no larger
            // than key. Show that filling this position sorts the whole prefix.
            let filled = values@.update(j as int, key);
            assert forall|a: int, b: int| 0 <= a < b < i + 1
                implies #[trigger] filled[a] <= #[trigger] filled[b] by {
                if b == j && a < j - 1 {
                    // For elements further left, order follows through the
                    // immediate predecessor of the insertion position.
                    assert(values@[a] <= values@[j - 1]);
                }
            }
            assert(sorted_prefix(filled, i + 1));
        }
        // The preceding proof bridges the temporary hole state back to the
        // complete sorted-prefix guarantee needed by the next pass.
        values[j] = key;
        i += 1;
    }
}

// Makes the sorting proof usable as a standalone verification example.
//
// No particular input is needed for verification; companion examples execute it.
fn main() {}

}
