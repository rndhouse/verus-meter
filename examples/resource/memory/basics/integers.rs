// This example shows how to check a counter's arithmetic and memory bound together.
//
// The caller owns the counter across two adjustments. Each call uses the same allowance
// for a borrowed reference and a signed adjustment.

use vstd::prelude::*;

verus! {

struct Counter {
    value: i64,
    changes: u8,
}

/// `adjust` updates the value and change count within the allowance for its two
/// parameters.
///
/// Preconditions leave room for both arithmetic operations. The caller retains
/// the counter's storage; this helper needs only its reference and adjustment.
fn adjust(counter: &mut Counter, change: i64)
    requires
        -1000 <= old(counter).value <= 1000,
        -1000 <= change <= 1000,
        old(counter).changes < 255,
    ensures
        final(counter).value == old(counter).value + change,
        final(counter).changes == old(counter).changes + 1,
    resources peak(memory) <= ref_size(counter) + value_size(change),
{
    counter.value += change;
    counter.changes += 1;
}

/// `main` keeps one counter live across two successive adjustments.
///
/// The budget follows the struct's field types and the helper's declared bound.
fn main()
    resources peak(memory) <= value_size(Counter) + peak(adjust),
{
    let mut counter = Counter { value: 10i64, changes: 0u8 };
    adjust(&mut counter, -3i64);
    adjust(&mut counter, 5i64);
    assert(counter.value == 12 && counter.changes == 2);
    assert(peak(memory) <= value_size(Counter) + peak(adjust));
}

}
