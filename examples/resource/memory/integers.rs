// A counter can track both increases and corrections within a fixed memory allowance.
//
// Different integer widths can share a struct and pass through helpers. The
// memory queries follow those types, while Verus also checks arithmetic safety.

use vstd::prelude::*;

verus! {

struct Counter {
    value: i64,
    changes: u8,
}

// Apply a bounded adjustment and record that the counter changed.
//
// Preconditions leave room for both arithmetic operations. The caller retains
// the counter's storage; this helper needs only its reference and adjustment.
fn adjust(counter: &mut Counter, change: i64)
    requires
        -1000 <= old(counter).value <= 1000,
        -1000 <= change <= 1000,
        old(counter).changes < 255,
    ensures
        final(counter).value == old(counter).value + change,
        final(counter).changes == old(counter).changes + 1,
    mem_peak <= mem_size(counter) + mem_size(change),
{
    counter.value += change;
    counter.changes += 1;
}

// Keep the counter live while successive adjustments reuse the helper's workspace.
//
// The budget follows the struct's field types and the helper's declared bound.
// A negative argument is a signed value, with the same storage cost as a positive one.
fn main()
    mem_peak <= mem_size(Counter) + mem_peak(adjust),
{
    let mut counter = Counter { value: 10i64, changes: 0u8 };
    adjust(&mut counter, -3i64);
    adjust(&mut counter, 5i64);
    assert(counter.value == 12 && counter.changes == 2);
    assert(current(mem_peak) <= mem_size(Counter) + mem_peak(adjust));
}

}
