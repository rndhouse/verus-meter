//! Exact ownership recurrences and checked closed-form induction.
use crate::prelude::*;

#[cfg(verus_keep_ghost)]
use super::forest::{Record, well_formed};

verus! {

broadcast use crate::seq::group_seq_axioms;

/// Apply an ordered ownership transition to the evolving forest. Each step
/// sees all earlier updates, including repeated visits and shifted indices.
#[verifier::opaque]
pub open spec fn iterate(
    step: spec_fn(int, Seq<Record>) -> Seq<Record>,
    initial: Seq<Record>,
    count: int,
) -> Seq<Record>
    decreases count,
{
    if count <= 0 {
        initial
    } else {
        step(count - 1, iterate(step, initial, count - 1))
    }
}

/// Iteration preserves validity when its checked transition preserves validity
/// for every reachable ordinal and every valid input forest.
pub proof fn iterate_facts(
    step: spec_fn(int, Seq<Record>) -> Seq<Record>,
    initial: Seq<Record>,
    count: int,
)
    requires
        count >= 0,
        well_formed(initial),
        forall|i: int, state: Seq<Record>|
            0 <= i < count && well_formed(state) ==> well_formed(#[trigger] step(i, state)),
    ensures
        well_formed(iterate(step, initial, count)),
    decreases count,
{
    reveal_with_fuel(iterate, 2);
    if count > 0 {
        iterate_facts(step, initial, count - 1);
    }
}

/// Pointwise multiplication facts for symbolic per-visit allocation envelopes.
/// These keep ordinary loop queries independent of global nonlinear rewriting.
pub proof fn product_bounds(amount: int, completed: int, total: int)
    requires
        amount >= 0,
        0 <= completed <= total,
    ensures
        amount * completed <= amount * total,
        amount * (completed + 1) == amount * completed + amount,
        completed < total ==> amount * completed + amount <= amount * total,
        amount * total == total * amount,
{
    assert(amount * completed <= amount * total) by (nonlinear_arith)
        requires
            amount >= 0,
            0 <= completed <= total,
    ;
    assert(amount * (completed + 1) == amount * completed + amount) by (nonlinear_arith);
    assert(completed < total ==> amount * completed + amount <= amount * total) by (nonlinear_arith)
        requires
            amount >= 0,
            0 <= completed <= total,
    ;
    assert(amount * total == total * amount) by (nonlinear_arith);
}

/// The exact recurrence with an additional proposed closed form as proof input.
/// The candidate never defines the returned forest.
#[verifier::opaque]
pub open spec fn iterate_closed(
    step: spec_fn(int, Seq<Record>) -> Seq<Record>,
    initial: Seq<Record>,
    count: int,
    closed: spec_fn(int) -> Seq<Record>,
) -> Seq<Record> {
    iterate(step, initial, count)
}

/// Prove a complete closed forest by its base and successor equations. The
/// induction does not depend on a finite unfolding window or a byte substitute.
pub proof fn iterate_closed_facts(
    step: spec_fn(int, Seq<Record>) -> Seq<Record>,
    initial: Seq<Record>,
    count: int,
    closed: spec_fn(int) -> Seq<Record>,
)
    requires
        count >= 0,
        closed(0) == initial,
        forall|i: int| 0 <= i < count ==> closed(i + 1) == #[trigger] step(i, closed(i)),
    ensures
        iterate_closed(step, initial, count, closed) == closed(count),
        iterate_closed(step, initial, count, closed) == iterate(step, initial, count),
    decreases count,
{
    reveal(iterate_closed);
    reveal_with_fuel(iterate, 2);
    if count > 0 {
        iterate_closed_facts(step, initial, count - 1, closed);
        assert(closed(count) == step(count - 1, closed(count - 1)));
    }
}

} // verus!
