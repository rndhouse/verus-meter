//! Evidence about a population of simultaneously owned synchronization witnesses.
use super::Loc;
use crate::prelude::*;

verus! {

/// An executable synchronization witness belongs to one protocol instance.
pub trait Holder {
    /// Identity stable throughout the witness's shared borrows.
    spec fn instance_id(&self) -> Loc;
}

/// Two roles that cannot be held simultaneously on one protocol instance.
/// For example, a writer excludes a reader while two readers can coexist.
pub trait Incompatible<Other: Holder>: Holder + Sized {
    /// The exclusive borrow supplies a distinct first witness even when both
    /// roles have the same Rust type.
    proof fn distinct_instances(tracked &mut self, tracked other: &Other)
        ensures
            *final(self) == *old(self),
            old(self).instance_id() != other.instance_id(),
    ;
}

/// A protocol proves its bound for any finite collection of owned witnesses
/// for the same instance. Borrowing a witness twice cannot supply two owned
/// elements of the tracked sequence. Capacity counts holders, independently
/// of the size or lifetime of any allocation.
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::resource::holder::BoundedHolder")]
pub trait BoundedHolder: Holder + Sized {
    /// Immutable holder limit for this instance.
    spec fn capacity(&self) -> nat;

    /// Establish the population inequality from linear ownership and the
    /// implementation's invariant. A single holder's postcondition alone
    /// cannot discharge this obligation.
    proof fn population_bound(tracked population: Seq<Self>, id: Loc, capacity: nat)
        requires
            forall|i: int|
                0 <= i < population.len() ==> #[trigger] population[i].instance_id() == id
                    && population[i].capacity() == capacity,
        ensures
            population.len() <= capacity,
    ;
}

} // verus!
