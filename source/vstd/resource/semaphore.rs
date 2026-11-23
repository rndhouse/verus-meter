//! A counting semaphore with immutable capacity and explicit release.
//! The atomic counter stores the number of available slots. Its ghost state
//! connects every successful decrement to one outstanding, linear witness.
use super::Loc;
use super::holder::{BoundedHolder, Holder};
use crate::atomic_ghost::*;
use crate::prelude::*;
use verus_state_machines_macros::tokenized_state_machine_vstd;

tokenized_state_machine_vstd! {
    slots {
        fields {
            #[sharding(constant)]
            pub capacity: nat,
            #[sharding(variable)]
            pub available: nat,
            #[sharding(count)]
            pub occupied: nat,
        }

        #[invariant]
        pub fn conserved(&self) -> bool {
            self.available + self.occupied == self.capacity
        }

        init! {
            initialize(capacity: nat) {
                init capacity = capacity;
                init available = capacity;
                init occupied = 0;
            }
        }

        transition! {
            acquire() {
                require pre.available > 0;
                update available = (pre.available - 1) as nat;
                add occupied += (1);
            }
        }

        transition! {
            release() {
                remove occupied -= (1);
                assert pre.available < pre.capacity;
                update available = pre.available + 1;
            }
        }

        property! {
            holder_bound(count: nat) {
                have occupied >= (count);
                assert count <= pre.capacity;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, capacity: nat) { }
        #[inductive(acquire)]
        fn acquire_inductive(pre: Self, post: Self) { }
        #[inductive(release)]
        fn release_inductive(pre: Self, post: Self) { }
    }
}

verus! {

struct_with_invariants! {
    /// A fixed-capacity semaphore. Its only runtime field is a sequentially
    /// consistent atomic counter. Capacity zero is valid.
    pub struct Semaphore {
        available: AtomicUsize<_, slots::available, _>,
        instance: Tracked<slots::Instance>,
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        invariant on available with (instance) is (value: usize, token: slots::available) {
            token.instance_id() == instance@.id() && token.value() == value
        }

        predicate { self.instance@.capacity() <= usize::MAX }
    }
}

/// One occupied slot. Moving this value transfers the slot. Dropping it
/// leaves the slot occupied. Only an explicit release returns it.
pub struct Permit<'a> {
    semaphore: &'a Semaphore,
    witness: Tracked<slots::occupied>,
}

impl Semaphore {
    /// Identity of the tokenized protocol created with this semaphore.
    pub closed spec fn id(&self) -> Loc {
        self.instance@.id()
    }

    /// Immutable upper bound on this instance's occupied slots.
    pub closed spec fn capacity(&self) -> nat {
        self.instance@.capacity()
    }

    /// Creates a fresh instance with all slots available.
    pub fn new(capacity: usize) -> (s: Self)
        ensures
            s.capacity() == capacity,
    {
        let tracked (Tracked(instance), Tracked(available), _) = slots::Instance::initialize(
            capacity as nat,
        );
        let instance = Tracked(instance);
        let available = AtomicUsize::new(Ghost(instance), capacity, Tracked(available));
        Semaphore { available, instance }
    }

    /// Attempts to occupy one slot. An empty semaphore or interference with
    /// the compare-exchange can make this attempt return `None`.
    pub fn try_acquire(&self) -> (result: Option<Permit<'_>>)
        ensures
            result matches Some(p) ==> p.semaphore() == *self && self.capacity() > 0,
    {
        proof {
            use_type_invariant(self);
        }
        let available = atomic_with_ghost!(&self.available => load(); ghost g => {});
        if available == 0 {
            return None;
        }
        let tracked mut witness = None;
        let result =
            atomic_with_ghost!(
            &self.available => compare_exchange(available, available - 1);
            returning res;
            ghost g => {
                if res is Ok {
                    witness = Some(self.instance.borrow().acquire(&mut g));
                }
            }
        );
        match result {
            Ok(_) => {
                let tracked unit = witness.tracked_unwrap();
                proof {
                    self.instance.borrow().holder_bound(1, &unit);
                }
                Some(Permit { semaphore: self, witness: Tracked(unit) })
            },
            Err(_) => None,
        }
    }

    /// Tries until it obtains a slot. No progress or fairness is assumed.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn acquire(&self) -> (p: Permit<'_>)
        ensures
            p.semaphore() == *self && self.capacity() > 0,
    {
        loop {
            if let Some(permit) = self.try_acquire() {
                return permit;
            }
        }
    }
}

impl<'a> Permit<'a> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.witness@.instance_id() == self.semaphore.instance@.id()
        &&& self.witness@.count() == 1
    }

    /// Instance whose capacity is occupied by this permit.
    pub closed spec fn semaphore(&self) -> Semaphore {
        *self.semaphore
    }

    /// Returns this slot to its issuing semaphore.
    pub fn release(self) {
        proof {
            use_type_invariant(&self);
        }
        let Permit { semaphore: issuer, witness: Tracked(unit) } = self;
        proof {
            use_type_invariant(issuer);
        }
        let _ =
            atomic_with_ghost!(
            &issuer.available => fetch_add(1);
            ghost g => { issuer.instance.borrow().release(&mut g, unit); }
        );
    }
}

impl<'a> Permit<'a> {
    /// Combine the distinct occupied tokens without executing a release or
    /// modifying the available counter.
    proof fn collect(tracked mut permits: Seq<Self>, id: Loc) -> (tracked total: slots::occupied)
        requires
            permits.len() > 0,
            forall|i: int| 0 <= i < permits.len() ==> #[trigger] permits[i].instance_id() == id,
        ensures
            total.instance_id() == id,
            total.count() == permits.len(),
        decreases permits.len(),
    {
        broadcast use crate::seq::group_seq_axioms;

        let ghost before = permits;
        assert(before.last().instance_id() == id);
        let tracked permit = permits.tracked_pop();
        assert forall|i: int| 0 <= i < permits.len() implies #[trigger] permits[i].instance_id()
            == id by {
            assert(permits[i] == before[i]);
            assert(before[i].instance_id() == id);
        }
        use_type_invariant(&permit);
        let tracked unit = permit.witness.get();
        if permits.len() == 0 {
            unit
        } else {
            let tracked mut rest = Self::collect(permits, id);
            rest.join(unit);
            rest
        }
    }
}

impl<'a> Holder for Permit<'a> {
    open spec fn instance_id(&self) -> Loc {
        self.semaphore().id()
    }
}

impl<'a> BoundedHolder for Permit<'a> {
    open spec fn capacity(&self) -> nat {
        self.semaphore().capacity()
    }

    proof fn population_bound(tracked population: Seq<Self>, id: Loc, capacity: nat) {
        if population.len() > 0 {
            let ghost count = population.len();
            assert(population[0].instance_id() == id && population[0].capacity() == capacity);
            let tracked instance = population.tracked_borrow(0).semaphore.instance.borrow().clone();
            let tracked total = Self::collect(population, id);
            instance.holder_bound(count, &total);
        }
    }
}

} // verus!
