// This module proves the one-guard limit used by the custom mutex example.
// Each lock starts with one proof token. Acquiring the lock moves its token
// into the guard, and releasing the guard puts the token back.
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::frac::FracGhost;
use vstd::resource::holder::{BoundedHolder, BoundedInstance, Holder, ProtocolInstance, issued_on_success};

verus! {

struct_with_invariants! {
    pub(crate) struct Lock {
        flag: AtomicBool<_, Option<FracGhost<()>>, _>,
        domain: Ghost<Loc>,
    }

    /// `wf` relates the lock flag to its proof token. The unlocked lock holds
    /// the unique token that a successful acquisition transfers to a guard.
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        invariant on flag with (domain) is (held: bool, token: Option<FracGhost<()>>) {
            &&& !held == token.is_some()
            &&& token matches Some(lock_token) ==> lock_token.id() == domain@ && lock_token.frac() == 1real
        }
    }
}

pub(crate) struct Guard<'lock> {
    lock: &'lock Lock,
    token: Tracked<FracGhost<()>>,
}

impl ProtocolInstance for Lock {
    /// `protocol_id` identifies this lock so the verifier can match guards to their issuer.
    closed spec fn protocol_id(&self) -> Loc { self.domain@ }
}

impl BoundedInstance for Lock {
    /// `holder_limit` gives the maximum number of guards this lock can issue at once.
    open spec fn holder_limit(&self) -> nat { 1 }
}

/// `transition_workspace` bounds the space workers use to acquire or release
/// the lock. Releasing a guard is the larger of the two operations.
pub open spec fn transition_workspace(workers: nat) -> nat {
    // Release uses the guard, three reference slots along the atomic store
    // call, and the Boolean being stored. Allow that space for each worker.
    workers * value_size(Guard) + 3 * (workers * ref_size(&bool)) + workers * value_size(bool)
}

impl Lock {
    /// `new` creates an unlocked mutex with a fresh identity and its own proof token.
    pub(crate) fn new() -> Self
        resources peak(memory) <= 3 * value_size(bool),
    {
        // Tie the initial token to this lock so a guard for a different lock
        // cannot justify a bound on this one's holders.
        let tracked token = FracGhost::<()>::new(());
        let domain = Ghost(token.id());
        let flag = AtomicBool::new(Ghost(domain), false, Tracked(Some(token)));
        Lock { flag, domain }
    }

    /// `try_enter` tries once to acquire the lock. A successful attempt returns
    /// a guard carrying the lock's unique token.
    pub(crate) fn try_enter(&self) -> (acquisition: Option<Guard<'_>>)
        ensures
            issued_on_success(acquisition, self),
            acquisition matches Some(guard) ==> guard.instance_id() == self.protocol_id(),
        // The expected and replacement flags are live as locals and as call
        // arguments alongside the receiver references and tagged result.
        resources peak(memory) <= 3 * ref_size(&bool)
            + 4 * value_size(bool) + value_size(Result<bool, bool>),
    {
        proof {
            use_type_invariant(self);
        }
        // Move the token out in the same atomic step that changes the flag
        // from free to held. A failed attempt leaves it where it was.
        let tracked mut taken = None;
        let success =
            atomic_with_ghost!(
            &self.flag => compare_exchange(false, true);
            returning result;
            ghost state => {
                if result is Ok {
                    taken = state;
                    state = None;
                }
            }
        );
        if success.is_ok() {
            let tracked unit = taken.tracked_unwrap();
            Some(Guard { lock: self, token: Tracked(unit) })
        } else {
            None
        }
    }
}

impl<'lock> Guard<'lock> {
    /// `wf` requires the guard to own the full token belonging to its lock.
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.token@.id() == self.lock.domain@
        &&& self.token@.frac() == 1real
    }

    /// `leave` consumes the guard and returns its token to the lock as it unlocks.
    pub(crate) fn leave(self)
        resources peak(memory) <= value_size(Guard) + 3 * ref_size(&bool) + value_size(bool),
    {
        proof {
            use_type_invariant(&self);
            use_type_invariant(self.lock);
        }
        // Return the token in the same atomic step that makes the lock available.
        let Guard { lock, token: Tracked(unit) } = self;
        atomic_with_ghost!(&lock.flag => store(false); ghost state => { state = Some(unit); });
    }
}

impl<'lock> Holder for Guard<'lock> {
    /// `instance_id` identifies the lock that issued this guard.
    closed spec fn instance_id(&self) -> Loc {
        self.lock.domain@
    }
}

impl<'lock> BoundedHolder for Guard<'lock> {
    /// `capacity` reports that this guard's lock admits one holder at a time.
    open spec fn capacity(&self) -> nat {
        1
    }

    /// `population_bound` proves that two guards for the same lock cannot coexist.
    /// Each would have to own the same token in full.
    proof fn population_bound(tracked mut population: Seq<Self>, id: Loc, capacity: nat) {
        broadcast use vstd::seq::group_seq_axioms;

        // Remember the original sequence so the proof can identify both
        // guards after removing them from the end.
        let ghost before = population;
        if population.len() > 0 {
            assert(before[0].instance_id() == id && before[0].capacity() == capacity);
        }
        if population.len() > 1 {
            assert(before.last().instance_id() == id);
            let tracked last_guard = population.tracked_pop();
            assert(population.last() == before[before.len() - 2]);
            assert(population.last().instance_id() == id);
            let tracked preceding_guard = population.tracked_pop();
            use_type_invariant(&last_guard);
            use_type_invariant(&preceding_guard);
            // Both guards claim the full token for this lock. Combining them
            // would exceed the single whole that the token algebra permits.
            let tracked mut both = last_guard.token.get();
            both.combine(preceding_guard.token.get());
            both.bounded();
        }
    }
}

} // verus!
