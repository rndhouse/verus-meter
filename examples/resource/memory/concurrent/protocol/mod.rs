// A successful CAS transfers the unique tracked token into the returned guard.
// Releasing the guard puts that token back. Two live guards for this instance
// would own two full fractions, contradicting the resource algebra.
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
            &&& token matches Some(t) ==> t.id() == domain@ && t.frac() == 1real
        }
    }
}

pub(crate) struct Guard<'a> {
    lock: &'a Lock,
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
    workers * value_size(Guard) + 3 * (workers * ref_size(&bool)) + workers * value_size(bool)
}

impl Lock {
    /// `new` creates an unlocked mutex with a fresh identity and its own proof token.
    pub(crate) fn new() -> (s: Self)
        resources peak(memory) <= 3 * value_size(bool),
    {
        let tracked token = FracGhost::<()>::new(());
        let domain = Ghost(token.id());
        let flag = AtomicBool::new(Ghost(domain), false, Tracked(Some(token)));
        Lock { flag, domain }
    }

    /// `try_enter` tries once to acquire the lock. A successful attempt returns
    /// a guard carrying the lock's unique token.
    pub(crate) fn try_enter(&self) -> (g: Option<Guard<'_>>)
        ensures
            issued_on_success(g, self),
            g matches Some(g) ==> g.instance_id() == self.protocol_id(),
        // The expected and replacement flags are live as locals and as call
        // arguments alongside the receiver references and tagged result.
        resources peak(memory) <= 3 * ref_size(&bool)
            + 4 * value_size(bool) + value_size(Result<bool, bool>),
    {
        proof {
            use_type_invariant(self);
        }
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

impl<'a> Guard<'a> {
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
        let Guard { lock, token: Tracked(unit) } = self;
        atomic_with_ghost!(&lock.flag => store(false); ghost state => { state = Some(unit); });
    }
}

impl<'a> Holder for Guard<'a> {
    /// `instance_id` identifies the lock that issued this guard.
    closed spec fn instance_id(&self) -> Loc {
        self.lock.domain@
    }
}

impl<'a> BoundedHolder for Guard<'a> {
    /// `capacity` reports that this guard's lock admits one holder at a time.
    open spec fn capacity(&self) -> nat {
        1
    }

    /// `population_bound` proves that two guards for the same lock cannot coexist.
    /// Each would have to own the same token in full.
    proof fn population_bound(tracked mut population: Seq<Self>, id: Loc, capacity: nat) {
        broadcast use vstd::seq::group_seq_axioms;

        let ghost before = population;
        if population.len() > 0 {
            assert(before[0].instance_id() == id && before[0].capacity() == capacity);
        }
        if population.len() > 1 {
            assert(before.last().instance_id() == id);
            let tracked a = population.tracked_pop();
            assert(population.last() == before[before.len() - 2]);
            assert(population.last().instance_id() == id);
            let tracked b = population.tracked_pop();
            use_type_invariant(&a);
            use_type_invariant(&b);
            let tracked mut both = a.token.get();
            both.combine(b.token.get());
            both.bounded();
        }
    }
}

} // verus!
