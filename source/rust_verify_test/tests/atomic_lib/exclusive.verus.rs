use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::resource::frac::FracGhost;
use vstd::resource::holder::{BoundedHolder, Holder};

verus! {

struct_with_invariants! {
    struct Lock {
        flag: AtomicBool<_, Option<FracGhost<()>>, _>,
        domain: Ghost<Loc>,
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        invariant on flag with (domain) is (held: bool, token: Option<FracGhost<()>>) {
            &&& !held == token.is_some()
            &&& token matches Some(t) ==> t.id() == domain@ && t.frac() == 1real
        }
    }
}

struct Guard<'a> {
    lock: &'a Lock,
    token: Tracked<FracGhost<()>>,
}

impl Lock {
    fn new() -> (s: Self) {
        let tracked token = FracGhost::<()>::new(());
        let domain = Ghost(token.id());
        let flag = AtomicBool::new(Ghost(domain), false, Tracked(Some(token)));
        Lock { flag, domain }
    }

    fn try_enter(&self) -> (g: Option<Guard<'_>>)
        ensures
            g matches Some(g) ==> g.instance_id() == self.domain@,
        resources peak(memory) <= 30,
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
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.token@.id() == self.lock.domain@
        &&& self.token@.frac() == 1real
    }

    fn leave(self)
        resources peak(memory) <= 33,
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
    closed spec fn instance_id(&self) -> Loc {
        self.lock.domain@
    }
}

impl<'a> BoundedHolder for Guard<'a> {
    open spec fn capacity(&self) -> nat {
        1
    }

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

// Keep two equal-sized allocations so only their source lifetimes distinguish them.
fn scratch(g: Guard<'_>)
    resources peak(memory) <= 256,
{
    let contained = Box::new([0u8; 64]);
    let surviving = Box::new([0u8; 64]);
    drop(contained);
    g.leave();
    drop(surviving);
}

// The callee's guard is argument 1 of this invocation.
fn relay(released: Guard<'_>, retained: Guard<'_>)
    resources peak(memory) <= 300,
{
    released.leave();
    scratch(retained);
}

fn attempt(lock: &Lock)
    resources peak(memory) <= 512,
{
    if let Some(g) = lock.try_enter() {
        let inside = Box::new([0u8; 45]);
        drop(inside);
        scratch(g);
    } else {
        let outside = Box::new([0u8; 46]);
        drop(outside);
    }
}

// Removing the tracked field ends the whole witness while the reference remains.
fn partial(g: Guard<'_>)
    resources peak(memory) <= 280,
{
    let surviving = Box::new([0u8; 51]);
    let Guard { lock, token: Tracked(unit) } = g;
    let later = Box::new([0u8; 52]);
    drop(surviving);
    drop(later);
}

fn symbolic(g: Guard<'_>, n: usize)
    requires n <= 500,
    resources peak(memory) <= n + 96,
{
    let buffer: Vec<u8> = Vec::with_capacity(n);
    drop(buffer);
    g.leave();
}

fn work() {
    let l = Lock::new();
    if let Some(g) = l.try_enter() {
        assert(g.capacity() == 1);
        g.leave();
    }
}

} // verus!
