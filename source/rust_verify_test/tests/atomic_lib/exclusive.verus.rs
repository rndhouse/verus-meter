// Client variations for the custom lock in examples/resource/memory/concurrent/protocol.
verus! {

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

// Reserving n bytes needs n + 40. At n = 0, release is the peak:
// the release helper needs 33 bytes while the 8-byte length remains live.
fn symbolic(g: Guard<'_>, n: usize)
    requires n <= 500,
    resources peak(memory) <= if n == 0 { 41 } else { n + 40 },
{
    let buffer: Vec<u8> = Vec::with_capacity(n);
    drop(buffer);
    g.leave();
}

// Moving the guard transfers the same witness and keeps the existing scratch covered.
fn rename(g: Guard<'_>)
    resources peak(memory) <= 256,
{
    let data = Box::new([0u8; 61]);
    let next = g;
    drop(data);
    next.leave();
}

// The last statement runs while the incoming guard is still owned. The retained
// vector keeps a symbolic byte term live at the implicit end of the block.
fn lexical(g: Guard<'_>, n: usize)
    requires n <= 500,
    resources peak(memory) <= n + 111,
{
    let retained: Vec<u8> = Vec::with_capacity(n);
    let last = Box::new([0u8; 63]);
    drop(last);
}

// The returned witness belongs to the selected input, even through another
// helper. The failure branch consumes that same input before returning None.
fn carry(g: Guard<'_>) -> (q: Guard<'_>)
    ensures q == g,
    resources peak(memory) <= 16,
{
    g
}

fn keep_guard<'a>(unused: Guard<'a>, selected: Guard<'a>, keep: bool) -> (q: Option<Guard<'a>>)
    ensures q matches Some(p) ==> p == selected,
    resources peak(memory) <= 128,
{
    unused.leave();
    if keep { Some(carry(selected)) } else { selected.leave(); None }
}

fn resume<'a>(a: Guard<'a>, b: Guard<'a>, keep: bool)
    resources peak(memory) <= 256,
{
    let ghost issuer = a.instance_id();
    let ghost limit = a.capacity();
    let result = keep_guard(b, a, keep);
    if let Some(q) = result {
        assert(q.instance_id() == issuer && q.capacity() == limit);
        let data = Box::new([0u8; 67]);
        let survives = Box::new([0u8; 66]);
        drop(data);
        q.leave();
        drop(survives);
    }
}

// Both guards have the same Rust type. An early return can select a different
// issuer from the tail, so neither caller input identifies every result.
fn choose_guard<'a>(a: Guard<'a>, b: Guard<'a>, left: bool) -> Guard<'a>
    resources peak(memory) <= 128,
{
    if left {
        b.leave();
        return a;
    }
    a.leave();
    b
}

fn use_choice<'a>(a: Guard<'a>, b: Guard<'a>, left: bool)
    resources peak(memory) <= 256,
{
    let q = choose_guard(a, b, left);
    let data = Box::new([0u8; 68]);
    drop(data);
    q.leave();
}

fn work() {
    let l = Lock::new();
    if let Some(g) = l.try_enter() {
        assert(g.capacity() == 1);
        g.leave();
    }
}

} // verus!
