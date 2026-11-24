// The caller knows the semaphore's capacity symbolically. Its identity, permit
// lifetime, and the executable acquire/release workspaces come from verified vstd.
use vstd::prelude::*;
use vstd::resource::holder::{BoundedHolder, Holder};
use vstd::resource::semaphore::{Permit, Semaphore};

verus! {

// Creation accounts for both verified constructor bodies at any input capacity.
fn create(k: usize) -> (s: Semaphore)
    ensures s.capacity() == k,
    resources peak(memory) <= 40,
{
    Semaphore::new(k)
}

fn attempt(s: &Semaphore) -> (q: Option<Permit<'_>>)
    ensures q matches Some(p) ==> p.instance_id() == s.id() && p.capacity() == s.capacity(),
    resources peak(memory) <= 81,
{
    s.try_acquire()
}

fn wait(s: &Semaphore) -> (q: Permit<'_>)
    ensures q.instance_id() == s.id() && q.capacity() == s.capacity(),
    resources peak(memory) <= 98,
{
    s.acquire()
}

fn release(p: Permit<'_>)
    resources peak(memory) <= 72,
{
    p.release();
}

fn retain(p: Permit<'_>, keep: bool) -> (q: Option<Permit<'_>>)
    ensures q matches Some(q) ==> q == p,
    resources peak(memory) <= 128,
{
    if keep { Some(p) } else { p.release(); None }
}

fn use_returned(p: Permit<'_>, keep: bool)
    resources peak(memory) <= 256,
{
    if let Some(q) = retain(p, keep) {
        let inside = Box::new([0u8; 73]);
        let surviving = Box::new([0u8; 74]);
        drop(inside);
        q.release();
        drop(surviving);
    }
}

fn scratch(p: Permit<'_>, n: usize)
    requires n <= 500,
    resources peak(memory) <= if n <= 40 { 80 } else { n + 40 },
{
    let data: Vec<u8> = Vec::with_capacity(n);
    drop(data);
    p.release();
}

fn different_instances(a: &Semaphore, b: &Semaphore, k: usize)
    requires a.capacity() == k,
    resources peak(memory) <= 256,
{
    if let Some(first) = a.try_acquire() {
        let second = b.acquire();
        assert(first.instance_id() == a.id() && first.capacity() == k);
        assert(second.instance_id() == b.id());
        first.release();
        second.release();
    }
}

fn layouts() {
    assert(value_size(Permit) == 8);
    assert(value_size(Option<Permit>) == 9);
    assert(value_size(Semaphore) == 8);
}

fn two(a: &Semaphore, b: &Semaphore) resources peak(memory) <= 512, {
    let g = wait(a);
    let one = Box::new([0u8; 47]);
    drop(one);
    g.release();
    if let Some(q) = attempt(b) {
        let two = Box::new([0u8; 48]);
        drop(two);
        q.release();
    }
}

} // verus!
