// A concrete payload exercises all six verified RwLock workspaces.
use vstd::prelude::*;
use vstd::rwlock::{ReadHandle, RwLock, RwLockPredicate, WriteHandle};

verus! {

struct Any;

impl<T> RwLockPredicate<T> for Any {
    open spec fn inv(self, _: T) -> bool { true }
}

fn layouts() {
    assert(value_size(RwLock<u32, Any>) == 13);
    assert(value_size(ReadHandle<'static, u32, Any>) == 8);
    assert(value_size(WriteHandle<'static, u32, Any>) == 8);
    assert(value_size(RwLock<Vec<u8>, Any>) == 33);
}

fn read(lock: &RwLock<u32, Any>)
    resources peak(memory) <= 98,
{
    let guard = lock.acquire_read();
    let scratch = Box::new([0u8; 55]);
    drop(scratch);
    guard.release_read();
}

fn make(v: u32) -> RwLock<u32, Any>
    resources peak(memory) <= 46,
{
    RwLock::new(v, Ghost(Any))
}

// The same constructor has a different frame at a larger payload width.
fn make_wide(v: [u8; 128]) -> RwLock<[u8; 128], Any>
    resources peak(memory) <= 777,
{
    RwLock::new(v, Ghost(Any))
}

fn end(guard: ReadHandle<'static, u32, Any>)
    resources peak(memory) <= 72,
{
    guard.release_read();
}

fn get(guard: &ReadHandle<'static, u32, Any>) -> u32
    resources peak(memory) <= 60,
{
    *guard.borrow()
}

fn write(lock: &RwLock<u32, Any>)
    resources peak(memory) <= 85,
{
    let (value, guard) = lock.acquire_write();
    guard.release_write(value);
}

fn inner(lock: RwLock<u32, Any>) -> u32
    resources peak(memory) <= 94,
{
    lock.into_inner()
}

} // verus!
