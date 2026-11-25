// This example shows how Verus Meter proves that four concurrent workers can
// each request 4 KiB of scratch and use at most 4 KiB of scratch between them.
//
// In `scratch`, each worker calls a helper that allocates and frees its buffer
// while the worker holds the mutex. The proof works for any requested buffer
// size and any order in which the workers acquire the lock.
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

// Start every worker before joining any of them, so the join order alone
// cannot explain the one-buffer bound.
macro_rules! four_workers {
    ($cell:ident, |$peer:ident| $body:block) => {{
        let $peer = $cell.clone();
        let first = std::thread::spawn(move || $body);
        let $peer = $cell.clone();
        let second = std::thread::spawn(move || $body);
        let $peer = $cell.clone();
        let third = std::thread::spawn(move || $body);
        let $peer = $cell.clone();
        let fourth = std::thread::spawn(move || $body);

        let a = first.join().unwrap();
        let b = second.join().unwrap();
        let c = third.join().unwrap();
        let d = fourth.join().unwrap();
    }};
}

verus! {

type Cell = Mutex<()>;
type SharedCell = Arc<Cell>;
type Job = std::thread::JoinHandle<()>;
type Guard = std::sync::MutexGuard<'static, ()>;
type LockResult = Result<Guard, std::sync::PoisonError<Guard>>;

/// `shared_cell` counts the caller's handle and the backing storage shared by all four workers.
spec fn shared_cell() -> nat {
    // The caller keeps one Arc handle. All its clones share the two reference
    // counts and the mutex used to serialize scratch allocations.
    value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell)
}

/// `published_worker` counts the join handle, completion tag, and shared handle
/// associated with one spawned worker.
spec fn published_worker() -> nat {
    value_size(Job) + value_size(u8) + value_size(SharedCell)
}

/// `temporary` reserves a scratch buffer and frees it before returning to the worker.
fn temporary(buffer_capacity: u16)
    resources peak(memory) <= buffer_capacity * value_size(u8)
        + value_size(Vec<u8>) + value_size(buffer_capacity),
{
    let scratch = Vec::<u8>::with_capacity(buffer_capacity as usize);
    drop(scratch);
}

/// `scratch_frames` bounds the caller and worker storage that can coexist with
/// a call to `temporary`.
spec fn scratch_frames(buffer_capacity: u16) -> nat {
    // Count the shared cell and the caller's size parameter once. Each of the
    // four workers has its own captured size and space for its lock result.
    shared_cell() + value_size(buffer_capacity)
        + 4 * (published_worker() + value_size(buffer_capacity) + value_size(LockResult))
}

/// `scratch` runs four workers that free their scratch before unlocking the mutex.
/// Their combined peak therefore includes only one scratch reservation.
fn scratch(buffer_capacity: u16)
    resources peak(memory) <= scratch_frames(buffer_capacity) + peak(temporary(buffer_capacity)),
{
    let cell = Arc::new(Cell::new(()));
    four_workers!(cell, |peer| {
        let guard = peer.lock();
        temporary(buffer_capacity);
        drop(guard);
    });
    // All four joins have returned. The caller still owns its input and the
    // shared cell, and each worker's scratch has already been freed.
    assert(current(memory) <= value_size(buffer_capacity) + value_size(SharedCell)
        + 2 * value_size(usize) + value_size(Cell));
    drop(cell);
}

/// `main` runs four workers with a 4 KiB scratch buffer per worker.
fn main() {
    scratch(4096);
}

} // verus!
