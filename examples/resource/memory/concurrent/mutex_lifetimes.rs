// This example shows how Verus Meter proves that four concurrent workers can
// each request 4 KiB of scratch and use at most 4 KiB of scratch between them.
// In `scratch`, each worker calls a helper that allocates and frees its buffer
// while the worker holds the mutex. The proof works for any requested buffer
// size and any order in which the workers acquire the lock.
//
// In `retained`, each worker saves its buffer in a shared vector before
// unlocking. Verus Meter tracks the buffers as the vector takes ownership.
// After all four workers finish, a bound that counts only one buffer fails
// verification because the vector can still hold all four.
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

// One requested reservation, shared by the executable allocation and its size formula.
macro_rules! payload_bytes {
    () => { 256 };
}

verus! {

type Cell = Mutex<Vec<Vec<u8>>>;
type SharedCell = Arc<Cell>;
type Job = std::thread::JoinHandle<()>;
type Guard = std::sync::MutexGuard<'static, Vec<Vec<u8>>>;
type LockResult = Result<Guard, std::sync::PoisonError<Guard>>;
type Payload = [u8; payload_bytes!()];

/// `shared_cell` counts the caller's handle and the backing storage shared by all four workers.
spec fn shared_cell() -> nat {
    // The caller keeps one Arc handle. All its clones share the two reference
    // counts and the mutex containing the outer Vec header.
    value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell)
}

/// `published_worker` counts the join handle, completion tag, and shared handle
/// associated with one spawned worker.
spec fn published_worker() -> nat {
    value_size(Job) + value_size(u8) + value_size(SharedCell)
}

/// `temporary` reserves a scratch buffer and frees it before returning to the worker.
fn temporary(bytes: u16)
    resources peak(memory) <= bytes + value_size(Vec<u8>) + value_size(bytes),
{
    let scratch = Vec::<u8>::with_capacity(bytes as usize);
    drop(scratch);
}

/// `scratch_frames` bounds the caller and worker storage that can coexist with
/// a call to `temporary`.
spec fn scratch_frames(bytes: u16) -> nat {
    // Count the shared cell and the caller's size parameter once. Each of the
    // four workers has its own captured size and space for its lock result.
    shared_cell() + value_size(bytes)
        + 4 * (published_worker() + value_size(bytes) + value_size(LockResult))
}

/// `scratch` runs four workers that free their scratch before unlocking the mutex.
/// Their combined peak therefore includes only one scratch reservation.
fn scratch(bytes: u16)
    resources peak(memory) <= scratch_frames(bytes) + peak(temporary(bytes)),
{
    let cell = Arc::new(Cell::new(Vec::new()));
    four_workers!(cell, |peer| {
        let guard = peer.lock();
        temporary(bytes);
        drop(guard);
    });
    // All four joins have returned. The caller still owns its input and the
    // shared cell, and each worker's scratch has already been freed.
    assert(current(memory) <= value_size(bytes) + value_size(SharedCell)
        + 2 * value_size(usize) + value_size(Cell));
    drop(cell);
}

/// `retained_entry` counts one inner vector's header and reserved payload in the shared collection.
spec fn retained_entry() -> nat {
    value_size(Vec<u8>) + value_size(Payload)
}

/// `retained_budget` bounds the workers, the shared collection, and a buffer
/// being added while a worker holds the mutex.
spec fn retained_budget() -> nat {
    // Each successful worker can leave one buffer in the shared vector.
    let shared = shared_cell() + 4 * retained_entry();

    // All four workers can be outstanding. Allow for each one's lock result
    // as well as its join handle, completion tag, and captured Arc.
    let workers = 4 * (published_worker() + value_size(LockResult));

    // The worker doing a push also holds a guard and supplies the new entry.
    // Adding that entry to the full collection bound is conservative.
    shared + workers + value_size(Guard) + retained_entry()
}

/// `retained` lets each worker add a buffer to the shared vector under the mutex.
/// The vector can still own all four buffers after the workers finish.
fn retained()
    resources peak(memory) <= retained_budget(),
{
    let cell = Arc::new(Cell::new(Vec::new()));
    four_workers!(cell, |peer| {
        let result = peer.lock();
        if result.is_err() { return; }
        let mut guard = result.unwrap();
        let buffer = Vec::<u8>::with_capacity(payload_bytes!());
        guard.push(buffer);
    });
    // After the joins, the outer vector can still own four inner Vec headers
    // and their payloads. Dropping the caller's last Arc frees the collection.
    assert(current(memory) <= value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell)
        + 4 * (value_size(Vec<u8>) + value_size(Payload)));
    drop(cell);
}

/// `main` runs both mutex examples to show how freeing or retaining a buffer changes the bound.
fn main() {
    scratch(4096);
    retained();
}

} // verus!
