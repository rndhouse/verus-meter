// This example shows how Verus Meter counts buffers that outlive the workers
// that allocate them.
//
// Each of four workers puts a buffer into a shared vector. After all four
// joins, the caller can still own four buffer reservations and their Vec
// headers. The checkpoint in `retained` verifies that bound.
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

// Start all four workers, then join them before checking what the vector owns.
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

        first.join().unwrap();
        second.join().unwrap();
        third.join().unwrap();
        fourth.join().unwrap();
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

/// `retained_entry` counts one inner vector's header and reserved payload in the shared collection.
spec fn retained_entry() -> nat {
    value_size(Vec<u8>) + value_size(Payload)
}

/// `retained_budget` bounds the workers, the shared collection, and a buffer
/// being added while a worker holds the mutex.
spec fn retained_budget() -> nat {
    // Count the caller's Arc, its two reference counts, and the mutex once.
    // Each successful worker can leave one buffer in the shared vector.
    let shared = value_size(SharedCell) + 2 * value_size(usize) + value_size(Cell)
        + 4 * retained_entry();

    // All four workers can be outstanding. Allow for each one's lock result
    // as well as its join handle, completion tag, and captured Arc.
    let workers = 4 * (value_size(Job) + value_size(u8) + value_size(SharedCell)
        + value_size(LockResult));

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

/// `main` runs the four workers and checks the storage retained after they join.
fn main() {
    retained();
}

} // verus!
