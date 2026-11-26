// This example shows how Verus Meter counts buffers that outlive the workers
// that allocate them.
//
// Each of four workers puts a buffer into a shared vector. After all four
// joins, the shared vector can still own all four buffers. The checkpoint in
// `main` counts their reservations and Vec headers.
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

verus! {

/// Number of bytes each worker reserves for its buffer.
const PAYLOAD_BYTES: usize = 256;

type Cell = Mutex<Vec<Vec<u8>>>;
type SharedCell = Arc<Cell>;
type Job = std::thread::JoinHandle<()>;
type Guard = std::sync::MutexGuard<'static, Vec<Vec<u8>>>;
type LockResult = Result<Guard, std::sync::PoisonError<Guard>>;
type Payload = [u8; PAYLOAD_BYTES];

/// `retained_entry` counts one inner vector's header and reserved payload in the shared collection.
spec fn retained_entry() -> nat {
    value_size(Vec<u8>)        // The inner vector's header, stored in one outer vector slot.
        + value_size(Payload)  // The byte reservation owned by that inner vector.
}

/// `retained_budget` bounds the workers, the shared collection, and a buffer
/// being added while a worker holds the mutex.
spec fn retained_budget() -> nat {
    let shared = value_size(SharedCell)  // The caller's Arc handle to the collection.
        + 2 * value_size(usize)          // Strong and weak counters shared by all Arc handles.
        + value_size(Cell)               // The mutex, including the outer vector's header.
        + 4 * retained_entry();          // Up to one stored buffer from each worker.

    let workers = 4 * (
        value_size(Job)           // The caller's join handle for this worker.
        + value_size(u8)          // The worker's completion tag, counted until join.
        + value_size(SharedCell)  // The worker's cloned Arc handle to the same collection.
        + value_size(LockResult)  // The result of this worker's lock call.
    );

    // This peak bound allows for a full collection even while a worker prepares its entry.
    shared + workers
        + value_size(Guard)  // The guard held by the one worker doing the push.
        + retained_entry()   // Its local buffer before the push transfers ownership.
}

/// `main` starts four workers and checks how much memory the shared vector
/// can still own after they join.
fn main()
    resources peak(memory) <= retained_budget(),
{
    let cell = Arc::new(Cell::new(Vec::new()));
    four_workers!(cell, |peer| {
        let result = peer.lock();
        if result.is_err() { return; }
        let mut guard = result.unwrap();
        let buffer = Vec::<u8>::with_capacity(PAYLOAD_BYTES);
        guard.push(buffer);
    });
    // After all four joins, the caller still owns the collection.
    assert(current(memory) <=
        value_size(SharedCell)     // The caller's remaining Arc handle.
        + 2 * value_size(usize)    // The strong and weak counters for that allocation.
        + value_size(Cell)         // The mutex and outer vector header.
        + 4 * (value_size(Vec<u8>) + value_size(Payload)));  // Up to four inner headers and their buffers.
    drop(cell);  // Dropping the last Arc releases the collection and its buffers.
}

} // verus!
