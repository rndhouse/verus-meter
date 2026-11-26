// Both examples use the same formatter, output, and byte budget. Each worker
// writes a run of one-digit records. Worker 2, for example, writes "2\n"
// repeatedly into the third 4 MiB range of the file.
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use vstd::prelude::*;

// Use the same batch size for the executable reservations and the size queries.
macro_rules! batch_bytes {
    () => { (4usize * 1024 * 1024) };
}

// Give each worker its own Arc handle and record digit. Spawn all four before
// joining so the order of joins places no limit on simultaneous formatting.
macro_rules! four_writers {
    ($file:ident, |$peer:ident, $worker_id:ident| $body:block) => {{
        macro_rules! start {
            ($id:literal) => {{
                let $peer = $file.clone();
                std::thread::spawn(move || {
                    let $worker_id: u8 = $id;
                    $body
                })
            }};
        }
        let first = start!(0);
        let second = start!(1);
        let third = start!(2);
        let fourth = start!(3);
        first.join().unwrap();
        second.join().unwrap();
        third.join().unwrap();
        fourth.join().unwrap();
    }};
}

// Copy the formatted bytes into the worker's assigned range while its guard
// is held. Keeping this loop at the write site exposes the borrow of the
// shared vector to the memory analysis.
macro_rules! write_batch {
    ($output:ident, $formatted:ident, $worker_id:ident) => {{
        vstd::prelude::verus_exec_expr! {{
            let file = &mut *$output;
            let start = ($worker_id as usize) * batch_bytes!();
            if start + $formatted.len() <= file.len() {
                let mut index = 0usize;
                while index < $formatted.len()
                    invariant index <= $formatted.len(), start + $formatted.len() <= file.len(),
                    decreases $formatted.len() - index,
                {
                    file[start + index] = $formatted[index];
                    index += 1;
                }
            }
        }}
    }};
}

verus! {

type Batch = [u8; batch_bytes!()];
type FileContents = [u8; 4 * batch_bytes!()];
type File = Mutex<Vec<u8>>;
type Guard = MutexGuard<'static, Vec<u8>>;
type LockResult = Result<Guard, PoisonError<Guard>>;

/// `format_batch` encodes the worker's digit and a newline for every record.
/// The returned vector contains a full batch of text.
pub(super) fn format_batch(worker_id: u8) -> (text: Vec<u8>)
    requires worker_id <= 9,
    ensures text.len() == batch_bytes!(),
    resources peak(memory) <=
        2 * value_size(u8)     // One byte for worker_id and one for its ASCII digit.
        + value_size(Vec<u8>)  // The header of the returned text vector.
        + value_size(Batch),   // The 4 MiB reserved for this worker's records.
{
    let digit = b'0' + worker_id;
    let mut text = Vec::with_capacity(batch_bytes!());
    // Each digit and newline adds two bytes, so the last complete record fills the batch.
    while text.len() < batch_bytes!()
        invariant text.len() <= batch_bytes!(), text.len() % 2 == 0,
        decreases batch_bytes!() - text.len(),
    {
        text.push(digit);
        text.push(b'\n');
    }
    text
}

/// `blank_file` makes room for all four batches before the workers start.
/// A write replaces bytes in place, so the output size is independent of the lock scope.
pub(super) fn blank_file() -> (file: Vec<u8>)
    ensures file.len() == 4 * batch_bytes!(),
    resources peak(memory) <=
        value_size(Vec<u8>)          // The output vector's header.
        + value_size(FileContents),  // The 16 MiB reserved for all four batches.
{
    let mut file = Vec::with_capacity(4 * batch_bytes!());
    while file.len() < 4 * batch_bytes!()
        invariant file.len() <= 4 * batch_bytes!(),
        decreases 4 * batch_bytes!() - file.len(),
    {
        file.push(0);
    }
    file
}

/// `export_budget` counts the shared output once and allows space for the
/// given number of simultaneously live formatting buffers.
pub(super) open spec fn export_budget(live_batches: nat) -> nat {
    let file = value_size(Arc<File>)  // The coordinator's handle to the shared file.
        + 2 * value_size(usize)       // The Arc's strong and weak counters, counted once.
        + value_size(File)            // The shared mutex, including the output vector's header.
        + value_size(FileContents);   // The output bytes shared by all four workers.

    let workers = 4 * (
        value_size(std::thread::JoinHandle<()>)  // The coordinator's join handle for this worker.
        + value_size(u8)                         // The worker's completion tag, counted until join.
        + value_size(Arc<File>)                  // The worker's cloned handle to the same file.
        + value_size(u8)                         // Its numeric worker_id.
        + value_size(LockResult)                 // The result of its file.lock() call.
    );

    let writer = value_size(Guard)  // Only one worker can hold the file's mutex guard.
        + ref_size(&mut Vec<u8>)    // Its mutable reference to the output vector.
        + 2 * value_size(usize);    // Its starting offset and loop index.

    let formatter = 2 * value_size(u8)  // The parameter and ASCII digit inside format_batch.
        + value_size(Vec<u8>)           // One formatted vector's header.
        + value_size(Batch);            // Its private 4 MiB reservation.

    file + workers + writer + live_batches * formatter  // One formatter allowance per live batch.
}

} // verus!
