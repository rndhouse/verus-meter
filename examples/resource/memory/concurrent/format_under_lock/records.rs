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
    resources peak(memory) <= 2 * value_size(u8) + value_size(Vec<u8>) + value_size(Batch),
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
    resources peak(memory) <= value_size(Vec<u8>) + value_size(FileContents),
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
    // The coordinator owns one Arc. Its backing holds the reference counts
    // and the mutex with its vector header. FileContents counts the reserved bytes.
    let file = value_size(Arc<File>) + 2 * value_size(usize) + value_size(File)
        + value_size(FileContents);

    // Each worker has a join handle and completion tag, a captured Arc,
    // a worker ID, and the result of trying to lock the file.
    let workers = 4 * (value_size(std::thread::JoinHandle<()>) + value_size(u8)
        + value_size(Arc<File>) + value_size(u8) + value_size(LockResult));

    // One writer holds the guard, borrows the output, and tracks its start and index.
    let writer = value_size(Guard) + ref_size(&mut Vec<u8>) + 2 * value_size(usize);

    // Each formatter uses its input ID, encoded digit, vector header, and reserved bytes.
    let formatter = 2 * value_size(u8) + value_size(Vec<u8>) + value_size(Batch);
    file + workers + writer + live_batches * formatter
}

} // verus!
