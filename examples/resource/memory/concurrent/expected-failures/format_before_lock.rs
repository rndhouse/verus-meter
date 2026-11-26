// rust_verify/tests/example.rs expect-failures --- Formatting before locking exceeds the one-buffer bound.
// This example shows why shortening a file lock can increase peak memory.
//
// Moving format_batch before lock() lets the workers prepare records in
// parallel. They still write the same bytes into the same four file ranges,
// but all four can now hold a 4 MiB buffer before the first write. The old
// bound allows only one. Compare format_under_lock/mod.rs.
//
// Look for the two `FAIL:` comments at the one-buffer bound and the call moved before the lock.
#[macro_use]
#[path = "../format_under_lock/records.rs"]
mod records;

use records::{blank_file, export_budget, format_batch};
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

verus! {

/// `export_records` starts all four writers before joining any of them.
/// The one-buffer claim fails because formatting can overlap across workers.
fn export_records()
    // FAIL: This bound allows only one live formatting buffer across all four workers.
    resources peak(memory) <= export_budget(1),
{
    let file = Arc::new(Mutex::new(blank_file()));
    four_writers!(file, |file, worker_id| {
        // FAIL: Each worker can finish formatting before any worker acquires the file lock.
        // At that point all four buffers are live.
        let formatted = format_batch(worker_id);
        let lock = file.lock();
        if lock.is_err() { return; }
        let mut output = lock.unwrap();
        write_batch!(output, formatted, worker_id);
        drop(formatted);
    });
}

/// `main` exports four batches of newline-delimited records.
fn main() {
    export_records();
}

} // verus!
