// This example shows how four workers can format 4 MiB of records each with
// room for just one 4 MiB formatting buffer.
//
// Imagine four workers processing independent inputs. This example starts
// at export, when each worker has a result to write. Each takes the file
// lock, formats its records, writes them, and frees its private buffer.
//
// Each worker writes to its own range of a shared, in-memory output file.
// The file reserves a separate 16 MiB whichever worker writes first.
#[macro_use]
mod records;

use records::{blank_file, export_budget, format_batch};
use std::sync::{Arc, Mutex};
use vstd::prelude::*;

verus! {

/// `export_records` starts all four writers before joining any of them.
/// Holding the file lock across formatting makes one buffer sufficient.
fn export_records()
    resources peak(memory) <= export_budget(1),
{
    let file = Arc::new(Mutex::new(blank_file()));
    four_writers!(file, |file, worker_id| {
        let lock = file.lock();
        if lock.is_err() { return; }
        let mut output = lock.unwrap();
        let formatted = format_batch(worker_id);
        write_batch!(output, formatted, worker_id);
        drop(formatted);
    });
}

/// `main` exports four batches of newline-delimited records.
fn main() {
    export_records();
}

} // verus!
