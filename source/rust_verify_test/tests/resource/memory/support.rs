//! Shared memory-test assertions; execution still uses the fork's isolated runner.

use crate::{common::assert_vir_error_msg, verify_one_file};

fn source(code: &str) -> String {
    format!("use vstd::prelude::*; verus! {{ {code} }}")
}

#[track_caller]
pub(super) fn verifies(name: &str, code: &str) {
    verify_one_file(name, source(code), &[]).unwrap();
}

#[track_caller]
pub(super) fn rejects(name: &str, code: &str, message: &str) {
    let err = verify_one_file(name, source(code), &[]).unwrap_err();
    assert!(
        !err.errors.is_empty() && err.errors.iter().all(|e| e.message.contains(message)),
        "expected {}: {:?}",
        message,
        err
    );
}

// Exact boundaries need both acceptance and rejection, with one diagnostic.
// A zero-byte peak has no smaller valid unsigned budget to test.
#[track_caller]
pub(super) fn exact_peak(name: &str, code: &str, peak: u64) {
    let bounded = |budget| source(&code.replace("BUDGET", &format!("{budget}u64")));
    verify_one_file(name, bounded(peak), &[]).unwrap();
    if peak > 0 {
        let err = verify_one_file(&format!("{name}_short"), bounded(peak - 1), &[]).unwrap_err();
        assert_vir_error_msg(err, &format!("peak {peak} bytes exceeds budget {} bytes", peak - 1));
    }
}
