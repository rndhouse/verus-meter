//! Shared memory-test assertions; execution still uses the fork's isolated runner.

use crate::{common::assert_vir_error_msg, verify_one_file};

/// Supply the same prelude and Verus block to every snippet-based assertion.
fn source(code: &str) -> String {
    format!("use vstd::prelude::*; verus! {{ {code} }}")
}

/// Check a snippet with the standard Verus prelude and require verification success.
#[track_caller]
pub(super) fn verifies(name: &str, code: &str) {
    verify_one_file(name, source(code), &[]).unwrap();
}

/// Require real diagnostics and check that every error contains the expected message.
#[track_caller]
pub(super) fn rejects(name: &str, code: &str, message: &str) {
    let err = verify_one_file(name, source(code), &[]).unwrap_err();
    assert!(
        !err.errors.is_empty() && err.errors.iter().all(|e| e.message.contains(message)),
        "expected {message}: {error:?}",
        error = err
    );
}

/// Accept the predicted bound and reject one byte less with a single diagnostic.
/// Zero-byte peaks have no smaller valid unsigned budget to test.
#[track_caller]
pub(super) fn exact_peak(name: &str, code: &str, peak: u64) {
    let bounded = |budget| source(&code.replace("BUDGET", &format!("{budget}u64")));
    verify_one_file(name, bounded(peak), &[]).unwrap();
    if peak > 0 {
        let short = peak - 1;
        let err = verify_one_file(&format!("{name}_short"), bounded(short), &[]).unwrap_err();
        assert_vir_error_msg(err, &format!("peak {peak} bytes exceeds budget {short} bytes"));
    }
}
