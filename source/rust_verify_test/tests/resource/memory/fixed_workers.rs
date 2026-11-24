//! Whole-function contracts over actual fixed workers and source mutex guards.
use super::support::verifies;

/// Either worker and its enclosing operation can independently exceed a bound.
fn exceeds(name: &str, body: &str) {
    let err =
        crate::verify_one_file(name, format!("use vstd::prelude::*; verus! {{ {body} }}"), &[])
            .unwrap_err();
    assert!(!err.errors.is_empty());
    assert!(
        err.errors.iter().all(|e| e.message.contains("memory budget exceeded")),
        "{:?}",
        err.errors
    );
}

fn pair(bound: &str, peer: &str, body: &str) -> String {
    let worker = |lock| body.replace("LOCK", lock);
    let first = worker("left");
    let second = worker("right");
    format!(
        r#"
        fn work(b: u16) resources peak(memory) <= {bound} {{
            let left = std::sync::Arc::new(std::sync::Mutex::new(0u8));
            let right = {peer};
            let a = vstd::thread::spawn(move || {{ {first} }});
            let c = vstd::thread::spawn(move || {{ {second} }});
            let a_done = a.join();
            let c_done = c.join();
        }}
    "#
    )
}

const GUARDED: &str = "
    let guard = LOCK.lock();
    let scratch = Vec::<u8>::with_capacity(b as usize);
    drop(scratch);
    drop(guard);
";

#[test]
fn one_mutex_bounds_two_symbolic_buffers() {
    // Caller scalar (2), one Arc backing (26), tags and join handles (18),
    // two captured environments (20), two lock Result slots (18) and Vec (24).
    verifies("guarded_pair", &pair("b + 108", "left.clone()", GUARDED));
    exceeds("guarded_one_byte_short", &pair("b + 107", "left.clone()", GUARDED));
    let distinct = "std::sync::Arc::new(std::sync::Mutex::new(0u8))";
    // A second backing (26) and another Vec slot (24) can now coexist.
    verifies("independent_pair", &pair("2 * b + 158", distinct, GUARDED));
    exceeds("distinct_pair_short", &pair("b + 256", distinct, GUARDED));
}

#[test]
fn waiting_and_released_buffers_can_overlap() {
    let waiting = "let scratch = Vec::<u8>::with_capacity(b as usize);
                   let guard = LOCK.lock(); drop(scratch); drop(guard);";
    let released =
        GUARDED.replace("drop(scratch);\n    drop(guard);", "drop(guard); drop(scratch);");
    for (name, body) in [("before_lock", waiting), ("after_unlock", released.as_str())] {
        verifies(name, &pair("2 * b + 256", "left.clone()", body));
        exceeds(name, &pair("b + 256", "left.clone()", body));
    }
}

#[test]
fn one_acquisition_covers_the_sum_of_its_live_buffers() {
    let two = GUARDED.replace(
        "drop(scratch);",
        "let second = Vec::<u8>::with_capacity(b as usize); drop(scratch); drop(second);",
    );
    verifies("two_under_one_guard", &pair("2 * b + 256", "left.clone()", &two));
    exceeds("two_under_one_guard_short", &pair("b + 256", "left.clone()", &two));
}

#[test]
fn joining_before_the_next_spawn_ends_the_overlap() {
    let body = "drop(LOCK); let v = Vec::<u8>::with_capacity(b as usize); drop(v);";
    let unrestricted = pair("b + 256", "left.clone()", body);
    let sequential = unrestricted
        .replace("let a_done = a.join();", "")
        .replace("let c = vstd", "let a_done = a.join(); let c = vstd");
    verifies("sequential_pair", &sequential);
    exceeds("overlapping_pair", &unrestricted);
    verifies("unrestricted_pair", &unrestricted.replace("b + 256", "2 * b + 256"));
}

#[test]
fn concurrent_exports_wait_for_the_byte_proof_and_erased_rust_checks() {
    let source = |bound| {
        format!("use vstd::prelude::*; verus! {{ {} }}", pair(bound, "left.clone()", GUARDED))
    };
    let dir = tempfile::tempdir().unwrap();
    let artifact = dir.path().join("workers.vir");
    let export = format!("--export={}", artifact.display());
    for mode in ["--no-verify", "--no-erasure-check"] {
        let err = crate::verify_one_file("unchecked_pair", source("b + 108"), &[mode, &export])
            .unwrap_err();
        crate::common::assert_vir_error_msg(err, "require verification of worker bodies");
        assert!(!artifact.exists());
    }
    crate::verify_one_file("invalid_pair", source("b + 107"), &[&export]).unwrap_err();
    assert!(!artifact.exists());
    crate::verify_one_file("verified_pair", source("b + 108"), &[&export]).unwrap();
    assert!(artifact.is_file());
}

#[test]
fn caller_storage_overlaps_workers_before_join() {
    let work = pair("b + 256", "left.clone()", GUARDED);
    let caller = "let local = Vec::<u8>::with_capacity(b as usize); drop(local);";
    let running = work.replace("let a_done =", &format!("{caller} let a_done ="));
    let joined =
        work.replace("let c_done = c.join();", &format!("let c_done = c.join(); {caller}"));
    exceeds("caller_and_worker", &running);
    verifies("caller_after_join", &joined);
}

#[test]
fn extracting_a_native_guard_preserves_the_acquisition() {
    let guard = GUARDED.replace(
        "let guard = LOCK.lock();",
        "let result = LOCK.lock(); if result.is_err() { return; } let guard = result.unwrap();",
    );
    verifies("extracted_mutex_guard", &pair("b + 256", "left.clone()", &guard));
}

#[test]
fn a_failed_try_lock_does_not_cover_scratch() {
    let attempt = GUARDED.replace("LOCK.lock()", "LOCK.try_lock()");
    verifies("failed_attempt_pair", &pair("2 * b + 256", "left.clone()", &attempt));
    exceeds("failed_attempt_pair_short", &pair("b + 256", "left.clone()", &attempt));
}
