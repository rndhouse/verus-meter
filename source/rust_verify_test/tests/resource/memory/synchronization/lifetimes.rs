//! Simultaneous byte observations across guard, allocation and cleanup boundaries.

use super::{rejects, verifies};

/// Inspect the same source observations used for byte obligations. Whole
/// concurrent verification still requires global interference coverage.
fn boundary(case: &str, program: &str, phase: &str, live: u64) {
    let result = crate::verify_one_file(
        case,
        format!("use vstd::prelude::*; verus! {{ {program} }}"),
        &["--trace"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(result.clone(), "mutex intervals awaiting global");
    let expected = format!("memory {phase}: {live} live bytes");
    assert!(result.notes.iter().any(|note| note.message == expected), "{:?}", result.notes);
}

#[test]
fn releasing_a_lock_result_preserves_exactly_the_scratch_still_live() {
    for (name, cleanup, live) in [
        ("contained", "drop(scratch); drop(held);", 10),
        ("escapes", "drop(held); drop(scratch);", 82),
    ] {
        let source = format!(
            r#"
                fn f() resources peak(memory) <= 1000 {{
                    let m = std::sync::Mutex::new(1u8);
                    let held = m.lock();
                    let scratch = Box::new([0u8; 64]);
                    {cleanup}
                }}
        "#
        );
        boundary(name, &source, "at mutex release", live);
    }
}

#[test]
fn guard_field_destruction_uses_declaration_order() {
    let program = r#"
        struct Pair<'a> { FIELDS }
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let result = m.lock();
            if result.is_err() { return; }
            let guard = result.unwrap();
            let pair = Pair { a: Box::new([0u8; 64]), z: guard };
            drop(pair);
        }
    "#;
    let guard = "z: std::sync::MutexGuard<'a, u8>";
    let scratch = "a: Box<[u8; 64]>";
    for (case, fields, live) in [
        ("guard_field_first", format!("{guard}, {scratch}"), 90),
        ("scratch_field_first", format!("{scratch}, {guard}"), 26),
    ] {
        boundary(case, &program.replace("FIELDS", &fields), "at mutex release", live);
    }
}

#[test]
fn closure_capture_destruction_covers_either_order() {
    let program = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            let scratch = Box::new([0u8; 64]);
            let closure = move || { BODY };
            drop(closure);
        }
    "#;
    for (case, body) in [
        ("guard_first_capture", "drop(held); drop(scratch);"),
        ("scratch_first_capture", "drop(scratch); drop(held);"),
    ] {
        boundary(
            case,
            &program.replace("BODY", body),
            "during unordered capture or aggregate cleanup",
            91,
        );
    }
}

#[test]
fn waiting_and_reacquisition_retain_live_allocations() {
    // The second Result destination (9) coexists with the mutex (10), both
    // source Box handles (16), and both allocations (96) during the call.
    boundary(
        "scratch_before_reacquire",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let first = m.lock();
            let a = Box::new([0u8; 64]);
            let b = Box::new([0u8; 32]);
            drop(first);
            let second = m.lock();
            drop(a);
            drop(b);
            drop(second);
        }
    "#,
        "while waiting for the mutex",
        131,
    );
}

#[test]
fn sections_keep_the_enclosing_storage_and_guard_state() {
    let program = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let outside = Box::new([0u8; 64]);
            resources peak(memory) <= 200 {
                let held = m.lock();
                drop(held);
            }
            drop(outside);
        }
    "#;
    boundary("outer_bytes_at_inner_unlock", program, "at mutex release", 82);
    rejects(
        "reentrant_inside_section",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            resources peak(memory) <= 200 {
                let inner = m.lock();
                drop(inner);
            }
            drop(held);
        }
    "#,
        "reentrant blocking acquisition",
    );
}

#[test]
fn replacing_live_scratch_under_a_lock_checks_both_allocations() {
    let program = r#"
        struct Scratch { slot: Box<[u8; 32]> }
        fn f() resources peak(memory) <= 80 {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            let mut scratch = Scratch { slot: Box::new([0u8; 32]) };
            REPLACEMENT
            drop(scratch);
            drop(held);
        }
    "#;
    rejects(
        "one_guarded_buffer",
        &program.replace("REPLACEMENT", ""),
        "mutex intervals awaiting global",
    );
    let source = program.replace("REPLACEMENT", "scratch.slot = Box::new([0u8; 32]);");
    let errors = crate::verify_one_file(
        "two_during_replacement",
        format!("use vstd::prelude::*; verus! {{ {source} }}"),
        &[],
    )
    .unwrap_err();
    assert!(
        errors.errors.iter().any(|d| d.message.contains("memory budget exceeded")),
        "{:?}",
        errors.errors
    );
}

#[test]
fn each_loop_visit_and_early_return_cleans_its_acquisition() {
    rejects(
        "separate_lock_visits",
        r#"
        fn f(n: usize, stop: bool) resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let mut i: usize = 0;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                let held = m.lock();
                let scratch = Box::new([0u8; 32]);
                if stop { return; }
                i = i + 1;
            }
            let final_guard = m.lock();
            drop(final_guard);
        }
    "#,
        "mutex intervals awaiting global",
    );
}

#[test]
fn a_workers_scratch_is_checked_at_its_own_lock_site() {
    let program = r#"
        fn f() resources peak(memory) <= 2000 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(0u8));
            let child = std::thread::spawn(move || {
                let held = m.lock();
                let scratch = Box::new([0u8; SIZE]);
                assert(current(memory) <= 128);
                drop(scratch);
                drop(held);
            });
            let done = child.join();
        }
    "#;
    verifies("small_worker_scratch", &program.replace("SIZE", "32"));
    let errors = crate::verify_one_file(
        "large_worker_scratch",
        format!("use vstd::prelude::*; verus! {{ {} }}", program.replace("SIZE", "256")),
        &[],
    )
    .unwrap_err();
    assert!(
        errors.errors.iter().any(|d| d.message.contains("memory budget exceeded")),
        "{:?}",
        errors.errors
    );
}

#[test]
fn inline_capture_storage_is_live_when_an_embedded_guard_unlocks() {
    boundary(
        "inline_capture_at_release",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            let closure = {
                let bytes = [0u8; 64];
                move || { drop(held); let copy = bytes; }
            };
            drop(closure);
        }
    "#,
        "at mutex release",
        83,
    );
}

#[test]
fn returning_owned_scratch_preserves_its_charge_across_unlock() {
    boundary(
        "scratch_returned_after_unlock",
        r#"
        fn make() -> (result: Box<[u8; 64]>) resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            let buffer = Box::new([0u8; 64]);
            drop(held);
            buffer
        }
    "#,
        "at mutex release",
        82,
    );
}

#[test]
fn a_symbolic_reservation_remains_live_across_unlock() {
    let program = r#"
        fn f(n: usize) requires n < 1000, resources peak(memory) <= BOUND + n {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            let buffer = Vec::<u8>::with_capacity(n);
            drop(held);
            let after = Box::new([0u8; 128]);
            drop(after);
            drop(buffer);
        }
    "#;
    // The 42-byte frame and n reserved slots coexist with another 136 bytes after unlock.
    rejects(
        "symbolic_survivor",
        &program.replace("BOUND", "178"),
        "mutex intervals awaiting global",
    );
    let errors = crate::verify_one_file(
        "symbolic_survivor_short",
        format!("use vstd::prelude::*; verus! {{ {} }}", program.replace("BOUND", "177")),
        &[],
    )
    .unwrap_err();
    assert!(
        errors.errors.iter().any(|d| d.message.contains("memory budget exceeded")),
        "{:?}",
        errors.errors
    );
}

#[test]
fn publishing_under_a_guard_transfers_storage_to_an_independent_worker() {
    let program = r#"
        fn f() resources peak(memory) <= 2000 {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            let scratch = Box::new([0u8; 64]);
            let child = std::thread::spawn(move || {
                assert(current(memory) <= LIMIT);
                drop(scratch);
            });
            CLEANUP
        }
    "#;
    for (name, cleanup, locked_join) in [
        ("unlock_before_join", "drop(held); let done = child.join();", false),
        ("join_before_unlock", "let done = child.join(); drop(held);", true),
    ] {
        let source = program.replace("CLEANUP", cleanup);
        let code = |limit: &str| {
            format!("use vstd::prelude::*; verus! {{ {} }}", source.replace("LIMIT", limit))
        };
        let good = crate::verify_one_file(&format!("{name}_72"), code("72"), &["--trace"]).unwrap();
        assert!(
            good.notes
                .iter()
                .any(|n| n.message.starts_with("memory after transferring worker captures:")),
            "{:?}",
            good.notes
        );
        assert_eq!(
            good.notes.iter().any(|n| n.message.starts_with("memory while waiting for a worker:")),
            locked_join
        );
        let short = crate::verify_one_file(&format!("{name}_71"), code("71"), &[]).unwrap_err();
        assert!(
            short.errors.iter().any(|e| e.message.contains("live 72 bytes exceeds bound 71 bytes")),
            "{:?}",
            short.errors
        );
    }
}

#[test]
fn a_conditional_return_preserves_both_release_footprints() {
    let program = r#"
        fn f(stop: bool) resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            let held = m.lock();
            let scratch = Box::new([0u8; 64]);
            if stop { return; }
            drop(held);
            drop(scratch);
        }
    "#;
    // On the return edge, reverse lexical order drops the temporary buffer
    // first. The condition (1), mutex (10), and implicitly destroyed Result
    // slot (9) are still live. The explicit drop consumes its Result operand.
    boundary("return_with_guard", program, "at mutex release", 20);
    boundary("fallthrough_with_guard", program, "at mutex release", 83);
}
