//! Size queries and fail-closed compiler integration for synchronization contracts.
use super::support::{rejects, verifies};

#[test]
fn opaque_sizes_are_source_model_values() {
    verifies(
        "synchronization_sizes",
        r#"
        fn sizes() resources peak(memory) <= 0 {
            assert(value_size(std::sync::Mutex<u64>) == 17);
            assert(value_size(std::sync::MutexGuard<'static, u64>) == 8);
            assert(value_size(Result<u8, u64>) == 9);
        }
    "#,
    );
}

#[test]
fn tracked_guards_are_not_runtime_memory_roots() {
    verifies(
        "tracked_guard",
        r#"
        fn f(tracked guard: std::sync::MutexGuard<'static, u64>)
            resources peak(memory) <= 0 {}
    "#,
    );
}

#[test]
fn mutex_construction_keeps_the_owned_payload_until_drop() {
    let source = r#"
        fn f() resources peak(memory) <= 1000 {
            let mut input = Vec::<Box<[u8; 64]>>::with_capacity(2);
            input.push(Box::new([0u8; 64]));
            let mutex = std::sync::Mutex::new(input);
            let moved = mutex;
            assert(current(memory) <= LIVE);
            drop(moved);
            assert(current(memory) <= 0);
        }
    "#;
    // Mutex state and poison flag (9), Vec handle (24), two reserved slots
    // (16), and the single boxed payload (64).
    verifies("mutex_payload_live", &source.replace("LIVE", "113"));
    rejects("mutex_payload_short", &source.replace("LIVE", "112"), "memory budget exceeded");
}

#[test]
fn blocking_reacquisition_requires_the_previous_guard_to_be_released() {
    rejects(
        "mutex_acquisition_coverage",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(1u64);
            let held = m.lock();
            let guard = m.lock();
        }
    "#,
        "reentrant blocking acquisition",
    );
}

#[test]
fn native_mutex_surface_keeps_acquisition_outcomes_visible() {
    verifies(
        "mutex_native_surface",
        r#"
        fn f() {
            let mutex = std::sync::Mutex::new(1u64);
            match mutex.try_lock() {
                Ok(mut guard) => {
                    let view = &*guard;
                    let value = *view;
                    *guard = value;
                    drop(guard);
                },
                Err(std::sync::TryLockError::WouldBlock) => {},
                Err(std::sync::TryLockError::Poisoned(poison)) => { drop(poison); },
            };
        }
    "#,
    );
}

#[test]
fn native_specifications_do_not_assume_acquisition_succeeds() {
    rejects(
        "mutex_no_assumed_success",
        r#"
        fn f(mutex: &std::sync::Mutex<u64>) {
            let result = mutex.try_lock();
            assert(result matches Ok(_));
        }
    "#,
        "assertion failed",
    );
}

#[test]
fn lifetime_checks_cannot_be_bypassed_for_runtime_synchronization() {
    let error = crate::verify_one_file(
        "mutex_no_lifetime",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f(m: &std::sync::Mutex<u64>) resources peak(memory) <= 1000 {}
        }
    "#
        .into(),
        &["--no-lifetime"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error,
        "runtime synchronization memory analysis requires lifetime checking",
    );
}

#[test]
fn user_names_do_not_receive_standard_mutex_layouts() {
    verifies(
        "user_mutex_layout",
        r#"
        struct Mutex { byte: u8 }
        fn f() resources peak(memory) <= 1 {
            assert(value_size(Mutex) == 1);
            let m = Mutex { byte: 7 };
        }
    "#,
    );
}

#[test]
fn containing_a_guard_does_not_bypass_the_cleanup_boundary() {
    rejects(
        "guard_field_coverage",
        r#"
        struct Wrapper { guard: std::sync::MutexGuard<'static, u64> }
        fn f(w: Wrapper) resources peak(memory) <= 1000 {}
    "#,
        "before concurrent lifetime accounting is available",
    );
}

#[test]
fn opaque_guard_specification_preserves_rust_send_restriction() {
    let err = crate::verify_one_file(
        "guard_send",
        r#"
        use vstd::prelude::*;
        verus! {
            fn requires_send<T: Send>(value: T) {}
            fn invalid(guard: std::sync::MutexGuard<'static, u64>) {
                requires_send(guard);
            }
        }
    "#
        .into(),
        &[],
    )
    .unwrap_err();
    crate::common::assert_rust_error_msg(err, "cannot be sent between threads safely");
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
fn worker_uses_the_mutex_instance_carried_by_its_arc_capture() {
    let source = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(0u8));
            let alias = m.clone();
            let worker = std::thread::spawn(move || {
                let held = m.lock();
                SECOND
                drop(held);
            });
            let done = worker.join();
        }
    "#;
    rejects(
        "worker_lock_instance",
        &source.replace("SECOND", "drop(alias);"),
        "checked worker effects still require global",
    );
    rejects(
        "worker_lock_alias",
        &source.replace("SECOND", "let again = alias.lock();"),
        "reentrant blocking acquisition",
    );
}

#[test]
fn the_lock_contract_preserves_the_unwrap_precondition() {
    let source = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(1u8);
            let result = m.lock();
            CHECK
            let guard = result.unwrap();
            drop(guard);
        }
    "#;
    rejects(
        "checked_guard_extract",
        &source.replace("CHECK", "if result.is_err() { return; }"),
        "mutex intervals awaiting global",
    );
    let errors = crate::verify_one_file(
        "unchecked_guard_extract",
        format!("use vstd::prelude::*; verus! {{ {} }}", source.replace("CHECK", "")),
        &[],
    )
    .unwrap_err();
    assert!(
        errors.errors.iter().any(|d| d.message.contains("precondition")),
        "{:?}",
        errors.errors
    );
}

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
        ("guard_field_first", format!("{guard}, {scratch}"), 74),
        ("scratch_field_first", format!("{scratch}, {guard}"), 10),
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
            74,
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
