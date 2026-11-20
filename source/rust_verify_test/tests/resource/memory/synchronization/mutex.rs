//! Native acquisition outcomes and mutex identities on local and worker paths.

use super::rejects;

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

#[test]
fn native_result_arms_transfer_only_the_guard_they_own() {
    let source = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            match m.try_lock() {
                Ok(guard) => { OK drop(guard); }
                Err(std::sync::TryLockError::Poisoned(poison)) => { POISON drop(poison); }
                Err(std::sync::TryLockError::WouldBlock) => { let later = m.lock(); drop(later); }
            };
        }
    "#;
    for (case, ok, poison, expected) in [
        ("would_block_holds_nothing", "", "", "mutex intervals awaiting global"),
        ("success_holds_guard", "let again = m.lock();", "", "reentrant blocking acquisition"),
        ("poison_holds_guard", "", "let again = m.lock();", "reentrant blocking acquisition"),
    ] {
        rejects(case, &source.replace("OK", ok).replace("POISON", poison), expected);
    }
}

#[test]
fn a_blocking_lock_keeps_its_acquisition_in_the_error_arm() {
    rejects(
        "poisoned_blocking_lock",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(0u8);
            match m.lock() {
                Ok(guard) => { drop(guard); }
                Err(poison) => { let again = m.lock(); drop(poison); }
            };
        }
    "#,
        "reentrant blocking acquisition",
    );
}

#[test]
fn a_stored_borrow_preserves_its_mutex_instance() {
    let program = r#"
        fn f() resources peak(memory) <= 1000 {
            let a = std::sync::Mutex::new(0u8);
            let b = std::sync::Mutex::new(0u8);
            let alias = &a;
            let first = alias.lock();
            let second = TARGET.lock();
            drop(second);
            drop(first);
        }
    "#;
    rejects(
        "borrow_of_same_mutex",
        &program.replace("TARGET", "a"),
        "reentrant blocking acquisition",
    );
    rejects(
        "borrow_and_distinct_mutex",
        &program.replace("TARGET", "b"),
        "mutex intervals awaiting global",
    );
}

#[test]
fn a_reassigned_reference_cannot_claim_its_former_mutex_identity() {
    rejects(
        "mutable_mutex_receiver",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let a = std::sync::Mutex::new(0u8);
            let b = std::sync::Mutex::new(0u8);
            let mut view = &a;
            view = &b;
            let held = b.lock();
            let again = view.lock();
        }
    "#,
        "without a checked mutex instance",
    );
}
