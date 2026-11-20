//! The protected owner tree, including transferred and replaced allocations.

use super::{rejects, verifies};

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
fn protected_vector_slots_and_popped_payload_have_separate_lifetimes() {
    let program = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(Vec::<Box<[u8; 64]>>::with_capacity(1));
            let result = m.lock();
            if result.is_err() { return; }
            let mut guard = result.unwrap();
            guard.push(Box::new([0u8; 64]));
            guard.push(Box::new([0u8; 64]));
            let popped = guard.pop();
            drop(guard);
            drop(m);
            assert(current(memory) <= LIVE);
            drop(popped);
            assert(current(memory) <= 0);
        }
    "#;
    // The Option tag and handle (9) plus the removed Box payload (64).
    rejects(
        "popped_past_unlock",
        &program.replace("LIVE", "73"),
        "mutex intervals awaiting global",
    );
    let errors = crate::verify_one_file(
        "popped_short",
        format!("use vstd::prelude::*; verus! {{ {} }}", program.replace("LIVE", "72")),
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
fn borrowed_payload_uses_the_same_guard_and_vector_storage() {
    let program = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Mutex::new(Vec::<Box<[u8; 64]>>::new());
            let result = m.lock();
            if result.is_err() { return; }
            let mut guard = result.unwrap();
            let view = &mut *guard;
            view.push(Box::new([0u8; 64]));
            let item = view.pop();
            drop(guard);
            drop(m);
            assert(current(memory) <= 81);
            drop(item);
        }
    "#;
    rejects("borrowed_payload", program, "mutex intervals awaiting global");
}

#[test]
fn replacing_the_protected_box_keeps_the_old_box_live_through_construction() {
    let program = r#"
        fn f() resources peak(memory) <= LIMIT {
            let m = std::sync::Mutex::new(Box::new([0u8; 64]));
            let result = m.lock();
            if result.is_err() { return; }
            let mut guard = result.unwrap();
            *guard = Box::new([1u8; 64]);
            drop(guard);
            drop(m);
            assert(current(memory) <= 0);
        }
    "#;
    rejects(
        "protected_replacement",
        &program.replace("LIMIT", "1000"),
        "mutex intervals awaiting global",
    );
    let errors = crate::verify_one_file(
        "protected_replacement_short",
        format!("use vstd::prelude::*; verus! {{ {} }}", program.replace("LIMIT", "135")),
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
fn a_worker_cannot_treat_shared_vector_geometry_as_actor_local() {
    rejects(
        "shared_guarded_vector_requires_an_interference_summary",
        r#"
        fn f() resources peak(memory) <= 2000 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(Vec::<u8>::new()));
            let peer = std::sync::Arc::clone(&m);
            let child = std::thread::spawn(move || {
                let result = peer.lock();
                if result.is_err() { return; }
                let mut guard = result.unwrap();
                guard.push(1u8);
            });
            let done = child.join();
            drop(m);
        }
    "#,
        "without a unique local protected payload",
    );
}
