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

#[test]
fn two_strong_aliases_update_one_persistent_protected_vector() {
    let program = r#"
        fn f() resources peak(memory) <= 1000 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 64]>>::with_capacity(1)));
            let alias = m.clone();
            let first = alias.lock();
            if first.is_err() { return; }
            let mut g = first.unwrap();
            g.push(Box::new([0u8; 64]));
            drop(g);
            drop(alias);
            let second = m.lock();
            if second.is_err() { return; }
            let mut h = second.unwrap();
            let popped = h.pop();
            drop(h);
            drop(m);
            assert(current(memory) <= LIMIT);
            drop(popped);
            assert(current(memory) <= 0);
        }
    "#;
    rejects(
        "protected_arc_aliases",
        &program.replace("LIMIT", "73"),
        "mutex intervals awaiting global",
    );
    let source = format!("use vstd::prelude::*; verus! {{ {} }}", program.replace("LIMIT", "72"));
    let err = crate::verify_one_file("protected_arc_popped_short", source, &[]).unwrap_err();
    crate::common::assert_any_vir_error_msg(err, "memory budget exceeded");
}

#[test]
fn a_worker_receiving_all_strong_handles_owns_the_protected_forest() {
    let source = r#"
        fn run() resources peak(memory) <= 2048 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 48]>>::new()));
            let peer = m.clone();
            let job = std::thread::spawn(move || {
                drop(peer);
                let r = m.lock();
                if r.is_err() { return; }
                let mut g = r.unwrap();
                g.push(Box::new([0u8; 48]));
                let removed = g.pop();
                drop(g);
                drop(m);
                assert(current(memory) <= LIMIT);
                drop(removed);
            });
            let done = job.join();
        }
    "#;
    // The worker still owns its capture environment. After dropping the mutex
    // the removed box must remain live independently through its Option.
    rejects(
        "all_handles_and_payload",
        &source.replace("LIMIT", "128"),
        "checked worker effects still require global",
    );
    let err = crate::verify_one_file(
        "all_handles_escaped_child",
        format!("use vstd::prelude::*; verus! {{ {} }}", source.replace("LIMIT", "47")),
        &[],
    )
    .unwrap_err();
    crate::common::assert_any_vir_error_msg(err, "memory budget exceeded");
}

#[test]
fn a_publisher_cannot_use_its_old_vector_snapshot_while_a_worker_can_observe_it() {
    let source = r#"
        fn run() resources peak(memory) <= 2048 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(Vec::<u8>::new()));
            let peer = m.clone();
            let job = std::thread::spawn(move || {
                let held = peer.lock();
                assert(current(memory) <= 128);
                drop(held);
            });
            JOIN_FIRST
            let r = m.lock();
            match r {
                Ok(mut g) => { g.push(1u8); },
                Err(poison) => { drop(poison); },
            }
            JOIN_LAST
        }
    "#;
    let join = "let done = job.join();";
    rejects(
        "observer_joined",
        &source.replace("JOIN_FIRST", join).replace("JOIN_LAST", ""),
        "checked worker effects still require global",
    );
    rejects(
        "observer_outstanding",
        &source.replace("JOIN_FIRST", "").replace("JOIN_LAST", join),
        "without a unique local protected payload",
    );
}
