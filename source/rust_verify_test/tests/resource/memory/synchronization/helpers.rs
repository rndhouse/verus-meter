//! Checked helper effects at their executable call sites.

use crate::verify_one_file;

/// Every reached function still awaits the global proof. Any additional
/// structural, Rust or byte-budget error makes the positive case fail.
fn check(name: &str, program: &str, expected: &str) {
    let err = verify_one_file(name, format!("use vstd::prelude::*; verus! {{ {program} }}"), &[])
        .unwrap_err();
    assert!(
        !err.errors.is_empty()
            && err.errors.iter().all(|d| d.code.is_none() && d.message.contains(expected)),
        "{:?}",
        err.errors
    );
}

const NESTED: &str = r#"
    type M = std::sync::Mutex<u8>;
    fn work(lock: &M) resources peak(memory) <= 128 {
        let guard = lock.lock();
        let scratch = Box::new([0u8; 32]);
        drop(scratch);
        drop(guard);
    }
    fn nested(first: &M, second: &M) resources peak(memory) <= 256 {
        let held = first.lock();
        work(second);
        drop(held);
    }
    fn caller() resources peak(memory) <= 512 {
        let a = M::new(0u8);
        let b = M::new(0u8);
        nested(&a, ACTUAL);
    }
"#;

#[test]
fn blocking_calls_require_distinct_instances_only_while_held() {
    check("different_locks", &NESTED.replace("ACTUAL", "&b"), "mutex intervals awaiting global");
    check("aliased_locks", &NESTED.replace("ACTUAL", "&a"), "reentrant blocking acquisition");
    let released =
        NESTED.replace("work(second);\n        drop(held);", "drop(held); work(second);");
    check("released_alias", &released.replace("ACTUAL", "&a"), "mutex intervals awaiting global");
}

#[test]
fn returning_and_consuming_a_guard_carries_the_actual_acquisition() {
    let program = r#"
        type M = std::sync::Mutex<u8>;
        type G<'a> = std::sync::MutexGuard<'a, u8>;
        fn acquire(m: &M) -> (r: std::sync::LockResult<G<'_>>) resources peak(memory) <= 32 {
            m.lock()
        }
        fn view(g: &G<'_>) resources peak(memory) <= 64 {
            let value = **g;
            let scratch = Box::new([0u8; 16]);
            drop(scratch);
        }
        fn pass<'a>(g: G<'a>) -> G<'a> resources peak(memory) <= 16 { g }
        fn release(g: G<'_>) resources peak(memory) <= 16 { drop(g); }
        fn run() resources peak(memory) <= 256 {
            let m = M::new(0u8);
            let r = acquire(&m);
            if r.is_err() { return; }
            let g = pass(r.unwrap());
            view(&g);
            ACTION
        }
    "#;
    check(
        "helper_release",
        &program.replace("ACTION", "release(g); let next = acquire(&m);"),
        "mutex intervals awaiting global",
    );
    check(
        "helper_guard_still_held",
        &program.replace("ACTION", "let next = acquire(&m); release(g);"),
        "reentrant blocking acquisition",
    );
}

#[test]
fn a_worker_instantiates_the_same_helper_on_its_captured_mutex() {
    let program = r#"
        fn nested(m: &std::sync::Mutex<u8>) resources peak(memory) <= 24 {
            let held = m.lock();
            drop(held);
        }
        fn caller() resources peak(memory) <= 512 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(0u8));
            let child = std::thread::spawn(move || {
                let before = m.lock();
                ACTION
            });
            let result = child.join();
        }
    "#;
    check(
        "worker_reentry",
        &program.replace("ACTION", "nested(&*m); drop(before);"),
        "reentrant blocking acquisition",
    );
    let source = program.replace("ACTION", "drop(before); nested(&*m);");
    let error = verify_one_file(
        "worker_helper",
        format!("use vstd::prelude::*; verus! {{ {source} }}"),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(
        error,
        &["mutex intervals awaiting global", "checked worker effects still require global"],
    );
}

#[test]
fn nested_try_lock_result_preserves_the_non_acquiring_alternative() {
    let program = r#"
        type M = std::sync::Mutex<u8>;
        fn attempt(m: &M) -> std::sync::TryLockResult<std::sync::MutexGuard<'_, u8>>
            resources peak(memory) <= 32 { m.try_lock() }
        fn caller() resources peak(memory) <= 256 {
            let m = M::new(0u8);
            let first = m.lock();
            let second = attempt(&m);
            drop(second);
            let third = m.lock();
            drop(first);
        }
    "#;
    check("failed_try_preserves_first_guard", program, "reentrant blocking acquisition");
}

#[test]
fn protected_replacement_through_a_helper_updates_the_shared_root() {
    let program = r#"
        type M = std::sync::Mutex<Box<[u8; 32]>>;
        fn replace(g: &mut std::sync::MutexGuard<'_, Box<[u8; 32]>>, fresh: Box<[u8; 32]>)
            resources peak(memory) <= 128 {
            **g = fresh;
        }
        fn run() resources peak(memory) <= 512 {
            let m = std::sync::Arc::new(M::new(Box::new([0u8; 32])));
            let alias = m.clone();
            let result = alias.lock();
            if result.is_err() { return; }
            let mut g = result.unwrap();
            replace(&mut g, Box::new([1u8; 32]));
            drop(g);
            drop(alias);
            drop(m);
            assert(current(memory) <= 0);
        }
    "#;
    check("shared_replacement", program, "mutex intervals awaiting global");
}

#[test]
fn an_implicit_parameter_drop_releases_the_guard_on_each_return() {
    check(
        "implicit_guard_release",
        r#"
        fn finish(g: std::sync::MutexGuard<'_, u8>, early: bool) resources peak(memory) <= 64 {
            if early { return; }
            let value = *g;
        }
        fn run(early: bool) resources peak(memory) <= 256 {
            let m = std::sync::Mutex::new(0u8);
            let r = m.lock();
            if r.is_err() { return; }
            finish(r.unwrap(), early);
            let next = m.lock();
        }
    "#,
        "mutex intervals awaiting global",
    );
}

#[test]
fn a_vector_helper_updates_the_length_used_after_reacquisition() {
    let source = r#"
        fn append(v: &mut Vec<Box<[u8; 32]>>, item: Box<[u8; 32]>) resources peak(memory) <= 128 {
            v.push(item);
        }
        fn run() resources peak(memory) <= 512 {
            let m = std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::with_capacity(1));
            let first = m.lock();
            if first.is_err() { return; }
            let mut g = first.unwrap();
            let view = &mut *g;
            let item = Box::new([0u8; 32]);
            append(view, item);
            drop(g);
            let next = m.lock();
            if next.is_err() { return; }
            let mut g = next.unwrap();
            let removed = g.pop();
            drop(g);
            drop(m);
            assert(current(memory) <= LIMIT);
            drop(removed);
        }
    "#;
    check("append_in_helper", &source.replace("LIMIT", "49"), "mutex intervals awaiting global");
    let errors = verify_one_file(
        "append_in_helper_short",
        format!("use vstd::prelude::*; verus! {{ {} }}", source.replace("LIMIT", "40")),
        &[],
    )
    .unwrap_err();
    crate::common::assert_any_vir_error_msg(errors, "memory budget exceeded");
}

#[test]
fn release_in_a_helper_observes_only_storage_still_live_at_the_call_site() {
    let source = r#"
        type M = std::sync::Mutex<u8>;
        fn work(m: &M) resources peak(memory) <= 128 {
            let g = m.lock();
            let scratch = Box::new([0u8; 32]);
            CLEANUP
        }
        fn caller() resources peak(memory) <= 256 {
            let m = M::new(0u8);
            let outside = [0u8; 19];
            work(&m);
        }
    "#;
    for (case, cleanup, bytes) in [
        ("scratch_ends_before_release", "drop(scratch); drop(g);", 37),
        ("scratch_ends_after_release", "drop(g); drop(scratch);", 77),
    ] {
        let errors = verify_one_file(
            case,
            format!("use vstd::prelude::*; verus! {{ {} }}", source.replace("CLEANUP", cleanup)),
            &["--trace"],
        )
        .unwrap_err();
        assert!(
            errors.errors.iter().all(|e| e.message.contains("mutex intervals awaiting global")),
            "{:?}",
            errors.errors
        );
        let expected = format!("memory at mutex release: {bytes} live bytes");
        assert!(
            errors.notes.iter().any(|n| n.message == expected
                && n.spans.iter().flat_map(|s| &s.text).any(|t| t.text.contains("work(&m)"))),
            "{:?}",
            errors.notes
        );
    }
}

#[test]
fn independent_payload_descriptions_cannot_update_two_aliases() {
    let program = r#"
        type M = std::sync::Mutex<Box<[u8; 32]>>;
        type G<'a> = std::sync::MutexGuard<'a, Box<[u8; 32]>>;
        fn change(g: &mut G<'_>, observer: &M, fresh: Box<[u8; 32]>) resources peak(memory) <= 128 {
            let attempt = observer.try_lock();
            drop(attempt);
            **g = fresh;
        }
        fn wrapper(g: &mut G<'_>, observer: &M, fresh: Box<[u8; 32]>) resources peak(memory) <= 256 {
            change(g, observer, fresh);
        }
        fn caller() resources peak(memory) <= 768 {
            let m = M::new(Box::new([0u8; 32]));
            let other = M::new(Box::new([1u8; 32]));
            let result = m.lock();
            if result.is_err() { return; }
            let mut g = result.unwrap();
            wrapper(&mut g, ACTUAL, Box::new([2u8; 32]));
        }
    "#;
    check("two_payloads", &program.replace("ACTUAL", "&other"), "mutex intervals awaiting global");
    check("same_payload", &program.replace("ACTUAL", "&m"), "aliased protected payloads");
}

#[test]
fn a_guard_parameter_carries_the_protected_vector_forest() {
    let source = r#"
        type G<'a> = std::sync::MutexGuard<'a, Vec<Box<[u8; 32]>>>;
        fn insert(g: &mut G<'_>, item: Box<[u8; 32]>) resources peak(memory) <= 128 {
            g.push(item);
        }
        fn run() resources peak(memory) <= 512 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));
            let alias = m.clone();
            let result = alias.lock();
            if result.is_err() { return; }
            let mut guard = result.unwrap();
            let item = Box::new([1u8; 32]);
            insert(&mut guard, item);
            let removed = guard.pop();
            drop(guard);
            drop(alias);
            drop(m);
            assert(current(memory) <= LIMIT);
            drop(removed);
        }
    "#;
    check(
        "protected_formal_vec",
        &source.replace("LIMIT", "41"),
        "mutex intervals awaiting global",
    );
    let errors = verify_one_file(
        "protected_formal_vec_short",
        format!("use vstd::prelude::*; verus! {{ {} }}", source.replace("LIMIT", "40")),
        &[],
    )
    .unwrap_err();
    crate::common::assert_any_vir_error_msg(errors, "memory budget exceeded");
}

#[test]
fn a_helper_borrowing_an_arc_receives_the_same_instance_as_its_owner() {
    let program = r#"
        type A = std::sync::Arc<std::sync::Mutex<u8>>;
        fn work(m: &A) resources peak(memory) <= 48 { let held = m.lock(); }
        fn run() resources peak(memory) <= 256 {
            let m = A::new(std::sync::Mutex::new(0u8));
            let peer = m.clone();
            let first = m.lock();
            ACTION
        }
    "#;
    check(
        "borrowed_arc",
        &program.replace("ACTION", "drop(first); work(&peer);"),
        "mutex intervals awaiting global",
    );
    check(
        "borrowed_arc_alias",
        &program.replace("ACTION", "work(&peer); drop(first);"),
        "reentrant blocking acquisition",
    );
}

#[test]
fn repeated_helper_calls_release_each_visits_guard() {
    check(
        "repeated_calls",
        r#"
        fn work(m: &std::sync::Mutex<u8>) resources peak(memory) <= 64 {
            let held = m.lock();
            let scratch = Box::new([0u8; 16]);
        }
        fn run(n: usize, stop: bool) resources peak(memory) <= 256 {
            let m = std::sync::Mutex::new(0u8);
            let mut i: usize = 0;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                work(&m);
                if stop { return; }
                i = i + 1;
            }
            work(&m);
        }
    "#,
        "mutex intervals awaiting global",
    );
}

#[test]
fn an_outer_mutex_does_not_supply_an_interface_for_an_embedded_guard() {
    super::rejects(
        "nested_input_guard",
        r#"
        fn consume(m: std::sync::Mutex<std::sync::MutexGuard<'static, u8>>)
            resources peak(memory) <= 1024 { drop(m); }
    "#,
        "runtime synchronization values before concurrent lifetime accounting",
    );
}
