//! Native thread/shared-storage surface and executable compiler evidence.
use super::support::{rejects, verifies};

#[test]
fn shared_and_worker_handles_have_source_sizes() {
    verifies(
        "concurrent_sizes",
        r#"
        fn sizes() resources peak(memory) <= 0 {
            assert(value_size(std::sync::Arc<u64>) == 8);
            assert(value_size(std::sync::Arc<std::sync::Mutex<u64>>) == 8);
            assert(value_size(std::thread::JoinHandle<u64>) == 8);
            assert(value_size(vstd::thread::JoinHandle<u64>) == 8);
            assert(value_size(std::thread::Result<u64>) == 17);
            assert(value_size(Ghost<std::sync::Arc<u64>>) == 0);
            assert(value_size(Tracked<u64>) == 0);
        }
    "#,
    );
}

#[test]
fn logical_identity_erasure_preserves_only_executable_arc_clones() {
    let error = crate::verify_one_file(
        "arc_clone_erasure",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 1000 {
                let root = std::sync::Arc::new(7u64);
                proof { let ghost_copy = root.clone(); }
                let copy = root.clone();
                drop(copy);
                drop(root);
            }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error.clone(),
        "before concurrent lifetime accounting is available",
    );
    assert_eq!(
        error
            .notes
            .iter()
            .filter(|note| note.message.contains("memory executable effect: ArcClone"))
            .count(),
        1
    );
}

#[test]
fn native_threads_retain_functional_worker_postconditions() {
    verifies(
        "native_thread_postconditions",
        r#"
        fn f() {
            let value = 7u64;
            let handle = std::thread::spawn(move || {
                ensures(|result: u64| result == value);
                value
            });
            match handle.join() {
                Ok(result) => { assert(result == value); },
                Err(error) => { drop(error); },
            }
        }
    "#,
    );
}

#[test]
fn join_success_is_not_assumed_from_functional_specifications() {
    rejects(
        "native_join_no_assumed_success",
        r#"
        fn f() {
            let handle = std::thread::spawn(move || 7u64);
            let result = handle.join();
            assert(result matches Ok(_));
        }
    "#,
        "assertion failed",
    );
}

#[test]
fn worker_capture_bridge_runs_before_the_global_memory_gate() {
    rejects(
        "worker_capture_bridge",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let shared = std::sync::Arc::new(7u64);
            let copy = shared.clone();
            let handle = std::thread::spawn(move || *copy);
            let result = handle.join();
            drop(result);
        }
    "#,
        "before concurrent lifetime accounting is available",
    );
}

#[test]
fn proof_only_uses_do_not_make_runtime_worker_captures() {
    let error = crate::verify_one_file(
        "worker_proof_capture_bridge",
        r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 1000 {
            let value = 7u64;
            let tracked token = 8u64;
            let handle = vstd::thread::spawn(move || {
                proof { assert(value == 7); assert(token == 8); }
                0u8
            });
            let result = handle.join();
            drop(result);
        }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error.clone(),
        "before concurrent lifetime accounting is available",
    );
    assert!(error.notes.iter().any(|note| {
        note.message.contains("memory closure captures: 0 executable fields, 0 inline source bytes")
    }));
}

#[test]
fn worker_dependencies_participate_in_recursion_checks() {
    rejects(
        "worker_recursive_dependency",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let handle = std::thread::spawn(move || f());
            let result = handle.join();
            drop(result);
        }
    "#,
        "recursive memory contracts",
    );
}

#[test]
fn nested_worker_dependencies_participate_in_recursion_checks() {
    rejects(
        "nested_worker_recursive_dependency",
        r#"
        fn f() resources peak(memory) <= 1000 {
            let handle = vstd::thread::spawn(move || {
                let child = std::thread::spawn(move || f());
                let result = child.join();
                drop(result);
            });
            let result = handle.join();
            drop(result);
        }
    "#,
        "recursive memory contracts",
    );
}

#[test]
fn moved_owners_and_copied_scalars_have_executable_capture_storage() {
    let error = crate::verify_one_file(
        "worker_mixed_capture_storage",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 1000 {
                let owner = Box::new([0u8; 16]);
                let shared = std::sync::Arc::new(7u64);
                let count = 2u16;
                let tracked token = 8u64;
                let handle = std::thread::spawn(move || {
                    proof { assert(token == 8); }
                    drop(owner);
                    *shared + count as u64
                });
                let result = handle.join();
                drop(result);
            }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error.clone(),
        "before concurrent lifetime accounting is available",
    );
    assert!(error.notes.iter().any(|note| {
        note.message
            .contains("memory closure captures: 3 executable fields, 18 inline source bytes")
    }));
}

#[test]
fn native_spawn_preserves_rust_send_checks() {
    let error = crate::verify_one_file(
        "worker_requires_send",
        r#"
        use vstd::prelude::*;
        verus! {
        fn f() {
            let value = std::rc::Rc::new(7u64);
            let handle = std::thread::spawn(move || *value);
            let result = handle.join();
            drop(result);
        }
        }
    "#
        .into(),
        &[],
    )
    .unwrap_err();
    crate::common::assert_rust_error_msg(error, "cannot be sent between threads safely");
}

#[test]
fn nested_logical_identity_clones_preserve_every_executable_operation() {
    let error = crate::verify_one_file(
        "nested_arc_clone_erasure",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 1000 {
                let root = std::sync::Arc::new(7u64);
                let copy = root.clone().clone();
                drop(copy);
                drop(root);
            }
        }
    "#
        .into(),
        &["--trace"],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error.clone(),
        "before concurrent lifetime accounting is available",
    );
    assert_eq!(
        error
            .notes
            .iter()
            .filter(|note| { note.message.contains("memory executable effect: ArcClone") })
            .count(),
        2,
    );
}
