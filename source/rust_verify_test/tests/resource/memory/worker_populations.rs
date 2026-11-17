//! Population tests use executable spawn, transfer and join operations. Local
//! obligations must run without lifting the global concurrent proof boundary.

use super::support::rejects;

const GLOBAL: &str = "checked worker effects still require global lifetime and interference proofs";

#[test]
fn repeated_shared_results_preserve_the_coordinators_alias() {
    rejects(
        "repeated_worker_aliases",
        r#"
        fn f(n: u16) resources peak(memory) <= 512 {
            let shared = std::sync::Arc::new(7u64);
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let input = shared.clone();
                let handle = vstd::thread::spawn(move || input.clone());
                let result = handle.join().unwrap(); drop(result);
                i += 1;
            }
            let remaining = shared.clone(); drop(shared); drop(remaining);
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn extraction_checks_the_current_join_result_extent() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= LIMIT {
            let handle = std::thread::spawn(move || Vec::<u8>::with_capacity(64));
            let result = handle.join().unwrap(); drop(result);
        }
        }
    "#;
    let accepted =
        crate::verify_one_file("join_overlap", code.replace("LIMIT", "113"), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(accepted, GLOBAL);
    let rejected = crate::verify_one_file("join_overlap_short", code.replace("LIMIT", "112"), &[])
        .unwrap_err();
    crate::common::assert_vir_error_msgs(rejected, &["memory budget exceeded", GLOBAL]);
}

#[test]
fn repeated_constructions_bind_each_source_iteration() {
    rejects(
        "repeated_worker_inputs",
        r#"
        fn f(n: u16) resources peak(memory) <= n + 512 {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let worker = move || Vec::<u8>::with_capacity(i as usize);
                let handle = std::thread::spawn(worker);
                let result = handle.join().unwrap(); drop(result);
                i += 1;
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn repeated_workers_cannot_hide_body_allocations() {
    let error = crate::verify_one_file(
        "repeated_worker_hidden_allocation",
        r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= 128 {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let handle = std::thread::spawn(move || {
                    let extra = Box::new([0u8; 256]); drop(extra);
                });
                let result = handle.join().unwrap();
                i += 1;
            }
        }
        }
        "#
        .into(),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["memory budget exceeded", GLOBAL]);
}

#[test]
fn transferring_a_handle_cannot_hide_detach_in_its_receiver() {
    rejects(
        "captured_worker_detach",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let producer = std::thread::spawn(move || Box::new([0u8; 16]));
            let collector = std::thread::spawn(move || { drop(producer); });
            let result = collector.join();
        }
        "#,
        "detached workers",
    );
}

#[test]
fn nested_worker_loop_contexts_are_independent() {
    rejects(
        "nested_worker_loops",
        r#"
        fn f(n: u16) resources peak(memory) <= 2048 {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let outer = std::thread::spawn(move || {
                    let mut j = 0u16;
                    while j < i invariant j <= i, decreases i - j, {
                        let child = std::thread::spawn(move || Box::new([0u8; 16]));
                        let result = child.join().unwrap(); drop(result);
                        j += 1;
                    }
                });
                let result = outer.join().unwrap();
                i += 1;
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn captured_join_handle_transfers_completion_and_shared_responsibility() {
    rejects(
        "worker_handle_transfer",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let shared = std::sync::Arc::new(7u64);
            let alias = shared.clone();
            let producer = std::thread::spawn(move || shared.clone());
            let collector = std::thread::spawn(move || {
                let result = producer.join().unwrap();
                let another = result.clone(); drop(result); another
            });
            drop(alias);
            let result = collector.join().unwrap(); drop(result);
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn nested_captures_preserve_outer_inputs_and_shared_identity() {
    rejects(
        "nested_worker_captures",
        r#"
        fn f(n: u16) resources peak(memory) <= n + 1024 {
            let shared = std::sync::Arc::new(7u64);
            let outer = std::thread::spawn(move || {
                let alias = shared.clone();
                let child = std::thread::spawn(move || {
                    let scratch = Vec::<u8>::with_capacity(n as usize);
                    drop(scratch); alias
                });
                drop(shared);
                child.join().unwrap()
            });
            let result = outer.join().unwrap(); drop(result);
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn nested_workers_join_their_actual_children() {
    rejects(
        "nested_worker_results",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let outer = std::thread::spawn(move || {
                let child = std::thread::spawn(move || Box::new([0u8; 16]));
                let waiting = Box::new([0u8; 32]);
                let result = child.join().unwrap();
                drop(waiting); result
            });
            let result = outer.join().unwrap(); drop(result);
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn nested_construction_moves_the_actual_outer_capture() {
    rejects(
        "nested_worker_owned_capture",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let input = Box::new([0u8; 16]);
            let outer = std::thread::spawn(move || {
                let child = std::thread::spawn(move || input);
                child.join().unwrap()
            });
            let result = outer.join().unwrap(); drop(result);
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn nested_workers_cannot_discard_unjoined_descendants() {
    rejects(
        "nested_worker_detach",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let outer = std::thread::spawn(move || {
                let child = std::thread::spawn(move || Box::new([0u8; 16]));
                drop(child);
            });
            let result = outer.join();
        }
        "#,
        "detached workers",
    );
}
