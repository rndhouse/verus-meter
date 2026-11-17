//! Source-driven worker proofs. The global rejection must remain even when all
//! generated local obligations verify; deliberately short bounds must also fail
//! at the actual executable allocation, independently of that rejection.

use super::support::rejects;

const GLOBAL: &str = "checked worker effects still require global lifetime and interference proofs";

#[test]
fn outgoing_sizes_use_construction_values_after_parent_mutation() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 512 {
                let mut count = 16usize;
                let worker = move || Vec::<u8>::with_capacity(count);
                count = 128;
                let handle = std::thread::spawn(worker);
                let result = handle.join().unwrap();
                assert(current(memory) <= LIMIT);
                drop(result);
            }
        }
    "#;
    let correct =
        crate::verify_one_file("worker_construction_output", code.replace("LIMIT", "56"), &[])
            .unwrap_err();
    crate::common::assert_vir_error_msg(correct, GLOBAL);
    let short = crate::verify_one_file(
        "worker_construction_output_short",
        code.replace("LIMIT", "55"),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(short, &["conditional memory budget exceeded", GLOBAL]);
}

#[test]
fn returned_runtime_children_use_the_common_ownership_template() {
    rejects(
        "worker_owned_result",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let handle = std::thread::spawn(move || {
                ensures(|r: Vec<Box<u8>>| r.len() == 1);
                let mut result = Vec::<Box<u8>>::with_capacity(2);
                result.push(Box::new(7u8)); result
            });
            let mut result = handle.join().unwrap();
            result.push(Box::new(9u8)); drop(result);
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn native_worker_body_is_checked_before_the_global_boundary() {
    rejects(
        "checked_native_worker",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let input = Box::new([0u8; 16]);
            let worker = move || { let scratch = Box::new([0u8; 32]); drop(scratch); input };
            let handle = std::thread::spawn(worker);
            let result = handle.join();
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn borrowed_body_cleanup_keeps_its_scalar_result() {
    rejects(
        "checked_borrowed_worker",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let shared = std::sync::Arc::new(7u64);
            let handle = std::thread::spawn(move || *shared);
            let result = handle.join();
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn worker_allocation_emits_a_real_byte_obligation() {
    let error = crate::verify_one_file(
        "checked_worker_short_bound",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 128 {
                let handle = std::thread::spawn(move || {
                    let scratch = Box::new([0u8; 256]); drop(scratch);
                });
                let result = handle.join();
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
fn both_join_apis_preserve_verified_payload_postconditions() {
    for spawn in ["std::thread::spawn", "vstd::thread::spawn"] {
        rejects(
            &format!("worker_join_{}", spawn.replace("::", "_")),
            &format!(
                r#"
            fn f() resources peak(memory) <= 1024 {{
                let handle = {spawn}(move || {{ ensures(|r: u64| r == 7); 7u64 }});
                let result = handle.join();
                assert(result is Ok);
                match result {{ Ok(value) => {{ assert(value == 7); }}, Err(_) => {{ assert(false); }} }}
            }}
        "#
            ),
            GLOBAL,
        );
    }
}

#[test]
fn worker_helper_returns_owned_storage_through_unwrap() {
    rejects(
        "worker_helper_return",
        r#"
        fn helper(input: Box<[u8; 16]>) -> Box<[u8; 16]>
            resources peak(memory) <= 128,
        { let temporary = Box::new([0u8; 32]); drop(temporary); input }
        fn f() resources peak(memory) <= 1024 {
            let input = Box::new([0u8; 16]);
            let worker = move || helper(input);
            let handle = std::thread::spawn(worker);
            let waiting = Box::new([0u8; 48]);
            let result = handle.join().unwrap();
            drop(waiting); drop(result);
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn shared_return_keeps_its_backing_after_the_environment_drops() {
    rejects(
        "worker_shared_return",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let shared = std::sync::Arc::new([0u8; 16]);
            let worker = move || shared.clone();
            let handle = std::thread::spawn(worker);
            let result = handle.join().unwrap();
            let alias = result.clone();
            drop(result); drop(alias);
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn symbolic_worker_loops_use_captured_inputs() {
    rejects(
        "worker_symbolic_loop",
        r#"
        fn f(n: u16) resources peak(memory) <= 4096 {
            let worker = move || {
                let mut i = 0u16;
                while i < n invariant i <= n, decreases n - i, {
                    let scratch = Vec::<u8>::with_capacity(16);
                    drop(scratch); i += 1;
                }
            };
            let handle = std::thread::spawn(worker);
            let result = handle.join();
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn conditional_allocations_and_early_returns_preserve_capture_cleanup() {
    rejects(
        "worker_early_return",
        r#"
        fn f(flag: bool) resources peak(memory) <= 1024 {
            let input = Box::new([0u8; 16]);
            let handle = std::thread::spawn(move || {
                if flag { let scratch = Box::new([0u8; 32]); drop(scratch); return input; }
                let scratch = Box::new([0u8; 64]); drop(scratch); input
            });
            let result = handle.join().unwrap(); drop(result);
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn aggregate_captures_and_delayed_copies_keep_construction_inputs() {
    rejects(
        "worker_aggregate_capture",
        r#"
        #[derive(Copy, Clone)]
        struct Input { count: u16, other: u16 }
        fn f() resources peak(memory) <= 1024 {
            let mut input = Input { count: 12, other: 7 };
            let worker = move || {
                let saved = input;
                let count = saved.count;
                let scratch = Vec::<u8>::with_capacity(count as usize);
                drop(scratch); saved.other
            };
            input.count = 200;
            let copied = worker;
            let first = std::thread::spawn(worker);
            let second = std::thread::spawn(copied);
            let a = first.join().unwrap(); let b = second.join().unwrap();
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn captured_and_returned_vector_keeps_allocation_metadata() {
    rejects(
        "worker_vector_return",
        r#"
        fn f(n: u16) resources peak(memory) <= n + 256 {
            let input = Vec::<u8>::with_capacity(n as usize);
            let handle = std::thread::spawn(move || input);
            let result = handle.join().unwrap(); drop(result);
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn worker_local_symbolic_return_has_a_checked_outgoing_descriptor() {
    rejects(
        "worker_new_vector_return",
        r#"
        fn f(n: u16) resources peak(memory) <= n + 256 {
            let handle = std::thread::spawn(move || Vec::<u8>::with_capacity(n as usize));
            let result = handle.join().unwrap(); drop(result);
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn failed_worker_correctness_cannot_establish_join_success() {
    let error = crate::verify_one_file(
        "worker_unproved_panic_freedom",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f(n: u64) resources peak(memory) <= 1024 {
                let handle = std::thread::spawn(move || n + 1);
                let result = handle.join().unwrap();
            }
        }
    "#
        .into(),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(
        error,
        &["possible arithmetic underflow/overflow", GLOBAL],
    );
}

#[test]
fn ordinary_result_cannot_fabricate_a_success_witness() {
    rejects(
        "worker_unknown_result_input",
        r#"
        fn f(unrelated: Result<u64, Box<u8>>) resources peak(memory) <= 1024 {
            let handle = std::thread::spawn(move || 1u64);
            let joined = handle.join(); drop(unrelated);
        }
    "#,
        "primitive Result inputs without checked outcome provenance",
    );
    rejects(
        "worker_foreign_result",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let handle = std::thread::spawn(move || 1u64);
            let joined = handle.join();
            let unrelated: Result<u64, u64> = Err(7);
            let result = unrelated.unwrap();
        }
    "#,
        "does not support struct layouts outside this crate",
    );
}

#[test]
fn dropping_a_live_handle_is_rejected() {
    rejects(
        "worker_detached_body",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let handle = std::thread::spawn(move || Box::new([0u8; 16]));
            drop(handle);
        }
    "#,
        "detached workers",
    );
}

#[test]
fn incomplete_global_proof_blocks_no_verify_and_compilation() {
    let directory = tempfile::tempdir().unwrap();
    let artifact = directory.path().join("incomplete.vir");
    let export = format!("--export={}", artifact.display());
    for option in ["--no-verify", "--compile"] {
        let error = crate::verify_one_file(
            &format!("worker_boundary_{option}"),
            r#"
            use vstd::prelude::*;
            verus! {
                fn f() resources peak(memory) <= 1024 {
                    let handle = std::thread::spawn(move || 1u64);
                    let result = handle.join().unwrap();
                }
            }
        "#
            .into(),
            &[option, &export],
        )
        .unwrap_err();
        crate::common::assert_vir_error_msg(error, GLOBAL);
        assert!(!artifact.exists(), "incomplete worker contracts must not be exported");
    }
}

#[test]
fn captured_vector_mutation_uses_a_separate_worker_proof_frame() {
    rejects(
        "worker_capture_mutation",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let input = Vec::<u8>::with_capacity(8);
            let handle = std::thread::spawn(move || {
                ensures(|r: Vec<u8>| r.len() == 1);
                let mut local = input; local.push(7u8); local
            });
            let mut result = handle.join().unwrap(); result.push(9u8); drop(result);
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn worker_helpers_and_loops_can_consume_runtime_owned_children() {
    rejects(
        "worker_owned_children",
        r#"
        fn helper() -> Vec<Box<u8>> resources peak(memory) <= 128 {
            let mut result = Vec::<Box<u8>>::with_capacity(2);
            result.push(Box::new(7u8)); result
        }
        fn f() resources peak(memory) <= 1024 {
            let handle = std::thread::spawn(move || {
                let children = helper(); drop(children);
                let mut i = 0u16;
                while i < 2 invariant i <= 2, decreases 2 - i, {
                    let mut scratch = Vec::<Box<u8>>::with_capacity(1);
                    scratch.push(Box::new(9u8)); drop(scratch); i += 1;
                }
            });
            let result = handle.join().unwrap();
        }
    "#,
        GLOBAL,
    );
}

#[test]
fn returned_storage_stays_charged_while_the_caller_allocates() {
    let error = crate::verify_one_file(
        "worker_return_overlap",
        r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 128 {
                let handle = std::thread::spawn(move || Box::new([0u8; 64]));
                let result = handle.join().unwrap();
                let waiting = Box::new([0u8; 64]);
                drop(waiting); drop(result);
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
fn shared_returns_preserve_the_actual_backing_instance() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
            fn f() resources peak(memory) <= 1024 {
                let first = std::sync::Arc::new(Vec::<u8>::with_capacity(16));
                let other = std::sync::Arc::new(Vec::<u8>::with_capacity(80));
                let handle = std::thread::spawn(move || first.clone());
                drop(other);
                let result = handle.join().unwrap();
                assert(current(memory) <= 63);
                drop(result);
            }
        }
    "#;
    let correct =
        crate::verify_one_file("worker_backing_identity", code.replace("<= 63", "<= 64"), &[])
            .unwrap_err();
    crate::common::assert_vir_error_msg(correct, GLOBAL);
    let error =
        crate::verify_one_file("worker_backing_identity_short", code.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}

#[test]
fn siblings_retain_shared_backing_through_a_transferred_join_handle() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 2048 {
            let inner = std::sync::Arc::new(Vec::<u8>::with_capacity(64));
            let peer = inner.clone();
            let left = std::thread::spawn(move || std::sync::Arc::new(inner));
            let right = std::thread::spawn(move || peer);
            let collector = std::thread::spawn(move || left.join().unwrap());
            let nested = collector.join().unwrap();
            drop(nested);
            let survivor = right.join().unwrap();
            assert(current(memory) <= 112);
            drop(survivor);
            assert(current(memory) <= 0);
        }
        }
    "#;
    let valid = crate::verify_one_file("sibling_shared_backing", code.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let short = code.replace("<= 112", "<= 111");
    let error = crate::verify_one_file("sibling_shared_backing_short", short, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}
