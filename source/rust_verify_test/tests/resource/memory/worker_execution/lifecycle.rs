//! Source regressions for the boundaries between the publisher, the worker
//! body and the caller that receives its result.

use super::{GLOBAL, rejects};
use crate::common::{assert_rust_error_msg, assert_vir_error_msg, assert_vir_error_msgs};
use crate::verify_one_file;

#[test]
fn relayed_join_keeps_the_same_mutex_allocation() {
    // Both mutexes have the same layout. What distinguishes the two cases is
    // which Arc was cloned before the worker took ownership of both handles.
    let program = r#"
        use vstd::prelude::*;
        verus! {
        fn run(left: std::sync::Mutex<u64>, right: std::sync::Mutex<u64>)
            resources peak(memory) <= 1024
        {
            let a = std::sync::Arc::new(left);
            let b = std::sync::Arc::new(right);
            let survivor = SURVIVOR.clone();
            let worker = std::thread::spawn(move || { drop(b); a });
            let relay = vstd::thread::spawn(move || worker.join().unwrap());
            let result = relay.join().unwrap();
            assert(current(memory) <= BOUND);
            drop(survivor);
            drop(result);
            assert(current(memory) <= 0);
        }
        }
    "#;
    // Two 8-byte handles remain. Each distinct backing adds a 16-byte Arc
    // control block and a 17-byte mutex containing the u64.
    for (name, survivor, bound, shortfall) in [
        ("same_mutex", "a", 49, None),
        ("same_mutex_short", "a", 48, Some("live 49 bytes exceeds bound 48 bytes")),
        ("distinct_mutexes", "b", 82, None),
        ("wrong_mutex", "b", 49, Some("live 82 bytes exceeds bound 49 bytes")),
    ] {
        let source = program.replace("SURVIVOR", survivor).replace("BOUND", &bound.to_string());
        let error = verify_one_file(name, source, &[]).unwrap_err();
        if let Some(shortfall) = shortfall {
            assert_vir_error_msgs(error, &[shortfall, GLOBAL]);
        } else {
            assert_vir_error_msg(error, GLOBAL);
        }
    }
}

#[test]
fn both_spawn_apis_require_the_workers_precondition() {
    for api in ["std", "vstd"] {
        let program = format!(
            r#"
            use vstd::prelude::*;
            verus! {{
            fn caller(n: u8) requires n > 0, resources peak(memory) <= 128 {{
                let handle = {api}::thread::spawn(move || {{
                    requires(n > 0);
                    n - 1
                }});
                let result = handle.join().unwrap();
            }}
            }}
            "#
        );
        verify_one_file(api, program.clone(), &[]).unwrap();
        let unchecked = program.replace("requires n > 0,", "");
        let error = verify_one_file(&format!("{api}_unchecked"), unchecked, &[]).unwrap_err();
        assert_vir_error_msg(error, "precondition not satisfied");
    }
}

#[test]
fn vstd_spawn_requires_a_sync_payload_in_a_shared_handle() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
        fn caller(input: std::sync::Arc<std::cell::Cell<u64>>) resources peak(memory) <= 1024 {
            let worker = vstd::thread::spawn(move || drop(input));
            let result = worker.join();
        }
        }
    "#;
    let error = verify_one_file("non_sync_payload", source.into(), &[]).unwrap_err();
    assert_rust_error_msg(error, "cannot be shared between threads safely");
}

#[test]
fn consuming_a_capture_does_not_admit_a_non_move_worker() {
    // Rust can infer a by-value capture for this closure. The supported
    // worker domain requires an explicit move closure.
    rejects(
        "non_move_worker",
        r#"
        fn caller() resources peak(memory) <= 1024 {
            let buffer = Vec::<u8>::with_capacity(19);
            let worker = std::thread::spawn(|| drop(buffer));
            worker.join().unwrap();
        }
        "#,
        "scoped or non-move worker captures",
    );
}

#[test]
fn a_functional_specification_cannot_hide_an_allocation_in_a_worker() {
    rejects(
        "opaque_worker_helper",
        r#"
        #[verifier::external_body]
        fn opaque() ensures true {
            let buffer = Vec::<u8>::with_capacity(1024); drop(buffer);
        }
        fn run() resources peak(memory) <= 128 {
            let job = std::thread::spawn(move || { opaque(); });
            let result = job.join();
        }
        "#,
        "calls without a current-model memory contract",
    );
}

#[test]
fn excluded_concurrency_operations_in_a_worker_fail_at_their_source() {
    for (name, operation, message) in [
        (
            "channel",
            "let (tx, rx) = std::sync::mpsc::channel::<u8>(); drop(tx); drop(rx);",
            "mpsc::channel` is not supported",
        ),
        (
            "condition_variable",
            "let c = std::sync::Condvar::new(); c.notify_one();",
            "Condvar` is not supported",
        ),
        (
            "barrier",
            "let b = std::sync::Barrier::new(1); let r = b.wait();",
            "Barrier` is not supported",
        ),
        (
            "scoped",
            "std::thread::scope(|s| { let h = s.spawn(|| {}); let r = h.join(); });",
            "scope` is not supported",
        ),
        (
            "relaxed_atomic",
            "let a = std::sync::atomic::AtomicUsize::new(1); let n = a.load(std::sync::atomic::Ordering::Relaxed);",
            "struct layouts outside this crate",
        ),
        ("unwind", "let r = std::panic::catch_unwind(|| {});", "std::panic::UnwindSafe"),
        (
            "async_worker",
            "let f = async { let v = Vec::<u8>::new(); drop(v); }; drop(f);",
            "coroutine types",
        ),
    ] {
        let source = format!(
            "use vstd::prelude::*; verus! {{
            fn run() resources peak(memory) <= 512 {{
                let job = std::thread::spawn(move || {{ {operation} }});
                let r = job.join();
            }}
        }}"
        );
        let error = verify_one_file(name, source, &[]).unwrap_err();
        assert!(
            error.errors.iter().any(|e| e.message.contains(message)
                && e.spans.iter().any(|s| s.text.iter().any(|line| line.text.contains(operation)))),
            "{name}: {:?}",
            error.errors
        );
    }
}
