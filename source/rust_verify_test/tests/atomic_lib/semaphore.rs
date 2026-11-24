//! Memory contracts on callers of the verified vstd semaphore.
use super::*;

const SOURCE: &str = include_str!("semaphore.verus.rs");

#[test]
fn verified_permit_follows_its_input_across_a_conditional_return() {
    let trace =
        verify_one_file("metered_permit", SOURCE.into(), &["--trace", "--no-cheating"]).unwrap();
    for message in [
        "73-byte allocation only observed within intact holder input 0",
        "74-byte allocation also observed outside intact holder input 0",
        "dynamic storage region only observed within intact holder input 0",
    ] {
        assert!(
            trace.notes.iter().any(|note| note.message == message),
            "missing observation {expected}",
            expected = message
        );
    }
}

#[test]
fn imported_semaphore_operations_require_their_measured_workspace() {
    for (name, peak) in [("create", 40), ("attempt", 81), ("wait", 98), ("release", 72)] {
        let short = peak - 1;
        let source = SOURCE
            .replace(&format!("peak(memory) <= {peak},"), &format!("peak(memory) <= {short},"));
        let error = verify_one_file(&format!("short_permit_{name}"), source, &["--no-cheating"])
            .unwrap_err();
        assert_vir_error_msg(error, &format!("peak {peak} bytes exceeds budget {short} bytes"));
    }
}

#[test]
fn a_worker_can_retain_and_release_its_captured_permit() {
    let source = format!(
        "{SOURCE}\n{}",
        code_str! {
            verus! {
                fn worker(p: Permit<'static>, keep: bool)
                    resources peak(memory) <= 512,
                {
                    let task = move || {
                        if let Some(q) = retain(p, keep) {
                            let buffer = Box::new([0u8; 75]);
                            drop(buffer);
                            q.release();
                        }
                    };
                    let handle = vstd::thread::spawn(task);
                    let done = handle.join();
                }
            }
        }
    );
    let trace = verify_one_file("worker_retained_permit", source, &["--trace", "--no-cheating"])
        .unwrap_err();
    assert_eq!(trace.errors.len(), 1);
    assert!(trace.errors[0].message.contains("global lifetime and interference proofs"));
    assert!(trace.notes.iter().any(|n| {
        n.message.starts_with("75-byte allocation only observed within intact holder capture ")
    }));
}
