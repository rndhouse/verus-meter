//! Verified reader/writer workspaces and interference on real acquisition scopes.
use super::*;

const SOURCE: &str = include_str!("rwlock.verus.rs");

#[test]
fn checked_generic_workspaces_include_ownership_and_explicit_release_frames() {
    verify_one_file("rwlock_workspaces", SOURCE.into(), &["--no-cheating"]).unwrap();
    for peak in [98, 46, 777, 72, 60, 85, 94] {
        let short = peak - 1;
        let source = SOURCE.replace(&format!("<= {peak},"), &format!("<= {short},"));
        let err = verify_one_file("rwlock_short", source, &["--no-cheating"]).unwrap_err();
        assert_vir_error_msg(err, &format!("peak {peak} bytes exceeds budget {short} bytes"));
    }
}

#[test]
fn readers_share_while_a_writer_excludes_a_reader_on_the_same_instance() {
    let pair = code_str! {
        verus! {
            fn workers() resources peak(memory) <= 1024, {
                let lock = std::sync::Arc::new(RwLock::<u32, Any>::new(1, Ghost(Any)));
                let peer = lock.clone();
                let a = vstd::thread::spawn(move || {
                    let r = lock.acquire_read();
                    let x = Box::new([0u8; 51]); drop(x);
                    r.release_read();
                });
                let b = vstd::thread::spawn(move || {
                    let (v, w) = peer.acquire_write();
                    let y = Box::new([0u8; 52]); drop(y);
                    w.release_write(v);
                });
                let a_done = a.join();
                let b_done = b.join();
            }
        }
    };
    for (code, exclusive) in [
        (pair.to_string(), true),
        (
            pair.replace(
                "lock.clone()",
                "std::sync::Arc::new(RwLock::<u32, Any>::new(1, Ghost(Any)))",
            ),
            false,
        ),
        (
            pair.replace("let (v, w) = peer.acquire_write();", "let w = peer.acquire_read();")
                .replace("w.release_write(v)", "w.release_read()"),
            false,
        ),
    ] {
        let trace = verify_one_file(
            "rwlock_roles",
            format!("{SOURCE}\n{code}"),
            &["--trace", "--no-cheating"],
        )
        .unwrap_err();
        assert_eq!(trace.errors.len(), 1);
        assert!(trace.errors[0].message.contains("global lifetime and interference proofs"));
        assert_eq!(
            trace.notes.iter().any(|n| n.message
                == "verified incompatible holder roles on the same issuer across actors"),
            exclusive
        );
    }
}

#[test]
fn owned_buffers_survive_release_moves_and_helper_returns() {
    let program = format!("{SOURCE}\n{}", include_str!("rwlock_owned.verus.rs"));
    verify_one_file("rwlock_buffers", program.clone(), &["--no-cheating"]).unwrap();
    let too_small = program.replace("2 * n + 1500", "n + 1500");
    let failure = verify_one_file("rwlock_overlap", too_small, &["--no-cheating"]).unwrap_err();
    assert_vir_error_msg(failure, "conditional memory budget exceeded");
}

#[test]
fn populated_cell_destruction_never_reclaims_its_payload() {
    for body in ["drop(cell);", "if early { return; } let value = cell.into_inner(); drop(value);"]
    {
        let code = format!(
            "{SOURCE}\nverus! {{ fn leak(cell: RwLock<Vec<u8>, Any>, early: bool) resources peak(memory) <= 1024, {{ {body} }} }}"
        );
        let failure = verify_one_file("rwlock_retained", code, &["--no-cheating"]).unwrap_err();
        assert_vir_error_msg(failure, "discarding a populated RwLock");
    }
}

#[test]
fn writer_replaces_only_its_own_cell() {
    let body = code_str! {
        verus! {
            fn swap(n: usize) requires n == 4096, resources peak(memory) <= n + 1500, {
                let a: Vec<u8> = Vec::with_capacity(n);
                let b: Vec<u8> = Vec::with_capacity(1);
                let left = RwLock::<_, Any>::new(a, Ghost(Any));
                let right = RwLock::<_, Any>::new(b, Ghost(Any));
                let (a, x) = left.acquire_write();
                let (b, y) = right.acquire_write();
                x.release_write(a); y.release_write(b);
                let first = left.into_inner(); drop(first);
                let other: Vec<u8> = Vec::with_capacity(n);
                let second = right.into_inner();
                drop(other); drop(second);
            }
        }
    };
    let program = format!("{SOURCE}\n{body}");
    verify_one_file("rwlock_instance", program.clone(), &["--no-cheating"]).unwrap();
    let swap = program.replace(
        "x.release_write(a); y.release_write(b);",
        "x.release_write(b); y.release_write(a);",
    );
    assert_ne!(program, swap);
    let failure = verify_one_file("rwlock_swap", swap, &["--no-cheating"]).unwrap_err();
    assert_vir_error_msg(failure, "conditional memory budget exceeded");
}

#[test]
fn a_worker_receives_the_existing_payload_when_the_lock_moves() {
    let body = code_str! {
        verus! {
            fn moved(n: usize) requires n == 4096, resources peak(memory) <= n + 2048, {
                let a: Vec<u8> = Vec::with_capacity(n);
                let cell = RwLock::<_, Any>::new(a, Ghost(Any));
                let j = vstd::thread::spawn(move || {
                    let (old, writer) = cell.acquire_write();
                    writer.release_write(old);
                    let value = cell.into_inner();
                    drop(value);
                });
                let done = j.join();
            }
        }
    };
    let trace =
        verify_one_file("rwlock_moved", format!("{SOURCE}\n{body}"), &["--trace", "--no-cheating"])
            .unwrap_err();
    assert_eq!(trace.errors.len(), 1);
    assert!(trace.errors[0].message.contains("global lifetime and interference proofs"));
}

#[test]
fn shared_writer_publishes_the_payload_recovered_after_join() {
    let program = format!("{SOURCE}\n{}", include_str!("rwlock_shared.verus.rs"));
    let verify =
        |name, code| verify_one_file(name, code, &["--trace", "--no-cheating"]).unwrap_err();
    let checked = verify("rwlock_shared", program.clone());
    assert_eq!(checked.errors.len(), 1);
    assert!(checked.errors[0].message.contains("global interference proofs"));
    assert!(checked.errors[0].message.contains("linked acquisitions = 1"));

    let short = verify("rwlock_shared_short", program.replace("<= 1200", "<= 600"));
    assert!(short.errors.iter().any(|e| e.message.contains("conditional memory budget exceeded")));

    let abandoned = verify(
        "rwlock_shared_abandoned",
        program.replace("guard.release_write(new);", "drop(guard); drop(new);"),
    );
    assert_vir_error_msg(abandoned, "an acquired payload without its outgoing contents");

    let two = program.replace("let guard = read.acquire_read();\n        let view = guard.borrow();\n        let count = view.len();\n        guard.release_read();",
        "let (old, guard) = read.acquire_write(); guard.release_write(Vec::<u8>::with_capacity(601)); drop(old);");
    assert_ne!(two, program);
    let writers = verify("rwlock_shared_writers", two);
    assert_eq!(writers.errors.len(), 1);
    assert!(writers.errors[0].message.contains("linked acquisitions = 2"));
}
