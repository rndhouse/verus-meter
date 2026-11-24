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
