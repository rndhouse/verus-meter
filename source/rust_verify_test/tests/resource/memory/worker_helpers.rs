//! Synchronous calls transfer the selected worker records and their backing.
//! The helper and the closed spawning domain must still report the global gap.

use crate::{common::assert_vir_error_msgs, verify_one_file};

const HELPER: &str = "worker population helpers before global lifetime and interference proofs";
const GLOBAL: &str = "checked worker effects still require global lifetime and interference proofs";

/// Pop down to a caller-selected count, allowing either outcome of each vstd join.
const COLLECT: &str = r#"
    fn collect(mut pending: Vec<JoinHandle<u16>>, keep: u16) -> (rest: Vec<JoinHandle<u16>>)
        requires keep <= pending.len(),
        ensures rest.len() == keep,
        resources peak(memory) <= 512
    {
        while pending.len() > keep as usize
            invariant keep <= pending.len(),
            decreases pending.len(),
        {
            let handle = pending.pop().unwrap();
            let outcome = handle.join();
            drop(outcome);
        }
        pending
    }
"#;

#[track_caller]
fn check(name: &str, functions: &str, errors: &[&str]) {
    let source =
        format!("use vstd::prelude::*; use vstd::thread::JoinHandle; verus! {{ {functions} }}");
    assert_vir_error_msgs(verify_one_file(name, source, &[]).unwrap_err(), errors);
}

#[test]
fn nested_helpers_transfer_the_remaining_symbolic_population() {
    let caller = r#"
        fn forward(v: Vec<JoinHandle<u16>>, keep: u16) -> (r: Vec<JoinHandle<u16>>)
            requires keep <= v.len(),
            ensures r.len() == keep,
            resources peak(memory) <= 1024
        { collect(v, keep) }

        fn f(n: u16, keep: u16)
            requires keep <= n,
            resources peak(memory) <= n * 128 + 131072
        {
            let mut batch = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, batch.len() == i, decreases n-i, {
                let h = vstd::thread::spawn(move || i);
                batch.push(h);
                i += 1;
            }
            let mut rest = forward(batch, keep);
            while rest.len() > 0 decreases rest.len(), {
                let size = rest.pop().unwrap().join().unwrap();
                let buffer = Vec::<u8>::with_capacity(size as usize);
                drop(buffer);
            }
        }
    "#;
    check("nested_population_helpers", &format!("{COLLECT}{caller}"), &[HELPER, HELPER, GLOBAL]);
}

#[test]
fn partial_helper_preserves_live_storage_and_join_responsibility() {
    let caller = r#"
        fn f() resources peak(memory) <= 4096 {
            let mut batch = Vec::with_capacity(2);
            let a = vstd::thread::spawn(move || 64u16);
            batch.push(a);
            let b = vstd::thread::spawn(move || 1024u16);
            batch.push(b);
            let mut rest = collect(batch, 1);
            assert(current(memory) <= 41);
            let size = rest.pop().unwrap().join().unwrap();
            drop(rest);
        }
    "#;
    // Vector header, both reserved handle slots and the surviving completion tag.
    let source = format!("{COLLECT}{caller}");
    check("partial_population_bytes", &source, &[HELPER, GLOBAL]);
    check(
        "partial_population_short",
        &source.replace("<= 41", "<= 40"),
        &["conditional memory budget exceeded", HELPER, GLOBAL],
    );
    check(
        "partial_population_lost",
        &source.replace("let size = rest.pop().unwrap().join().unwrap();", ""),
        &["cannot discard outstanding worker handles", HELPER, GLOBAL],
    );
}

#[test]
fn helper_summary_requires_the_original_backing_and_actual_join() {
    check(
        "helper_replaces_backing",
        &COLLECT.replace("        pending\n", "        Vec::new()\n"),
        &["a worker population helper must transfer its input vector"],
    );
    let detached = COLLECT.replace("let outcome = handle.join();", "let outcome = handle;");
    check("helper_drops_handle", &detached, &["without a checked back-edge ownership relation"]);
    check(
        "helper_invents_success",
        &COLLECT.replace("drop(outcome);", "let value = outcome.unwrap();"),
        &["Result success without a checked worker outcome"],
    );
    let native = COLLECT.replace("Vec<JoinHandle", "Vec<std::thread::JoinHandle");
    check(
        "helper_unmodeled_panic_payload",
        &native,
        &["a parameter join with owned or unknown outcome storage"],
    );
}

#[test]
fn native_helper_forwards_the_selected_worker_with_its_owned_result() {
    let source = r#"
        fn relay(v: Vec<std::thread::JoinHandle<Vec<u8>>>) -> (r: Vec<std::thread::JoinHandle<Vec<u8>>>)
            ensures r == v,
            resources peak(memory) <= 80
        { let moved = v; moved }

        fn f() resources peak(memory) <= 4096 {
            let mut handles = Vec::with_capacity(2);
            let a = std::thread::spawn(move || Vec::<u8>::with_capacity(64));
            handles.push(a);
            let b = std::thread::spawn(move || Vec::<u8>::with_capacity(1024));
            handles.push(b);
            let collector = std::thread::spawn(move || -> (r: Vec<std::thread::JoinHandle<Vec<u8>>>)
                ensures r.len() == 1
            {
                let mut pending = handles;
                let large = pending.pop().unwrap().join().unwrap();
                drop(large);
                pending
            });
            let rest = collector.join().unwrap();
            let mut rest = relay(rest);
            let buffer = rest.pop().unwrap().join().unwrap();
            drop(rest);
            assert(current(memory) <= 88);
            drop(buffer);
            assert(current(memory) <= 0);
        }
    "#;
    check("native_population_relay", source, &[HELPER, GLOBAL]);
    let larger = source.replace("with_capacity(64)", "with_capacity(65)");
    check(
        "native_population_relay_too_large",
        &larger,
        &["memory budget exceeded", HELPER, GLOBAL],
    );
}
