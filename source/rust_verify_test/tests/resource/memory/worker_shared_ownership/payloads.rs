//! An indexed outer Arc keeps the original payload, its aliases and any join obligation.
use super::GLOBAL;
use crate::common::{assert_vir_error_msg, assert_vir_error_msgs};

fn verify(name: &str, source: &str, messages: &[&str]) {
    let code = format!("use vstd::prelude::*; verus! {{ {source} }}");
    let errors = crate::verify_one_file(name, code, &[]).unwrap_err();
    if let [only] = messages {
        assert_vir_error_msg(errors, only);
    } else {
        assert_vir_error_msgs(errors, messages);
    }
}

const BUDGET: &str = "conditional memory budget exceeded";
const PASS: &str = "fn pass(v: Vec<u8>) -> Vec<u8> resources peak(memory) <= 64 { v }";

fn indexed(payload: &str, setup: &str, checkpoints: &str) -> String {
    format!(
        r#"
        let outer = std::sync::Arc::new({payload});
        let peer = outer.clone();
        let mut jobs = Vec::with_capacity(2);
        jobs.push(std::thread::spawn(move || peer));
        jobs.push(std::thread::spawn(move || outer));
        {setup}
        let last = jobs.pop().unwrap().join().unwrap();
        drop(jobs);
        {checkpoints}
    "#
    )
}

const DROP_FIRST: &str = "let first = jobs.pop().unwrap().join().unwrap(); drop(first);";

#[test]
fn incoming_buffer_follows_its_paying_frame_through_a_helper() {
    let body = indexed(
        "v",
        DROP_FIRST,
        "assert(current(memory) <= 48); drop(last); assert(current(memory) <= 0);",
    );
    let input = format!(
        "{PASS} fn consume(v: Vec<u8>) resources peak(memory) <= 512 {{ let v = pass(v); {body} }}"
    );
    // The receiving frame pays for the outer control block, Vec header and handle.
    verify("input", &input, &[GLOBAL]);
    verify("input_short", &input.replace("<= 48", "<= 47"), &[BUDGET, GLOBAL]);

    let caller = r#"
        fn caller() resources peak(memory) <= 612 {
            let buffer = Vec::<u8>::with_capacity(100);
            consume(buffer);
            assert(current(memory) <= 0);
            let next = Vec::<u8>::with_capacity(588);
            assert(current(memory) <= 612); drop(next);
        }
    "#;
    verify("closed_consumer", &format!("{input}{caller}"), &[GLOBAL]);
    // The helper's declared allowance is 512. The caller still pays the
    // original 100 bytes during the call and can reuse them on return.
    let small = caller
        .replace("peak(memory) <= 612", "peak(memory) <= 611")
        .replace("capacity(588)", "capacity(100)");
    verify("closed_consumer_short", &format!("{input}{small}"), &[BUDGET, GLOBAL]);

    // In the allocating frame the same helper returns the original 100-byte buffer.
    let allocating = input
        .replace("fn consume(v: Vec<u8>)", "fn consume()")
        .replace(
            "let v = pass(v);",
            "let seed = Vec::<u8>::with_capacity(100); let v = pass(seed);",
        )
        .replace("<= 48", "<= 148");
    verify("allocating", &allocating, &[GLOBAL]);
    verify("allocating_short", &allocating.replace("<= 148", "<= 147"), &[BUDGET, GLOBAL]);
}

#[test]
fn two_owned_allocations_survive_collection() {
    let body = indexed(
        "Payload { v, tail: Box::new(9u64) }",
        DROP_FIRST,
        "assert(current(memory) <= 89); drop(last); assert(current(memory) <= 0);",
    );
    let code = format!(
        "{PASS} struct Payload {{ v: Vec<u8>, tail: Box<u64> }}
        fn f() resources peak(memory) <= 512 {{
            let seed = Vec::<u8>::with_capacity(25); let v = pass(seed); {body}
        }}"
    );
    // 8-byte handle, 16-byte control, 32-byte inline payload, 25-byte buffer and 8-byte box.
    verify("vector_box", &code, &[GLOBAL]);
    verify("vector_box_short", &code.replace("<= 89", "<= 88"), &[BUDGET, GLOBAL]);
}

const SYMBOLIC_PROGRAM: &str = r#"
    struct Pair { a: std::sync::Arc<Vec<u8>>, b: std::sync::Arc<Vec<u8>> }
    fn f(n: u16) requires n > 0, resources peak(memory) <= 9 * n + 384 {
        let inner = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
        let alias = inner.clone();
        let root = std::sync::Arc::new(Pair { a: inner, b: alias });
        let mut jobs = Vec::with_capacity(n as usize);
        let mut i = 0u16;
        while i < n invariant i <= n, jobs.len() == i, decreases n - i, {
            let outer = root.clone();
            jobs.push(std::thread::spawn(move || outer));
            i += 1;
        }
        drop(root);
        COLLECT
        assert(current(memory) <= 103); drop(last);
        assert(current(memory) <= 4);
    }
"#;

const DROP_ALL_BUT_LAST: &str = r#"
        while jobs.len() > 1 invariant 1 <= jobs.len() <= n, decreases jobs.len(), {
            let result = jobs.pop().unwrap().join().unwrap(); drop(result);
        }
        let last = jobs.pop().unwrap().join().unwrap();
        drop(jobs);
"#;

#[test]
fn symbolic_collection_releases_duplicate_inner_links_once() {
    let symbolic = SYMBOLIC_PROGRAM.replace("COLLECT", DROP_ALL_BUT_LAST);
    verify("nested", &symbolic, &[GLOBAL]);
    verify("nested_short", &symbolic.replace("<= 103", "<= 102"), &[BUDGET, GLOBAL]);
    let keep = symbolic
        .replace("let alias =", "let keep = inner.clone(); let alias =")
        .replace("<= 103", "<= 111")
        .replace("<= 4);", "<= 71); drop(keep);");
    verify("external_inner", &keep, &[GLOBAL]);
    verify("early_inner_release", &keep.replace("<= 71", "<= 12"), &[BUDGET, GLOBAL]);
    let full_drain = symbolic
        .replace("requires n > 0, ", "")
        .replace(
            "jobs.len() > 1 invariant 1 <= jobs.len() <= n",
            "jobs.len() > 0 invariant jobs.len() <= n",
        )
        .replace("let last = jobs.pop().unwrap().join().unwrap();", "")
        .replace("assert(current(memory) <= 103); drop(last);", "");
    verify("empty_or_drained", &full_drain, &[GLOBAL]);
}

#[test]
fn a_symbolic_result_vector_retains_the_payload_until_its_last_alias_drops() {
    let collect = r#"
        let mut results = Vec::with_capacity(n as usize);
        while jobs.len() > 0 invariant jobs.len() + results.len() == n, decreases jobs.len(), {
            let r = jobs.pop().unwrap().join().unwrap(); results.push(r);
        }
        drop(jobs);
        let last = results.pop().unwrap(); drop(results);
    "#;
    let program = SYMBOLIC_PROGRAM.replace("COLLECT", collect).replace("9 * n", "17 * n");
    verify("retained_results", &program, &[GLOBAL]);
    verify("retained_short", &program.replace("<= 103", "<= 102"), &[BUDGET, GLOBAL]);
}

#[test]
fn indexed_result_can_destroy_both_backings_before_its_join() {
    let code = SYMBOLIC_PROGRAM.replace("COLLECT", DROP_ALL_BUT_LAST).replace(
        "assert(current(memory) <= 103); drop(last);",
        r#"
        let final_worker = std::thread::spawn(move || {
            assert(current(memory) <= 99); drop(last); assert(current(memory) <= 8);
        });
        final_worker.join().unwrap();
    "#,
    );
    verify("pre_join", &code, &[GLOBAL]);
    let peer = code
        .replace("let alias =", "let keep = inner.clone(); let alias =")
        .replace("assert(current(memory) <= 4);", "drop(keep); assert(current(memory) <= 4);");
    verify("pre_join_survivor", &peer, &["at a worker checkpoint with shared backing", GLOBAL]);
    // Keep a second outer alias in its original worker slot. Both inner
    // fields remain live even though the checked worker has dropped its handle.
    let outstanding = code
        .replace("requires n > 0", "requires n >= 2")
        .replace(
            "jobs.len() > 1 invariant 1 <= jobs.len()",
            "jobs.len() > 2 invariant 2 <= jobs.len()",
        )
        .replace("drop(jobs);", "")
        .replace(
            "final_worker.join().unwrap();",
            "final_worker.join().unwrap();
            let peer = jobs.pop().unwrap().join().unwrap(); drop(jobs); drop(peer);",
        );
    verify("unjoined_peer", &outstanding, &["at a worker checkpoint with shared backing", GLOBAL]);
}

#[test]
fn a_job_inside_the_payload_must_reach_its_own_join() {
    let checked = r#"
        let slot = std::sync::Arc::into_inner(last);
        match slot {
            Some(job) => {
                let buffer = job.join().unwrap();
                assert(current(memory) <= 48);
                drop(buffer);
            },
            None => {},
        }
        assert(current(memory) <= 0);
    "#;
    let body = indexed("job", DROP_FIRST, checked);
    let code = format!(
        "fn f() resources peak(memory) <= 600 {{
        let job = std::thread::spawn(move || Vec::<u8>::with_capacity(24)); {body}
    }}"
    );
    verify("joined", &code, &[GLOBAL]);
    let stored = code.replace(
        "let slot =",
        "let mut results = Vec::with_capacity(1);
        results.push(last); let last = results.pop().unwrap(); drop(results); let slot =",
    );
    verify("stored_job", &stored, &[GLOBAL]);
    verify("joined_short", &code.replace("<= 48", "<= 47"), &[BUDGET, GLOBAL]);
    verify(
        "lost_job",
        &code.replace(checked, "drop(last);"),
        &["detached workers in a memory accounting scope"],
    );
    let shared = code.replace("let slot =", "let keep = last.clone(); let slot =");
    verify("aliased", &shared, &["extracting a shared payload without exclusive ownership"]);
    let retained = code
        .replace(
            DROP_FIRST,
            "let mut holders = Vec::with_capacity(1);
         let first = jobs.pop().unwrap().join().unwrap(); holders.push(first);",
        )
        .replace("assert(current(memory) <= 48);", "")
        .replace("assert(current(memory) <= 0);", "drop(holders);");
    verify(
        "reserved",
        &retained,
        &["cannot extract a shared payload while indexed aliases still own it", GLOBAL],
    );
}
