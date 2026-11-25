//! Shared allocation identity and lifetime across worker captures, joins and drops.

mod collections;
mod occurrences;
mod payloads;

use super::support::rejects;

const GLOBAL: &str = "checked worker effects still require global lifetime and interference proofs";

#[test]
fn a_strong_drop_cannot_discharge_an_outstanding_job_inside_the_payload() {
    rejects(
        "job_in_shared_payload",
        r#"
        fn f() resources peak(memory) <= 600 {
            let job = vstd::thread::spawn(move || 3u64);
            let root = std::sync::Arc::new(job);
            let worker = vstd::thread::spawn(move || { drop(root); });
            worker.join().unwrap();
        }
        "#,
        "detached workers in a memory accounting scope",
    );
}

#[test]
fn last_strong_drop_in_a_worker_releases_the_backing_before_its_join() {
    let program = r#"
        use vstd::prelude::*;
        verus! {
        struct Pair { left: std::sync::Arc<Vec<u8>>, right: std::sync::Arc<Vec<u8>> }
        fn f() resources peak(memory) <= 1024 {
            let buf = std::sync::Arc::new(Vec::<u8>::with_capacity(64));
            let alias = buf.clone();
            let root = std::sync::Arc::new(Pair { left: buf, right: alias });
            let peer = root.clone();
            let first = vstd::thread::spawn(move || { drop(peer); });
            let last = vstd::thread::spawn(move || {
                first.join().unwrap();
                if false { assert(current(memory) <= 0); }
                assert(current(memory) <= 152);
                drop(root);
                assert(current(memory) <= 16);
            });
            last.join().unwrap();
            assert(current(memory) <= 0);
        }
        }
    "#;
    // The receiving worker's 16-byte environment retains the 32-byte outer
    // backing and one 104-byte inner backing through both fields. Its own
    // joiner need not run for the source destructor to release both.
    let valid = crate::verify_one_file("pre_join_final_drop", program.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let extra = program
        .replace("let alias = buf.clone();", "let keep = buf.clone(); let alias = buf.clone();")
        .replace("last.join().unwrap();", "last.join().unwrap(); drop(keep);");
    for (name, code) in [
        ("pre_join_one_byte_short", program.replace("<= 152", "<= 151")),
        ("inner_alias_still_live", extra),
        (
            "peer_returns_alias",
            program
                .replace("move || { drop(peer); }", "move || peer")
                .replace("first.join().unwrap();", "let keep = first.join().unwrap();")
                .replace("<= 152", "<= 160")
                .replace("<= 16);", "<= 24); drop(keep);"),
        ),
    ] {
        let error = crate::verify_one_file(name, code, &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["at a worker checkpoint with shared backing", GLOBAL],
        );
    }
}

#[test]
fn repeated_coordinator_visits_release_the_current_visits_shared_buffer() {
    let program = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= 256 {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let root = std::sync::Arc::new(Vec::<u8>::with_capacity(12));
                let second = root.clone();
                let first = vstd::thread::spawn(move || { drop(root); });
                let last = vstd::thread::spawn(move || {
                    first.join().unwrap();
                    assert(current(memory) <= 68);
                    drop(second);
                    assert(current(memory) <= 16);
                });
                last.join().unwrap();
                i += 1;
            }
            assert(current(memory) <= 4);
        }
        }
    "#;
    // Every iteration constructs fresh backing and settles both workers
    // before the next visit. With zero visits, only the two u16 slots remain.
    let valid = crate::verify_one_file("fresh_shared_each_visit", program.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let short = crate::verify_one_file(
        "fresh_shared_one_byte_short",
        program.replace("<= 68", "<= 67"),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(short, &["68 bytes exceeds budget 67 bytes", GLOBAL]);
}

#[test]
fn symbolic_shared_checkpoint_uses_the_workers_captured_condition() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16, small: bool) requires n <= 64, small ==> n <= 7,
            resources peak(memory) <= n + 128,
        {
            let root = std::sync::Arc::new(Vec::<u8>::with_capacity(n as usize));
            let h = vstd::thread::spawn(move || {
                if small {
                    assert(current(memory) <= 56);
                } else {
                    assert(current(memory) <= 113);
                }
                drop(root);
                assert(current(memory) <= 9);
            });
            h.join().unwrap();
        }
        }
    "#;
    // The immutable flag, Arc handle, control block and Vec contribute 49
    // bytes. At publication the path condition selects the applicable limit.
    let valid = crate::verify_one_file("conditional_backing", code.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    for (name, budget, short) in [("small", "<= 56", "<= 55"), ("large", "<= 113", "<= 112")] {
        let error = crate::verify_one_file(name, code.replace(budget, short), &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["conditional memory budget exceeded at a worker checkpoint", GLOBAL],
        );
    }
}

#[test]
fn worker_checkpoint_follows_the_identity_of_a_selected_join_result() {
    let program = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 1024 {
            let small = std::sync::Arc::new(Vec::<u8>::with_capacity(7));
            let large = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
            let mut jobs = Vec::with_capacity(2);
            let a = std::thread::spawn(move || small);
            jobs.push(a);
            let b = std::thread::spawn(move || large);
            jobs.push(b);
            let other = jobs.pop().unwrap().join().unwrap();
            drop(other);
            let selected = jobs.pop().unwrap().join().unwrap();
            drop(jobs);
            let child = std::thread::spawn(move || {
                assert(current(memory) <= 55);
                drop(selected);
                assert(current(memory) <= 8);
            });
            child.join().unwrap();
        }
        }
    "#;
    // After the first result is dropped, the second points to the 7-byte buffer.
    // Swapping their capacities makes that result carry a 19-byte buffer.
    let reversed = program.replace("capacity(7)", "capacity(19)").replacen(
        "let large = std::sync::Arc::new(Vec::<u8>::with_capacity(19))",
        "let large = std::sync::Arc::new(Vec::<u8>::with_capacity(7))",
        1,
    );
    let retain_other = program
        .replace("drop(other);", "")
        .replace("child.join().unwrap();", "child.join().unwrap(); drop(other);");
    for (name, code) in [
        ("selected_small", program.to_string()),
        ("unrelated_result_stays_live", retain_other.clone()),
        ("selected_large", reversed.replace("<= 55", "<= 67")),
    ] {
        let error = crate::verify_one_file(name, code, &[]).unwrap_err();
        crate::common::assert_vir_error_msg(error, GLOBAL);
    }
    for (name, code) in [
        // The first two collected results now refer to different allocations,
        // but the third worker returned an independent alias of the small one.
        (
            "other_reservation_keeps_small",
            retain_other
                .replace("Vec::with_capacity(2)", "Vec::with_capacity(3)")
                .replace("let a =", "let alias = small.clone(); let a =")
                .replace(
                    "let other =",
                    "let c = std::thread::spawn(move || alias); jobs.push(c); let other =",
                )
                .replace(
                    "let selected =",
                    "let discarded = jobs.pop().unwrap().join().unwrap(); drop(discarded); let selected =",
                ),
        ),
        ("small_short", program.replace("<= 55", "<= 54")),
        ("large_short", reversed.replace("<= 55", "<= 66")),
        (
            "selected_external_clone",
            program
                .replace("drop(jobs);", "drop(jobs); let keep = selected.clone();")
                .replace("child.join().unwrap();", "child.join().unwrap(); drop(keep);"),
        ),
    ] {
        let error = crate::verify_one_file(name, code, &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["at a worker checkpoint with shared backing", GLOBAL],
        );
    }
}

#[test]
fn indexed_workers_can_own_every_alias_of_the_backing() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 512 {
            let root = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
            let alias = root.clone();
            let mut handles = Vec::with_capacity(2);
            handles.push(std::thread::spawn(move || alias));
            handles.push(std::thread::spawn(move || root));
            assert(current(memory) <= 101);
            let first = handles.pop().unwrap().join().unwrap();
            drop(first);
            assert(current(memory) <= 100);
            let last = handles.pop().unwrap().join().unwrap();
            drop(handles);
            assert(current(memory) <= 67);
            drop(last);
            assert(current(memory) <= 0);
        }
        }
    "#;
    // The vector and its two slots cost 40, the tags cost 2, and the single
    // shared backing costs 59. Each join transfers a different strong alias.
    let valid = crate::verify_one_file("only_indexed_owners", code.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    for (name, bound, smaller) in [
        ("publication", "<= 101", "<= 100"),
        ("after_first_drop", "<= 100", "<= 99"),
        ("last_owner", "<= 67", "<= 66"),
    ] {
        let error = crate::verify_one_file(name, code.replace(bound, smaller), &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn a_symbolic_worker_population_reserves_each_shared_backing_once() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= n * 64 + 160 {
            let root = std::sync::Arc::new(17u64);
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let a = root.clone();
                let b = root.clone();
                let worker = std::thread::spawn(move || { drop(a); drop(b); 17u64 });
                handles.push(worker);
                i += 1;
            }
            drop(root);
            if n == 0 { assert(current(memory) <= 28); }
            if n == 2 { assert(current(memory) <= 118); }
            while handles.len() > 0 invariant handles.len() <= n, decreases handles.len(), {
                let h = handles.pop().unwrap();
                let _v = h.join().unwrap();
            }
            drop(handles);
            assert(current(memory) <= 4);
        }
        }
    "#;
    // 70 bytes in the publisher and up to 24 bytes per running worker.
    crate::verify_one_file("indexed_shared_backing", code.to_string(), &[]).unwrap();
    let short = crate::verify_one_file(
        "indexed_shared_backing_short",
        code.replace("<= 118", "<= 117"),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(short, "current(memory) checkpoint");
    // A different allocation with the same payload type needs its own backing.
    let distinct = code
        .replace("let mut handles", "let other = std::sync::Arc::new(17u64); let mut handles")
        .replace("let b = root.clone()", "let b = other.clone()")
        .replace("drop(root);", "drop(root); drop(other);");
    crate::verify_one_file("both_distinct_backings", distinct.replace("<= 118", "<= 142"), &[])
        .unwrap();
    let error = crate::verify_one_file("indexed_distinct_backings", distinct, &[]).unwrap_err();
    crate::common::assert_vir_error_msg(error, "current(memory) checkpoint");
}

#[test]
fn the_final_indexed_result_keeps_its_arc_after_all_joins() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) requires n > 0, resources peak(memory) <= n * 9 + 160 {
            let root = std::sync::Arc::new(17u64);
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let alias = root.clone();
                let worker = std::thread::spawn(move || alias);
                handles.push(worker);
                i += 1;
            }
            drop(root);
            while handles.len() > 1 invariant 1 <= handles.len() <= n, decreases handles.len(), {
                let h = handles.pop().unwrap();
                let alias = h.join().unwrap(); drop(alias);
            }
            let last = handles.pop().unwrap().join().unwrap();
            drop(handles);
            assert(current(memory) <= 36);
            drop(last);
            assert(current(memory) <= 4);
        }
        }
    "#;
    let valid = crate::verify_one_file("last_indexed_alias", code.to_string(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let short =
        crate::verify_one_file("last_indexed_alias_short", code.replace("<= 36", "<= 35"), &[])
            .unwrap_err();
    crate::common::assert_vir_error_msgs(short, &["live 36 bytes exceeds bound 35 bytes", GLOBAL]);
}

#[test]
fn indexed_arc_keeps_its_vector_buffer_through_the_final_join() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16, b: u16) resources peak(memory) <= n * 9 + b + 160 {
            let root = std::sync::Arc::new(Vec::<u8>::with_capacity(b as usize));
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let alias = root.clone();
                let worker = std::thread::spawn(move || alias);
                handles.push(worker);
                i += 1;
            }
            if n == 0 && b == 19 { assert(current(memory) <= 97); }
            drop(root);
            if n == 2 && b == 19 { assert(current(memory) <= 107); }
            if n == 0 {
                assert(current(memory) <= 30);
                return;
            }
            while handles.len() > 1 invariant 1 <= handles.len() <= n, decreases handles.len(), {
                let h = handles.pop().unwrap();
                let alias = h.join().unwrap(); drop(alias);
            }
            let last = handles.pop().unwrap().join().unwrap();
            drop(handles);
            if b == 19 { assert(current(memory) <= 73); }
            drop(last);
            assert(current(memory) <= 6);
        }
        }
    "#;
    let valid = crate::verify_one_file("indexed_arc_buffer", code.to_string(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);

    // At b = 19 the shared allocation contributes 16 control + 24 inline + 19
    // buffer bytes. Two pending workers and the final joined alias each retain it.
    for (name, exact, short) in [
        ("publisher_only", "<= 97", "<= 96"),
        ("pending", "<= 107", "<= 106"),
        ("joined", "<= 73", "<= 72"),
    ] {
        let error = crate::verify_one_file(name, code.replace(exact, short), &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
}

#[test]
fn mixed_arc_joins_keep_the_allocation_selected_by_each_pop() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 1024 {
            let small = std::sync::Arc::new(Vec::<u8>::with_capacity(7));
            let large = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
            let mut handles = Vec::with_capacity(3);
            let a = small.clone();
            let worker = std::thread::spawn(move || a);
            handles.push(worker);
            let b = large.clone();
            let worker = std::thread::spawn(move || b);
            handles.push(worker);
            let other = small.clone();
            let worker = std::thread::spawn(move || other);
            handles.push(worker);
            drop(small);
            drop(large);
            let first = handles.pop().unwrap().join().unwrap();
            let middle = handles.pop().unwrap().join().unwrap();
            let last = handles.pop().unwrap().join().unwrap();
            let survivor = last.clone();
            drop(last);
            drop(handles);
            drop(middle);
            assert(current(memory) <= 63);
            drop(first);
            assert(current(memory) <= 55);
            drop(survivor);
            assert(current(memory) <= 0);
        }
        }
    "#;
    let valid = crate::verify_one_file("mixed_arc_clone", code.to_string(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);

    // Two independent joins can return the same 47-byte backing. With two
    // handles it occupies 63 bytes, then 55 with one. The middle worker
    // returns the distinct 19-byte buffer.
    for (name, changed) in [
        ("mixed_arc_short", code.replace("<= 55", "<= 54")),
        ("mixed_arc_swapped", code.replace("survivor = last.clone()", "survivor = middle.clone()")),
    ] {
        let error = crate::verify_one_file(name, changed, &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["conditional memory budget exceeded", GLOBAL],
        );
    }
    let transferred = code.replace(
        "drop(survivor);",
        "let child = std::thread::spawn(move || { let r = survivor.clone(); drop(survivor); r });
         let r = child.join().unwrap(); assert(current(memory) <= 55); drop(r);",
    );
    let error =
        crate::verify_one_file("mixed_arc_transferred_alias", transferred, &[]).unwrap_err();
    crate::common::assert_vir_error_msg(error, GLOBAL);

    // The receiver owns the popped handle. The publisher still has two live
    // results while the receiver joins its worker and returns a cloned alias.
    let delegated = code.replace(
        "let last = handles.pop().unwrap().join().unwrap();",
        "let h = handles.pop().unwrap();
         let collector = std::thread::spawn(move || {
             let r = h.join().unwrap(); let alias = r.clone(); drop(r); alias
         });
         let last = collector.join().unwrap();",
    );
    let error =
        crate::verify_one_file("mixed_arc_delegated_join", delegated.clone(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(error, GLOBAL);
    let swapped = delegated.replace("survivor = last.clone()", "survivor = middle.clone()");
    let error = crate::verify_one_file("mixed_arc_delegated_wrong_root", swapped, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
    let foreign = delegated
        .replace("let collector =", "let foreign = middle.clone(); let collector =")
        .replace("let alias = r.clone(); drop(r); alias", "drop(r); foreign");
    let error = crate::verify_one_file("mixed_arc_foreign_result", foreign, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);

    let lost = delegated.replace(
        "let r = h.join().unwrap(); let alias = r.clone(); drop(r); alias",
        "drop(h); std::sync::Arc::new(Vec::<u8>::with_capacity(7))",
    );
    let error = crate::verify_one_file("mixed_arc_lost_join", lost, &[]).unwrap_err();
    crate::common::assert_vir_error_msg(error, "detached workers in a memory accounting scope");

    let forwarded = delegated
        .replace(
            "fn f()",
            "fn relay(v: Vec<std::thread::JoinHandle<std::sync::Arc<Vec<u8>>>>)
            -> (rest: Vec<std::thread::JoinHandle<std::sync::Arc<Vec<u8>>>>)
            ensures rest == v,
            resources peak(memory) <= 100
        { v }
        fn f()",
        )
        .replace("drop(large);", "drop(large); let mut handles = relay(handles);");
    let error = crate::verify_one_file("mixed_arc_helper_transfer", forwarded, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(
        error,
        &["worker population helpers before global lifetime and interference proofs", GLOBAL],
    );
}

#[test]
fn surviving_results_from_one_join_site_keep_their_own_backings() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 1024 {
            let small = std::sync::Arc::new(Vec::<u8>::with_capacity(7));
            let large = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
            let mut handles = Vec::with_capacity(2);
            CAPTURES
            drop(small); drop(large);
            let mut results = Vec::with_capacity(2);
            while handles.len() > 0
                invariant handles.len() + results.len() == 2,
                decreases handles.len(),
            {
                let h = handles.pop().unwrap();
                let link = h.join().unwrap();
                results.push(link);
            }
            drop(handles);
            let small = results.pop().unwrap();
            let large = results.pop().unwrap();
            let survivor = small.clone();
            drop(small); drop(large); drop(results);
            assert(current(memory) <= 55);
            drop(survivor);
            assert(current(memory) <= 0);
        }
        }
    "#
    .replace("CAPTURES", DISJOINT_CAPTURES);
    let bulk = code
        .replace("let large = results.pop().unwrap();", "")
        .replace("drop(large); drop(results);", "drop(results);");
    let cloned = code.replace(
        "results.push(link);",
        "let other = link.clone(); results.push(other); drop(link);",
    );
    for (name, program) in [
        ("join_site_move", code.clone()),
        ("join_site_bulk_drop", bulk),
        ("join_site_store_clone", cloned),
    ] {
        let error = crate::verify_one_file(name, program, &[]).unwrap_err();
        crate::common::assert_vir_error_msg(error, GLOBAL);
    }
    let swapped = code.replace("survivor = small.clone()", "survivor = large.clone()");
    let error = crate::verify_one_file("join_site_wrong_survivor", swapped, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}

// Each visit publishes two handles in this order. A complete drain covers
// n == 0. A partial drain requires a worker to remain for the final join.
fn mixed_arc_program(requirement: &str, captures: &str, collection: &str) -> String {
    r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) REQUIREMENT resources peak(memory) <= n * 18 + 320 {
            let small = std::sync::Arc::new(Vec::<u8>::with_capacity(7));
            let large = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
            let mut handles = Vec::with_capacity(2 * n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == 2 * i, decreases n - i, {
                CAPTURES
                i += 1;
            }
            drop(small); drop(large);
            COLLECTION
            assert(current(memory) <= 4);
        }
        }
    "#
    .replace("REQUIREMENT", requirement)
    .replace("CAPTURES", captures)
    .replace("COLLECTION", collection)
}

const BOTH_CAPTURES: &str = r#"
    let a = small.clone(); let b = large.clone();
    let worker = std::thread::spawn(move || { drop(b); a });
    handles.push(worker);
    let c = large.clone(); let d = small.clone();
    let worker = std::thread::spawn(move || { drop(d); c });
    handles.push(worker);
"#;

const DISJOINT_CAPTURES: &str = r#"
    let a = small.clone();
    let worker = std::thread::spawn(move || a);
    handles.push(worker);
    let c = large.clone();
    let worker = std::thread::spawn(move || c);
    handles.push(worker);
"#;

const FULL_DRAIN: &str = r#"
    while handles.len() > 0 invariant handles.len() <= 2 * n, decreases handles.len(), {
        let h = handles.pop().unwrap();
        let link = h.join().unwrap();
        drop(link);
    }
    drop(handles);
"#;

#[test]
fn mixed_arc_workers_reconcile_a_symbolic_number_of_results() {
    let multiple = DISJOINT_CAPTURES.replace(
        "let worker = std::thread::spawn(move || a);",
        "let extra = small.clone(); let worker = std::thread::spawn(move || { drop(extra); a });",
    );
    for (name, captures) in [
        ("mixed_arc_drain", BOTH_CAPTURES),
        ("mixed_arc_disjoint_drain", DISJOINT_CAPTURES),
        ("mixed_arc_weighted_drain", multiple.as_str()),
    ] {
        let error = crate::verify_one_file(name, mixed_arc_program("", captures, FULL_DRAIN), &[])
            .unwrap_err();
        crate::common::assert_vir_error_msg(error, GLOBAL);
    }
}

#[test]
fn mixed_arc_drain_can_branch_on_the_remaining_length() {
    // Both paths consume one slot. The last path creates an extra local alias.
    let drain = r#"
        while handles.len() > 0 invariant handles.len() <= 2 * n, decreases handles.len(), {
            if handles.len() == 1 {
                let h = handles.pop().unwrap();
                let link = h.join().unwrap();
                let alias = link.clone(); drop(link); drop(alias);
            } else {
                let h = handles.pop().unwrap();
                let link = h.join().unwrap(); drop(link);
            }
        }
        drop(handles);
    "#;
    let error = crate::verify_one_file(
        "mixed_arc_branch",
        mixed_arc_program("", DISJOINT_CAPTURES, drain),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(error, GLOBAL);
}

#[test]
fn mixed_arc_partial_drain_preserves_the_final_handle() {
    let drain = r#"
        while handles.len() > 1 invariant 1 <= handles.len() <= 2 * n, decreases handles.len(), {
            let h = handles.pop().unwrap();
            let link = h.join().unwrap(); drop(link);
        }
        let last = handles.pop().unwrap().join().unwrap();
        drop(handles);
        assert(current(memory) <= 59);
        drop(last);
    "#;
    let program = mixed_arc_program("requires n > 0,", BOTH_CAPTURES, drain);
    let error = crate::verify_one_file("mixed_arc_partial", program.clone(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(error, GLOBAL);

    // The first publication is the final join. Returning its larger buffer
    // breaks the 59-byte checkpoint while preserving every spawn and join.
    let swapped = program.replace("drop(b); a", "drop(a); b").replace("drop(d); c", "drop(c); d");
    let error = crate::verify_one_file("mixed_arc_partial_wrong_buffer", swapped, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}

#[test]
fn mixed_arc_drain_rejects_a_fictitious_worker() {
    let invented = format!("assert(handles.len() == 2 * n + 1); {FULL_DRAIN}");
    let error = crate::verify_one_file(
        "mixed_arc_invented",
        mixed_arc_program("", DISJOINT_CAPTURES, &invented),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["assertion failed", GLOBAL]);

    let again = FULL_DRAIN.replace(
        "drop(handles);",
        "let absent = handles.pop().unwrap(); absent.join().unwrap(); drop(handles);",
    );
    let error = crate::verify_one_file(
        "mixed_arc_extra_join",
        mixed_arc_program("", DISJOINT_CAPTURES, &again),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(
        error,
        &["cannot establish the selected worker's family and result description", GLOBAL],
    );
}

#[test]
fn worker_result_fields_preserve_distinct_shared_roots() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        struct Links { first: std::sync::Arc<Vec<u8>>, second: std::sync::Arc<Vec<u8>> }
        fn f(n: u16) resources peak(memory) <= n * 8 + 2048 {
            let small = std::sync::Arc::new(Vec::<u8>::with_capacity(7));
            let large = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
            let jobs: Vec<Box<u64>> = Vec::with_capacity(n as usize);
            let worker = std::thread::spawn(move || {
                drop(jobs);
                let alias = small.clone(); drop(small);
                Links { first: large, second: alias }
            });
            let survivor = {
                let links = worker.join().unwrap();
                let kept = links.second;
                drop(links.first);
                kept
            };
            assert(current(memory) <= 57);
            drop(survivor);
            assert(current(memory) <= 2);
        }
        }
    "#;
    // The captured owning vector requires a checked transfer template.
    // Only n (2), one handle (8), control (16), Vec (24), and 7 bytes remain.
    let valid =
        crate::verify_one_file("worker_shared_result_paths", code.to_string(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let swapped = code.replace("first: large, second: alias", "first: alias, second: large");
    let error =
        crate::verify_one_file("worker_shared_result_paths_swapped", swapped, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}

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
