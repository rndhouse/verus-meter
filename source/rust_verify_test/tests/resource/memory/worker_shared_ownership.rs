//! Shared allocation identity and lifetime across worker captures, joins and drops.

use super::support::rejects;

const GLOBAL: &str = "checked worker effects still require global lifetime and interference proofs";

#[test]
fn a_receiving_actor_cannot_discharge_its_publishers_indexed_shared_claims() {
    rejects(
        "worker_population_strong_capture",
        r#"
        fn f() resources peak(memory) <= 2048 {
            let backing = std::sync::Arc::new(17u64);
            let alias = backing.clone();
            let mut handles = Vec::with_capacity(1);
            let child = std::thread::spawn(move || { drop(alias); 17u64 });
            handles.push(child);
            let collector = std::thread::spawn(move || {
                let mut pending = handles;
                let _value = pending.pop().unwrap().join().unwrap();
            });
            collector.join().unwrap();
            drop(backing);
        }
        "#,
        "collection of indexed shared claims outside their publishing coordinator",
    );
}

#[test]
fn a_symbolic_worker_population_reserves_each_shared_backing_once() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= n * 9 + 160 {
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
            if n == 2 { assert(current(memory) <= 70); }
            while handles.len() > 0 invariant handles.len() <= n, decreases handles.len(), {
                let h = handles.pop().unwrap();
                let _v = h.join().unwrap();
            }
            drop(handles);
            assert(current(memory) <= 4);
        }
        }
    "#;
    // 28 coordinator bytes, two 8-byte handle slots, two completion tags,
    // and a single 24-byte backing even with four captured strong handles.
    let valid =
        crate::verify_one_file("indexed_shared_backing", code.to_string(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let short =
        crate::verify_one_file("indexed_shared_backing_short", code.replace("<= 70", "<= 69"), &[])
            .unwrap_err();
    crate::common::assert_vir_error_msgs(short, &["conditional memory budget exceeded", GLOBAL]);
    // A different allocation with the same payload type needs its own backing.
    let distinct = code
        .replace("let mut handles", "let other = std::sync::Arc::new(17u64); let mut handles")
        .replace("let b = root.clone()", "let b = other.clone()")
        .replace("drop(root);", "drop(root); drop(other);");
    let error = crate::verify_one_file("indexed_distinct_backings", distinct, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
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
    for (name, exact, short) in [("pending", "<= 107", "<= 106"), ("joined", "<= 73", "<= 72")] {
        let error = crate::verify_one_file(name, code.replace(exact, short), &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["conditional memory budget exceeded", GLOBAL],
        );
    }

    // Incoming storage and nested strong references have lifetimes of their own.
    let buffer = "Vec::<u8>::with_capacity(b as usize)";
    for (name, program) in [
        ("nested_arc", code.replace(buffer, &format!("std::sync::Arc::new({buffer})"))),
        (
            "incoming_buffer",
            code.replace("b: u16)", "b: u16, buf: Vec<u8>)").replace(buffer, "buf"),
        ),
    ] {
        let error = crate::verify_one_file(name, program, &[]).unwrap_err();
        crate::common::assert_vir_error_msg(
            error,
            "indexed Arc payload with incoming storage or nested reference lifetimes",
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
    let escaped = code.replace(
        "drop(survivor);",
        "let child = std::thread::spawn(move || drop(survivor)); child.join().unwrap();",
    );
    let error = crate::verify_one_file("mixed_arc_escape", escaped, &[]).unwrap_err();
    crate::common::assert_vir_error_msg(error, "transferring a selected Arc across actors");
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
fn receiving_a_mixed_arc_result_requires_its_publishers_claim() {
    // Each family returns its only captured alias. The join keeps its claim
    // live in the result even when there is no net debit to either allocation.
    let collection = format!(
        "let collector = std::thread::spawn(move || {{
            let mut handles = handles;
            {FULL_DRAIN}
        }});
        collector.join().unwrap();"
    );
    let error = crate::verify_one_file(
        "mixed_arc_receiving_worker",
        mixed_arc_program("", DISJOINT_CAPTURES, &collection),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(
        error,
        "collection of indexed shared claims outside their publishing coordinator",
    );
}

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
