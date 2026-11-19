//! Captured handle slots keep their canonical backing in the publisher until join.
use super::{DISJOINT_CAPTURES, FULL_DRAIN, GLOBAL, mixed_arc_program};
use crate::common::{assert_vir_error_msg, assert_vir_error_msgs};
use crate::verify_one_file;

#[test]
fn collecting_worker_drains_symbolic_mixed_arc_results() {
    // Includes an empty publication loop. Each occupied slot returns exactly
    // one of two distinct allocations and the caller checks its final 4 bytes.
    let collection = format!(
        "let collector = std::thread::spawn(move || {{
        let mut handles = handles;
        {FULL_DRAIN}
    }});
    collector.join().unwrap();"
    );
    let uniform = DISJOINT_CAPTURES.replace("let c = large.clone()", "let c = small.clone()");
    for (name, captures) in [
        ("collect_mixed_roots", DISJOINT_CAPTURES),
        ("collect_one_root_multiple_families", uniform.as_str()),
    ] {
        let error =
            verify_one_file(name, mixed_arc_program("", captures, &collection), &[]).unwrap_err();
        assert_vir_error_msg(error, GLOBAL);
    }
}

#[test]
fn collecting_one_vector_keeps_the_siblings_shared_backing() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 2048 {
            let backing = std::sync::Arc::new(17u64);
            let alias = backing.clone();
            let mut handles = Vec::with_capacity(1);
            let child = std::thread::spawn(move || { drop(alias); 17u64 });
            handles.push(child);
            let sibling = backing.clone();
            let mut others = Vec::with_capacity(1);
            let other = std::thread::spawn(move || { drop(sibling); 17u64 });
            others.push(other);
            drop(backing);
            let collector = std::thread::spawn(move || {
                let mut pending = handles;
                assert(current(memory) <= 81);
                let _value = pending.pop().unwrap().join().unwrap();
            });
            collector.join().unwrap();
            assert(current(memory) <= 57);
            let peer = others.pop().unwrap();
            let _result = peer.join().unwrap();
            drop(others);
            assert(current(memory) <= 8);
        }
        }
    "#;
    let check = |name, program| verify_one_file(name, program, &[]).unwrap_err();
    assert_vir_error_msg(check("shared_collector", code.into()), GLOBAL);
    // The collector frame and one 24-byte Arc allocation coexist. Joining the
    // collector still leaves the sibling vector, completion tag and same Arc.
    for (name, from, to, message) in [
        ("collector_short", "<= 81", "<= 80", "at a worker checkpoint with shared backing"),
        ("sibling_short", "<= 57", "<= 56", "conditional memory budget exceeded"),
        (
            "collector_lost_vector",
            "let _value = pending.pop().unwrap().join().unwrap();",
            "drop(pending);",
            "cannot discard outstanding worker handles",
        ),
    ] {
        assert_vir_error_msgs(check(name, code.replace(from, to)), &[message, GLOBAL]);
    }
    // Both control blocks remain live through the same captured outer Arc.
    let nested = code
        .replace(
            "let backing = std::sync::Arc::new(17u64);",
            "let inner = std::sync::Arc::new(17u64); let backing = std::sync::Arc::new(inner);",
        )
        .replace("<= 81", "<= 105")
        .replace("<= 57", "<= 81");
    assert_vir_error_msg(check("collector_nested_checkpoint", nested.clone()), GLOBAL);
    assert_vir_error_msgs(
        check("collector_nested_short", nested.replace("<= 105", "<= 104")),
        &["at a worker checkpoint with shared backing", GLOBAL],
    );
    let scalar = code.replace(
        "let _value = pending.pop().unwrap().join().unwrap();",
        "pending.pop().unwrap().join().unwrap()",
    );
    assert_vir_error_msg(check("collector_returns_scalar", scalar), GLOBAL);
}

#[test]
fn publisher_can_drop_its_last_fixed_alias_before_collecting() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 2048 {
            let inner = std::sync::Arc::new(17u64);
            let backing = std::sync::Arc::new(inner);
            let alias = backing.clone();
            let mut handles = Vec::with_capacity(1);
            let worker = std::thread::spawn(move || drop(alias));
            handles.push(worker);
            let collector = std::thread::spawn(move || {
                let mut handles = handles;
                handles.pop().unwrap().join().unwrap();
            });
            drop(backing);
            assert(current(memory) <= 57);
            collector.join().unwrap();
            assert(current(memory) <= 0);
        }
        }
    "#;
    let error =
        verify_one_file("only_collector_retains_nested_arcs", code.into(), &[]).unwrap_err();
    assert_vir_error_msg(error, GLOBAL);
    let error =
        verify_one_file("premature_release_of_nested_arcs", code.replace("<= 57", "<= 56"), &[])
            .unwrap_err();
    assert_vir_error_msgs(error, &["live 57 bytes exceeds bound 56 bytes", GLOBAL]);
}

#[test]
fn collector_returns_the_remaining_handle_slots() {
    let collection = r#"
        let collector = std::thread::spawn(move || -> (r: Vec<std::thread::JoinHandle<std::sync::Arc<Vec<u8>>>>)
            ensures r.len() == keep
        {
            let mut batch = handles;
            while batch.len() > keep as usize
                invariant keep <= batch.len() <= 2 * n,
                decreases batch.len(),
            {
                let h = batch.pop().unwrap();
                drop(h.join().unwrap());
            }
            batch
        });
        let mut handles = collector.join().unwrap();
        if n == 1 && keep == 0 { assert(current(memory) <= 46); }
        if n == 1 && keep == 1 { assert(current(memory) <= 94); }
        if n == 1 && keep == 2 { assert(current(memory) <= 154); }
    "#;
    let program = mixed_arc_program(
        "requires keep <= 2 * n,",
        DISJOINT_CAPTURES,
        &format!("{collection}{FULL_DRAIN}"),
    )
    .replace("fn f(n: u16)", "fn f(n: u16, keep: u16)")
    .replace("memory) <= 4);", "memory) <= 6);");
    let check = |name, program| verify_one_file(name, program, &[]).unwrap_err();
    assert_vir_error_msg(check("collector_returns_slots", program.clone()), GLOBAL);
    assert_vir_error_msgs(
        check("collector_remainder_short", program.replace("<= 94", "<= 93")),
        &["conditional memory budget exceeded", GLOBAL],
    );
    // A concrete failing execution leaves one real handle. Its backing still
    // has an outstanding reference when the function exits.
    let lost = program
        .replace("requires keep <= 2 * n,", "requires n == 1, keep == 1,")
        .replace(FULL_DRAIN, "drop(handles);")
        .replace("assert(current(memory) <= 6);", "");
    assert_vir_error_msgs(
        check("lost_returned_slots", lost),
        &[
            "cannot discard outstanding worker handles",
            "outstanding shared worker claims at accounting scope exit",
            GLOBAL,
        ],
    );
}

#[test]
fn collected_arc_keeps_the_selected_workers_result_identity() {
    let collection = r#"
        let collector = std::thread::spawn(move || {
            let mut batch = handles;
            while batch.len() > 1 invariant 1 <= batch.len() <= 2 * n, decreases batch.len(), {
                let h = batch.pop().unwrap();
                drop(h.join().unwrap());
            }
            let link = batch.pop().unwrap().join().unwrap();
            drop(batch);
            link
        });
        let link = collector.join().unwrap();
        assert(current(memory) <= 59);
        drop(link);
    "#;
    let program = mixed_arc_program("requires n > 0,", DISJOINT_CAPTURES, collection);
    let check = |name, program| verify_one_file(name, program, &[]).unwrap_err();
    assert_vir_error_msg(check("collector_returns_first_arc", program), GLOBAL);
    // The same collector with one concrete pair gives a small counterexample.
    // Reversing its captures changes the surviving allocation from 47 to 59 bytes.
    let pair = format!(
        r#"
        use vstd::prelude::*;
        verus! {{
            fn f() resources peak(memory) <= 340 {{
                let n = 1u16;
                let small = std::sync::Arc::new(Vec::<u8>::with_capacity(7));
                let large = std::sync::Arc::new(Vec::<u8>::with_capacity(19));
                let mut handles = Vec::with_capacity(2);
                {DISJOINT_CAPTURES}
                drop(small); drop(large);
                {collection}
            }}
        }}
    "#
    )
    .replace("<= 59", "<= 57");
    assert_vir_error_msg(check("collector_fixed_pair", pair.clone()), GLOBAL);
    let switched = pair
        .replace("a = small.clone()", "a = large.clone()")
        .replace("c = large.clone()", "c = small.clone()");
    assert_vir_error_msgs(
        check("collector_returns_larger_arc", switched),
        &["conditional memory budget exceeded", GLOBAL],
    );
}
