//! Population tests use executable spawn, transfer and join operations. Local
//! obligations must run without lifting the global concurrent proof boundary.

use super::support::rejects;

const GLOBAL: &str = "checked worker effects still require global lifetime and interference proofs";

#[test]
fn scalar_worker_results_size_buffers_through_a_checked_helper() {
    rejects(
        "scalar_worker_helper_buffers",
        r#"
        fn buffer(size: u16) -> Vec<u8>
            resources peak(memory) <= size + 64
        {
            Vec::with_capacity(size as usize)
        }
        fn f(n: u16, keep: u16)
            requires keep <= n,
            resources peak(memory) <= n * 128 + 131072
        {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || i);
                handles.push(worker);
                i += 1;
            }
            while handles.len() > keep as usize
                invariant handles.len() <= n,
                decreases handles.len(),
            {
                let handle = handles.pop().unwrap();
                let moved = handle;
                let size = moved.join().unwrap();
                let storage = buffer(size);
                drop(storage);
            }
            while handles.len() > 0 decreases handles.len(), {
                let size = handles.pop().unwrap().join().unwrap();
                let storage = buffer(size);
                drop(storage);
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn scalar_worker_results_do_not_hide_an_oversized_allocation() {
    let source = r#"
        fn f(n: u16) resources peak(memory) <= n * 128 + 131072 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || i);
                handles.push(worker);
                i += 1;
            }
            while handles.len() > 0 decreases handles.len(), {
                let size = handles.pop().unwrap().join().unwrap();
                let storage = Vec::<u8>::with_capacity(size as usize + EXTRA);
                drop(storage);
            }
        }
        "#;
    rejects("scalar_worker_buffers", &source.replace("EXTRA", "0"), GLOBAL);
    let enlarged = source.replace("EXTRA", "200_000");
    let error = crate::verify_one_file(
        "scalar_worker_buffers_too_large",
        format!("use vstd::prelude::*; verus! {{ {enlarged} }}"),
        &[],
    )
    .unwrap_err();
    assert!(error.errors.iter().any(|error| error.message.contains("memory budget exceeded")));
    assert!(error.errors.iter().any(|error| error.message.contains(GLOBAL)));
    assert!(error.errors.iter().all(|error| {
        error.message.contains("memory budget exceeded") || error.message.contains(GLOBAL)
    }));
}

#[test]
fn scalar_worker_observations_preserve_boolean_and_signed_results() {
    let source = r#"
        fn size(value: TYPE) -> u16 resources peak(memory) <= 64 {
            if CONDITION { 64 } else { 32 }
        }
        fn f(n: u16) resources peak(memory) <= n * 128 + 131072 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || RESULT);
                handles.push(worker);
                i += 1;
            }
            while handles.len() > 0 decreases handles.len(), {
                let value = handles.pop().unwrap().join().unwrap();
                let amount = size(value);
                let storage = Vec::<u8>::with_capacity(amount as usize);
                drop(storage);
            }
        }
        "#;
    for (name, typ, condition, result) in [
        ("boolean_worker_results", "bool", "value", "i < 4"),
        ("signed_worker_results", "i16", "value < 0", "if i < 4 { -7i16 } else { 9i16 }"),
    ] {
        rejects(
            name,
            &source.replace("TYPE", typ).replace("CONDITION", condition).replace("RESULT", result),
            GLOBAL,
        );
    }
}

#[test]
fn unrepresented_scalar_results_cannot_supply_a_population_description() {
    // Array contents currently have no scalar transfer description. A mixed
    // family selection cannot borrow the known family's scalar observation.
    rejects(
        "unknown_scalar_worker_result",
        r#"
        fn f(n: u16) resources peak(memory) <= n * 256 + 131072 {
            let mut handles = Vec::with_capacity(2 * n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == 2 * i, decreases n - i, {
                let unknown = std::thread::spawn(move || {
                    let values = [7u16; 1];
                    values[0]
                });
                handles.push(unknown);
                let known = std::thread::spawn(move || i);
                handles.push(known);
                i += 1;
            }
            while handles.len() > 0 decreases handles.len(), {
                let size = handles.pop().unwrap().join().unwrap();
                let storage = Vec::<u8>::with_capacity(size as usize);
                drop(storage);
            }
        }
        "#,
        "no precise helper summary can be inferred",
    );
}

#[test]
fn scalar_worker_functional_proofs_support_input_dependent_allocations() {
    let source = r#"
        use vstd::std_specs::thread::JoinHandleSpec;
        fn f(n: u16) resources peak(memory) <= n * 128 + 512 {
            let mut handles: Vec<std::thread::JoinHandle<u16>> = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n
                invariant
                    i <= n,
                    handles.len() == i,
                    forall|j:int, value:u16| 0 <= j < handles.len()
                        && #[trigger] handles@[j].result_predicate(value) ==> value == j,
                decreases n - i,
            {
                let worker = std::thread::spawn(move || -> (result: u16)
                    ensures result == i { i });
                handles.push(worker);
                i += 1;
            }
            while handles.len() > 0
                invariant
                    handles.len() <= n,
                    forall|j:int, value:u16| 0 <= j < handles.len()
                        && #[trigger] handles@[j].result_predicate(value) ==> value == j,
                decreases handles.len(),
            {
                let size = handles.pop().unwrap().join().unwrap();
                let storage = Vec::<u8>::with_capacity(size as usize);
                drop(storage);
            }
        }
        "#;
    rejects("worker_scalar_functional_bounds", source, GLOBAL);
    // An explicit match must receive the selected occurrence even when Err
    // comes first. Its arm-local binding supplies the executable capacity.
    let matched = source.replace(
        "handles.pop().unwrap().join().unwrap()",
        "match handles.pop().unwrap().join() { Err(_) => 0u16, Ok(size) => size }",
    );
    rejects("worker_scalar_match_bounds", &matched, GLOBAL);

    let false_contract = source.replace("result == i { i }", "result == i { 2000u16 }");
    let error = crate::verify_one_file(
        "worker_scalar_false_contract",
        format!("use vstd::prelude::*; verus! {{ {false_contract} }}"),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msgs(
        error,
        &["unable to prove post-condition of closure", GLOBAL],
    );

    // Change the executable result and its functional proof together. The
    // unchanged allocation now exceeds the budget for small positive n.
    let enlarged = matched
        .replace("value == j", "value == 2000")
        .replace("result == i { i }", "result == 2000 { 2000u16 }");
    let error = crate::verify_one_file(
        "worker_scalar_functional_bounds_too_large",
        format!("use vstd::prelude::*; verus! {{ {enlarged} }}"),
        &[],
    )
    .unwrap_err();
    assert!(error.errors.iter().any(|error| error.message.contains("memory budget exceeded")));
    assert!(error.errors.iter().any(|error| error.message.contains(GLOBAL)));
    assert!(error.errors.iter().all(|error| {
        error.message.contains("memory budget exceeded") || error.message.contains(GLOBAL)
    }));
}

#[test]
fn mixed_worker_batches_preserve_each_result_during_partial_collection() {
    let source = r#"
        fn f(n: u16, keep: u16)
            requires keep <= n,
            resources peak(memory) <= n * 131072 + n * 256 + 1024
        {
            let mut handles = Vec::with_capacity(2 * n as usize);
            let mut i = 0u16;
            while i < n
                invariant i <= n, handles.len() == 2 * i,
                decreases n - i,
            {
                let first = std::thread::spawn(move || Vec::<u8>::with_capacity(i as usize));
                handles.push(first);
                let second = std::thread::spawn(move || Vec::<u8>::with_capacity(2 * i as usize + 17));
                handles.push(second);
                i += 1;
            }
            while handles.len() > keep as usize
                invariant handles.len() <= 2 * n,
                decreases handles.len(),
            {
                let handle = handles.pop().unwrap();
                let moved = handle;
                let result = moved.join().unwrap();
                drop(result);
            }
            while handles.len() > 0
                invariant handles.len() <= keep,
                decreases handles.len(),
            {
                let result = handles.pop().unwrap().join().unwrap();
                drop(result);
            }
        }
        "#;
    rejects("mixed_worker_batches", source, GLOBAL);

    // Change an executable allocation in the second family. Its result must
    // retain its own extent after either collection loop selects its handle.
    let enlarged = source.replace("2 * i as usize + 17", "2 * i as usize + 200_000");
    let error = crate::verify_one_file(
        "mixed_worker_batches_large_result",
        format!("use vstd::prelude::*; verus! {{ {enlarged} }}"),
        &[],
    )
    .unwrap_err();
    assert!(error.errors.iter().any(|error| error.message.contains("memory budget exceeded")));
    assert!(error.errors.iter().any(|error| error.message.contains(GLOBAL)));
    assert!(
        error.errors.iter().all(|error| error.message.contains("memory budget exceeded")
            || error.message.contains(GLOBAL))
    );
}

#[test]
fn symbolic_worker_collections_keep_their_own_family_and_results() {
    rejects(
        "symbolic_worker_families",
        r#"
        fn f(n: u16, keep: u16)
            requires keep <= n,
            resources peak(memory) <= n * 131072 + n * 256 + 1024
        {
            let mut left = Vec::with_capacity(n as usize);
            let mut right = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n
                invariant i <= n, left.len() == i, right.len() == i,
                decreases n - i,
            {
                let first = std::thread::spawn(move || Vec::<u8>::with_capacity(i as usize));
                left.push(first);
                let second = std::thread::spawn(move || Vec::<u8>::with_capacity(2 * i as usize + 17));
                right.push(second);
                i += 1;
            }
            while left.len() > keep as usize
                invariant left.len() <= n,
                decreases left.len(),
            {
                let handle = left.pop().unwrap();
                let moved = handle;
                let result = moved.join().unwrap();
                drop(result);
            }
            while right.len() > 0 decreases right.len(), {
                let result = right.pop().unwrap().join().unwrap();
                drop(result);
            }
            while left.len() > 0 decreases left.len(), {
                let result = left.pop().unwrap().join().unwrap();
                drop(result);
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn every_body_in_a_mixed_worker_population_keeps_its_allocation_checks() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 1024 {
            let mut handles = Vec::with_capacity(2);
            let small = std::thread::spawn(move || Vec::<u8>::with_capacity(8));
            handles.push(small);
            let large = std::thread::spawn(move || Vec::<u8>::with_capacity(4096));
            handles.push(large);
            while handles.len() > 0 decreases handles.len(), {
                let result = handles.pop().unwrap().join().unwrap();
                drop(result);
            }
        }
        }
    "#;
    let valid = crate::verify_one_file(
        "mixed_worker_sufficient_bound",
        source.replace("<= 1024", "<= 8192"),
        &[],
    )
    .unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let error =
        crate::verify_one_file("mixed_worker_large_result", source.into(), &[]).unwrap_err();
    assert!(error.errors.iter().any(|error| error.message.contains("memory budget exceeded")));
    assert!(error.errors.iter().all(|error| {
        error.message.contains("memory budget exceeded") || error.message.contains(GLOBAL)
    }));
}

#[test]
fn discarding_a_selected_mixed_family_handle_is_still_detach() {
    rejects(
        "mixed_worker_detach",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let mut handles = Vec::with_capacity(2);
            let first = std::thread::spawn(move || 7u64);
            handles.push(first);
            let second = std::thread::spawn(move || 9u64);
            handles.push(second);
            let selected = handles.pop().unwrap();
            drop(selected);
            let remaining = handles.pop().unwrap();
            let value = remaining.join().unwrap();
        }
        "#,
        "detached workers in a memory accounting scope",
    );
}

#[test]
fn a_collecting_worker_can_receive_a_selected_population_handle() {
    let code = r#"
        fn f(n: u16) resources peak(memory) <= n * 128 + 131072 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || i);
                handles.push(worker);
                i += 1;
            }
            while handles.len() > 0 decreases handles.len(), {
                let selected = handles.pop().unwrap();
                let collector = std::thread::spawn(move || selected.join().unwrap());
                let size = collector.join().unwrap();
                let storage = Vec::<u8>::with_capacity(size as usize);
                drop(storage);
            }
        }
    "#;
    rejects("worker_collects_selected_handle", code, GLOBAL);
    let detached = code.replace("selected.join().unwrap()", "{ drop(selected); 0u16 }");
    rejects("worker_detaches_selected_handle", &detached, "detached workers");
}

#[test]
fn a_worker_receives_and_drains_an_entire_symbolic_collection() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= n * 128 + 131072 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let child = std::thread::spawn(move || i);
                handles.push(child);
                i += 1;
            }
            let collector = std::thread::spawn(move || {
                let mut pending = handles;
                while pending.len() > 0 decreases pending.len(), {
                    let size = pending.pop().unwrap().join().unwrap();
                    let storage = Vec::<u8>::with_capacity(size as usize);
                    drop(storage);
                }
            });
            collector.join().unwrap();
        }
        }
    "#;
    let check = |name: &str, source: String, errors: &[&str]| {
        let error = crate::verify_one_file(name, source, &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(error, errors);
    };
    check("worker_receives_population", code.into(), &[GLOBAL]);
    let early_stop = code.replace("pending.len() > 0", "pending.len() > 1");
    check(
        "worker_leaves_handle",
        early_stop,
        &["cannot discard outstanding worker handles", GLOBAL],
    );
    let oversized = code.replace("capacity(size as usize)", "capacity(size as usize + 200_000)");
    check(
        "worker_received_population_over_budget",
        oversized,
        &["conditional memory budget exceeded", GLOBAL],
    );
}

#[test]
fn a_returned_population_is_drained_by_the_thread_that_joins_its_producer() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16, keep: u16)
            requires keep <= n,
            resources peak(memory) <= n * 128 + 131072
        {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let child = std::thread::spawn(move || Vec::<u8>::with_capacity(i as usize + 64));
                handles.push(child);
                i += 1;
            }
            let worker = std::thread::spawn(move || -> (result: Vec<std::thread::JoinHandle<Vec<u8>>>)
                ensures result.len() == keep
            {
                let mut batch = handles;
                while batch.len() > keep as usize
                    invariant keep <= batch.len() <= n,
                    decreases batch.len(),
                {
                    let completed = batch.pop().unwrap().join().unwrap();
                    drop(completed);
                }
                batch
            });
            DRAIN
        }
        }
    "#;
    let drain = r#"
            let mut pending = worker.join().unwrap();
            while pending.len() > 0 decreases pending.len(), {
                let completed = pending.pop().unwrap().join().unwrap();
                drop(completed);
            }
    "#;
    let transferred = format!(
        "let receiver = std::thread::spawn(move || {{ {drain} }}); let done = receiver.join().unwrap();"
    );
    for (name, body) in [("parent", drain), ("receiver", transferred.as_str())] {
        let source = code.replace("DRAIN", body);
        let verified =
            crate::verify_one_file(&format!("returned_population_{name}"), source.clone(), &[])
                .unwrap_err();
        crate::common::assert_vir_error_msg(verified, GLOBAL);
        let leak = source.replace("while pending.len() > 0", "while pending.len() > 1");
        let error = crate::verify_one_file(&format!("returned_population_{name}_lost"), leak, &[])
            .unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["cannot discard outstanding worker handles", GLOBAL],
        );
    }
}

#[test]
fn returned_workers_cannot_escape_the_outer_accounting_domain() {
    rejects(
        "pending_worker_result_escapes",
        r#"
        fn f() -> Vec<std::thread::JoinHandle<u8>> resources peak(memory) <= 1024 {
            let mut pending = Vec::with_capacity(1);
            let child = std::thread::spawn(move || 7u8);
            pending.push(child);
            let worker = std::thread::spawn(move || pending);
            worker.join().unwrap()
        }
        "#,
        "imported reference populations without checked occurrence descriptors",
    );
}

#[test]
fn a_returned_handle_keeps_its_own_worker_result() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 4096 {
            let mut handles = Vec::with_capacity(2);
            let small = std::thread::spawn(move || Vec::<u8>::with_capacity(64));
            let large = std::thread::spawn(move || Vec::<u8>::with_capacity(1024));
            handles.push(small);
            handles.push(large);
            let worker = std::thread::spawn(move || -> (result: Vec<std::thread::JoinHandle<Vec<u8>>>)
                ensures result.len() == 1
            {
                let mut pending = handles;
                let completed = pending.pop().unwrap().join().unwrap();
                drop(completed);
                pending
            });
            let mut rest = worker.join().unwrap();
            let buffer = rest.pop().unwrap().join().unwrap();
            drop(rest);
            assert(current(memory) <= 88);
            drop(buffer);
            assert(current(memory) <= 0);
        }
        }
    "#;
    let valid =
        crate::verify_one_file("returned_handle_keeps_small_buffer", code.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    // Same count, allocations and joins. Change which worker the caller receives.
    let swapped = code.replace(
        "handles.push(small);\n            handles.push(large);",
        "handles.push(large); handles.push(small);",
    );
    let error =
        crate::verify_one_file("returned_handle_keeps_large_buffer", swapped, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}

#[test]
fn transferring_two_producer_handles_preserves_each_publication() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 8192 {
            let mut small = Vec::with_capacity(1);
            let child = std::thread::spawn(move || Vec::<u8>::with_capacity(64));
            small.push(child);
            let mut large = Vec::with_capacity(1);
            let child = std::thread::spawn(move || Vec::<u8>::with_capacity(1024));
            large.push(child);
            let a = std::thread::spawn(move || -> (v: Vec<std::thread::JoinHandle<Vec<u8>>>)
                ensures v.len() == 1
            { small });
            let b = std::thread::spawn(move || -> (v: Vec<std::thread::JoinHandle<Vec<u8>>>)
                ensures v.len() == 1
            { large });

            let receiver = std::thread::spawn(move || {
                let mut discarded = FIRST.join().unwrap();
                let first = discarded.pop().unwrap().join().unwrap();
                drop(first);
                drop(discarded);
                let mut retained = SECOND.join().unwrap();
                let second = retained.pop().unwrap().join().unwrap();
                drop(retained);
                second
            });
            let buffer = receiver.join().unwrap();
            assert(current(memory) <= 88);
            drop(buffer);
            assert(current(memory) <= 0);
        }
        }
    "#;
    for (first, second, expected) in
        [("b", "a", vec![GLOBAL]), ("a", "b", vec!["conditional memory budget exceeded", GLOBAL])]
    {
        let source = code.replace("FIRST", first).replace("SECOND", second);
        let error =
            crate::verify_one_file(&format!("receive_population_from_{second}"), source, &[])
                .unwrap_err();
        crate::common::assert_vir_error_msgs(error, &expected);
    }
}

#[test]
fn a_worker_returns_the_selected_buffer_from_a_captured_collection() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 4096 {
            let mut handles = Vec::with_capacity(2);
            let a = std::thread::spawn(move || Vec::<u8>::with_capacity(64));
            handles.push(a);
            let b = std::thread::spawn(move || Vec::<u8>::with_capacity(1024));
            handles.push(b);
            let collector = std::thread::spawn(move || {
                let mut pending = handles;
                let large = pending.pop().unwrap().join().unwrap();
                let small = pending.pop().unwrap().join().unwrap();
                drop(large);
                small
            });
            let result = collector.join().unwrap();
            assert(current(memory) <= 88);
            drop(result);
            assert(current(memory) <= 0);
        }
        }
    "#;
    let valid =
        crate::verify_one_file("worker_returns_small_buffer", code.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    // Keep both allocations and both joins. Only change which result survives.
    let large = code
        .replace("drop(large);", "drop(small);")
        .replace("                small\n", "                large\n");
    let error = crate::verify_one_file("worker_returns_large_buffer", large, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}

#[test]
fn a_buffer_keeps_its_allocation_across_two_worker_joins() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= 4096 {
            let mut handles = Vec::with_capacity(1);
            let child = std::thread::spawn(move || Vec::<u8>::with_capacity(1024));
            handles.push(child);
            let selected = handles.pop().unwrap();
            drop(handles);
            let collector = std::thread::spawn(move || selected.join().unwrap());
            let result = collector.join().unwrap();
            assert(current(memory) <= 1048);
            drop(result);
            assert(current(memory) <= 0);
        }
        }
    "#;
    let valid = crate::verify_one_file("worker_double_join_buffer", code.into(), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(valid, GLOBAL);
    let enlarged = code.replace("with_capacity(1024)", "with_capacity(1025)");
    let error =
        crate::verify_one_file("worker_double_join_buffer_short", enlarged, &[]).unwrap_err();
    crate::common::assert_vir_error_msgs(error, &["conditional memory budget exceeded", GLOBAL]);
}

#[test]
fn retained_workers_keep_each_construction_until_collection() {
    rejects(
        "retained_worker_inputs",
        r#"
        fn f(n: u16) resources peak(memory) <= n * 65536 + n * 128 + 512 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || Vec::<u8>::with_capacity(i as usize));
                handles.push(worker);
                i += 1;
            }
            while handles.len() > 0 decreases handles.len(), {
                let worker = handles.pop().unwrap();
                let result = worker.join().unwrap();
                drop(result);
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn partial_collection_preserves_the_remaining_worker_observations() {
    rejects(
        "partial_worker_collection",
        r#"
        fn f(n: u16, keep: u16)
            requires keep <= n,
            resources peak(memory) <= n * 65536 + n * 128 + 512
        {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || Vec::<u8>::with_capacity(i as usize));
                handles.push(worker);
                i += 1;
            }
            while handles.len() > keep as usize
                invariant handles.len() <= n,
                decreases handles.len(),
            {
                let worker = handles.pop().unwrap();
                let moved = worker;
                let result = moved.join().unwrap();
                drop(result);
            }
            while handles.len() > 0 decreases handles.len(), {
                let worker = handles.pop().unwrap();
                let result = worker.join().unwrap();
                drop(result);
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn retained_workers_still_check_executable_allocation_sizes() {
    let error = crate::verify_one_file(
        "retained_worker_large_result",
        r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= n * 65536 + n * 128 + 512 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || Vec::<u8>::with_capacity(200_000));
                handles.push(worker);
                i += 1;
            }
            while handles.len() > 0 decreases handles.len(), {
                let worker = handles.pop().unwrap();
                let result = worker.join().unwrap();
                drop(result);
            }
        }
        }
        "#
        .to_string(),
        &[],
    )
    .unwrap_err();
    assert!(error.errors.iter().any(|error| error.message.contains("memory budget exceeded")));
    assert!(error.errors.iter().any(|error| error.message.contains(GLOBAL)));
    assert!(
        error.errors.iter().all(|error| error.message.contains("memory budget exceeded")
            || error.message.contains(GLOBAL))
    );
}

#[test]
fn discarding_a_collection_cannot_retire_its_workers() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= n * 128 + 512 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || 7u64);
                handles.push(worker);
                i += 1;
            }
            CLEANUP
        }
        }
        "#;
    // Each form must observe the final collection, not its empty declaration.
    for (name, cleanup) in [
        ("discard_retained_workers", "drop(handles);"),
        ("implicitly_discard_retained_workers", ""),
        ("return_discards_retained_workers", "return;"),
    ] {
        let error =
            crate::verify_one_file(name, source.replace("CLEANUP", cleanup), &[]).unwrap_err();
        crate::common::assert_vir_error_msgs(
            error,
            &["cannot discard outstanding worker handles", GLOBAL],
        );
    }
}

#[test]
fn return_operand_collects_workers_before_lexical_cleanup() {
    rejects(
        "return_collects_retained_workers",
        r#"
        fn f(n: u16) -> u64 resources peak(memory) <= n * 65536 + n * 128 + 512 {
            let mut handles = Vec::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n invariant i <= n, handles.len() == i, decreases n - i, {
                let worker = std::thread::spawn(move || Vec::<u8>::with_capacity(i as usize));
                handles.push(worker);
                i += 1;
            }
            return {
                while handles.len() > 0 decreases handles.len(), {
                    let worker = handles.pop().unwrap();
                    let result = worker.join().unwrap();
                    drop(result);
                }
                7u64
            };
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn extraction_checks_the_current_join_result_extent() {
    let code = r#"
        use vstd::prelude::*;
        verus! {
        fn f() resources peak(memory) <= LIMIT {
            let handle = std::thread::spawn(move || Vec::<u8>::with_capacity(64));
            let result = handle.join().unwrap(); drop(result);
        }
        }
    "#;
    let accepted =
        crate::verify_one_file("join_overlap", code.replace("LIMIT", "113"), &[]).unwrap_err();
    crate::common::assert_vir_error_msg(accepted, GLOBAL);
    let rejected = crate::verify_one_file("join_overlap_short", code.replace("LIMIT", "112"), &[])
        .unwrap_err();
    crate::common::assert_vir_error_msgs(rejected, &["memory budget exceeded", GLOBAL]);
}

#[test]
fn repeated_constructions_bind_each_source_iteration() {
    rejects(
        "repeated_worker_inputs",
        r#"
        fn f(n: u16) resources peak(memory) <= n + 512 {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let worker = move || Vec::<u8>::with_capacity(i as usize);
                let handle = std::thread::spawn(worker);
                let result = handle.join().unwrap(); drop(result);
                i += 1;
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn repeated_workers_cannot_hide_body_allocations() {
    let error = crate::verify_one_file(
        "repeated_worker_hidden_allocation",
        r#"
        use vstd::prelude::*;
        verus! {
        fn f(n: u16) resources peak(memory) <= 128 {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let handle = std::thread::spawn(move || {
                    let extra = Box::new([0u8; 256]); drop(extra);
                });
                let result = handle.join().unwrap();
                i += 1;
            }
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
fn transferring_a_handle_cannot_hide_detach_in_its_receiver() {
    rejects(
        "captured_worker_detach",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let producer = std::thread::spawn(move || Box::new([0u8; 16]));
            let collector = std::thread::spawn(move || { drop(producer); });
            let result = collector.join();
        }
        "#,
        "detached workers",
    );
}

#[test]
fn nested_worker_loop_contexts_are_independent() {
    rejects(
        "nested_worker_loops",
        r#"
        fn f(n: u16) resources peak(memory) <= 2048 {
            let mut i = 0u16;
            while i < n invariant i <= n, decreases n - i, {
                let outer = std::thread::spawn(move || {
                    let mut j = 0u16;
                    while j < i invariant j <= i, decreases i - j, {
                        let child = std::thread::spawn(move || Box::new([0u8; 16]));
                        let result = child.join().unwrap(); drop(result);
                        j += 1;
                    }
                });
                let result = outer.join().unwrap();
                i += 1;
            }
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn nested_workers_join_their_actual_children() {
    rejects(
        "nested_worker_results",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let outer = std::thread::spawn(move || {
                let child = std::thread::spawn(move || Box::new([0u8; 16]));
                let waiting = Box::new([0u8; 32]);
                let result = child.join().unwrap();
                drop(waiting); result
            });
            let result = outer.join().unwrap(); drop(result);
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn nested_construction_moves_the_actual_outer_capture() {
    rejects(
        "nested_worker_owned_capture",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let input = Box::new([0u8; 16]);
            let outer = std::thread::spawn(move || {
                let child = std::thread::spawn(move || input);
                child.join().unwrap()
            });
            let result = outer.join().unwrap(); drop(result);
        }
        "#,
        GLOBAL,
    );
}

#[test]
fn nested_workers_cannot_discard_unjoined_descendants() {
    rejects(
        "nested_worker_detach",
        r#"
        fn f() resources peak(memory) <= 1024 {
            let outer = std::thread::spawn(move || {
                let child = std::thread::spawn(move || Box::new([0u8; 16]));
                drop(child);
            });
            let result = outer.join();
        }
        "#,
        "detached workers",
    );
}
