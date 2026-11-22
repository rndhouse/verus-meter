//! Acquisition-relative contents of an owning payload shared by fixed workers.
use super::rejects;

mod joined;
mod repeated;

/// Local checks still run when the domain lacks its global interference proof.
fn diagnostics(name: &str, program: &str, expected: &[&str]) {
    let source = format!("use vstd::prelude::*; verus! {{ {program} }}");
    // An unresolved dynamic peak can precede a release in the same closure.
    // Continue checking to catch an independent failure to conserve its bytes.
    let err = crate::verify_one_file(name, source, &["--multiple-errors=16"]).unwrap_err();
    let messages: Vec<_> = err.errors.iter().map(|d| d.message.as_str()).collect();
    for text in expected {
        assert!(messages.iter().any(|msg| msg.contains(text)), "{}: {:?}", text, messages);
    }
    assert!(
        messages.iter().all(|msg| expected.iter().any(|text| msg.contains(text))),
        "{:?}",
        messages
    );
}

const TWO_WRITERS: &str = r#"
    HELPER
    fn work() resources peak(memory) <= 4096 {
        let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));
        ALIASES
        let producer = std::thread::spawn(move || {
            let r = peer.lock();
            if r.is_err() { return; }
            let mut guard = r.unwrap();
            INSERT
        });
        let consumer = std::thread::spawn(move || {
            let r = cell.lock();
            if r.is_err() { return; }
            let mut guard = r.unwrap();
            let removed = guard.pop();
            drop(guard);
            drop(removed);
        });
        JOINS
    }
"#;

enum Write {
    Push,
    Call,
    ReplaceAndPush,
}

fn writers(write: Write, aliases: &str, joins: &str) -> String {
    let (helper, insert) = match write {
        Write::Call => (
            r#"fn insert(g: &mut std::sync::MutexGuard<'_, Vec<Box<[u8; 32]>>>, item: Box<[u8; 32]>)
                resources peak(memory) <= 128 { g.push(item); }"#,
            "let item = Box::new([1u8; 32]); insert(&mut guard, item);",
        ),
        Write::Push => ("", "guard.push(Box::new([1u8; 32]));"),
        Write::ReplaceAndPush => (
            "",
            r#"
            *guard = Vec::new();
            guard.push(Box::new([1u8; 32]));
            assert(current(memory) <= LIMIT);
        "#,
        ),
    };
    TWO_WRITERS
        .replace("HELPER", helper)
        .replace("ALIASES", aliases)
        .replace("INSERT", insert)
        .replace("JOINS", joins)
}

const ALIAS: &str = "let peer = cell.clone();";
const REVERSED: &str = "let second = consumer.join(); let first = producer.join();";
const SAME: &str = "checked acquisitions = 2, distinct mutexes = 1";
const LINKED: &str = "distinct mutexes = 1, linked acquisitions = 2";
const CHECKPOINT: &str = "at a worker checkpoint with shared backing";

#[test]
fn direct_and_factored_writes_share_the_cell_independently_of_join_order() {
    diagnostics("direct_writers", &writers(Write::Push, ALIAS, REVERSED), &[LINKED]);
    let joins = "let first = producer.join(); let second = consumer.join();";
    diagnostics(
        "factored_writers",
        &writers(Write::Call, ALIAS, joins),
        &[LINKED, "mutex intervals awaiting global"],
    );
}

#[test]
fn different_mutex_allocations_of_the_same_type_keep_independent_contents() {
    let aliases = r#"
        let other = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));
        let peer = other.clone();
        let keep = cell.clone();
    "#;
    let program = writers(Write::Push, aliases, REVERSED).replace(
        "let removed = guard.pop();",
        "let removed = guard.pop(); assert(current(memory) <= LIMIT);",
    );
    // The other mutex received the box. Only the frame, Arc and empty Option
    // remain at this consumer's checkpoint.
    let distinct = "distinct mutexes = 2, linked acquisitions = 2";
    diagnostics("distinct_writers", &program.replace("LIMIT", "74"), &[distinct]);
    diagnostics("distinct_writers_short", &program.replace("LIMIT", "73"), &[distinct, CHECKPOINT]);
}

#[test]
fn a_pop_can_receive_the_preceding_holders_box_in_either_join_order() {
    let at = |joins: &str, bound: u32| {
        writers(Write::Push, ALIAS, joins).replace(
            "let removed = guard.pop();",
            &format!("let removed = guard.pop(); assert(current(memory) <= {bound});"),
        )
    };
    // The mutex is empty after this pop in either order. If the push ran
    // first, the removed 32 bytes are now in the Option. 74 + 32 = 106.
    for (name, joins) in
        [("forward", "let a = producer.join(); let b = consumer.join();"), ("reverse", REVERSED)]
    {
        diagnostics(&format!("pop_{name}"), &at(joins, 106), &[LINKED]);
        diagnostics(&format!("pop_{name}_short"), &at(joins, 105), &[LINKED, CHECKPOINT]);
    }
}

#[test]
fn a_shared_vector_keeps_its_explicit_reservation_across_acquisitions() {
    let program =
        writers(Write::Push, ALIAS, REVERSED).replace(">>::new()", ">>::with_capacity(3)").replace(
            "guard.push(Box::new([1u8; 32]));",
            "guard.push(Box::new([1u8; 32])); assert(current(memory) <= LIMIT);",
        );
    // 16 frame + 49 Arc + 24 reserved slots + 32 box payload.
    diagnostics("reserved_exact", &program.replace("LIMIT", "121"), &[LINKED]);
    diagnostics("reserved_short", &program.replace("LIMIT", "120"), &[LINKED, CHECKPOINT]);
}

#[test]
fn a_worker_receives_a_reservation_chosen_by_another_workers_capture() {
    let program = writers(Write::Push, ALIAS, REVERSED)
        .replace("fn work()", "fn work(n: u8)")
        .replace("guard.push", "*guard = Vec::with_capacity(n as usize); guard.push")
        .replace(
            "let removed = guard.pop();",
            "let removed = guard.pop(); assert(current(memory) <= LIMIT);",
        );
    // The consumer never captures n. Its worst case is the popped box and
    // 255 explicitly reserved pointer slots in the mutex: 106 + 255 * 8.
    diagnostics("captured_slots_exact", &program.replace("LIMIT", "2146"), &[LINKED]);
    diagnostics("captured_slots_short", &program.replace("LIMIT", "2145"), &[LINKED, CHECKPOINT]);
}

#[test]
fn a_replacement_and_the_preceding_workers_box_can_be_live_together() {
    let program = writers(Write::Push, ALIAS, REVERSED).replace(
        "let removed = guard.pop();",
        r#"let removed = guard.pop();
           let next = Box::new([9u8; 32]);
           assert(current(memory) <= LIMIT);
           guard.push(next);"#,
    );
    // The removed Option can still own 32 bytes when the new 40-byte box
    // (pointer plus allocation) becomes live.
    diagnostics("both_boxes_exact", &program.replace("LIMIT", "146"), &[LINKED]);
    diagnostics("both_boxes_short", &program.replace("LIMIT", "145"), &[LINKED, CHECKPOINT]);
}

#[test]
fn two_preceding_pushes_can_leave_a_box_in_the_mutex_after_a_pop() {
    let aliases = format!("{ALIAS} let extra = cell.clone();");
    let joins = format!("{REVERSED} let third = another.join();");
    let program = writers(Write::Push, &aliases, &joins)
        .replace(
            "let consumer =",
            r#"let another = std::thread::spawn(move || {
                   let r = extra.lock();
                   if r.is_err() { return; }
                   let mut guard = r.unwrap();
                   guard.push(Box::new([2u8; 32]));
               });
               let consumer ="#,
        )
        .replace(
            "let removed = guard.pop();",
            "let removed = guard.pop(); assert(current(memory) <= LIMIT);",
        );
    // One remaining slot and its box add 40 bytes to the 106-byte pop.
    let linked = "distinct mutexes = 1, linked acquisitions = 3";
    diagnostics("two_prior_pushes", &program.replace("LIMIT", "146"), &[linked]);
    diagnostics("two_prior_pushes_short", &program.replace("LIMIT", "145"), &[linked, CHECKPOINT]);
}

#[test]
fn an_unresolved_initial_vector_cannot_be_treated_as_empty() {
    let program = writers(Write::Push, ALIAS, REVERSED)
        .replace(
            "let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));",
            r#"let mut initial = Vec::<Box<[u8; 32]>>::new();
               initial.push(Box::new([2u8; 32]));
               let cell = std::sync::Arc::new(std::sync::Mutex::new(initial));"#,
        )
        .replace(
            "guard.push(Box::new([1u8; 32]));",
            "guard.push(Box::new([1u8; 32])); assert(current(memory) <= 105);",
        );
    diagnostics(
        "unresolved_initial_contents",
        &program,
        &[
            "linked acquisitions = 0",
            // The caller also receives an unrestricted surviving backing at join.
            "conditional memory budget exceeded: cannot prove the required model bytes",
            "conditional memory budget exceeded during worker",
            CHECKPOINT,
        ],
    );
}

#[test]
fn a_dynamic_payload_cannot_be_priced_or_extracted_from_its_initial_state() {
    // This worker never dereferences the guard. Its checkpoint is seen before
    // the analysis encounters the later writer that can change its backing.
    let reader = r#"
        fn observe() resources peak(memory) <= 4096 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));
            let peer = cell.clone();
            let reader = std::thread::spawn(move || {
                let held = peer.lock();
                assert(current(memory) <= 512);
                drop(held);
            });
            OTHER
            let done = reader.join();
        }
    "#;
    rejects(
        "reader_of_unchanged_cell",
        &reader.replace("OTHER", "drop(cell);"),
        "checked worker effects still require global",
    );
    let writer = r#"
        let writer = std::thread::spawn(move || {
            let r = cell.lock();
            if r.is_err() { return; }
            let mut guard = r.unwrap();
            guard.push(Box::new([0u8; 32]));
        });
        let wrote = writer.join();
    "#;
    rejects(
        "checkpoint_before_peer_write",
        &reader.replace("OTHER", writer),
        "a worker checkpoint requiring the current shared payload",
    );
    let aliases = format!("{ALIAS} let keep = cell.clone();");
    let observe = format!("{REVERSED} assert(current(memory) <= 512); drop(keep);");
    diagnostics(
        "coordinator_observes_after_joins",
        &writers(Write::Push, &aliases, &observe),
        &[LINKED],
    );
    let joins = format!("{REVERSED} let recovered = std::sync::Arc::into_inner(keep);");
    diagnostics("coordinator_after_both_joins", &writers(Write::Push, &aliases, &joins), &[LINKED]);
}

#[test]
fn a_fixed_payload_is_counted_once_both_inside_and_outside_the_guard() {
    let program = r#"
        fn work() resources peak(memory) <= 4096 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Box::new([0u8; 32])));
            let peer = cell.clone();
            let first = std::thread::spawn(move || {
                assert(current(memory) <= OUTSIDE);
                let r = peer.lock();
                if r.is_err() { return; }
                let mut guard = r.unwrap();
                *guard = Box::new([1u8; 32]);
                assert(current(memory) <= INSIDE);
            });
            let second = std::thread::spawn(move || {
                let r = cell.lock();
                if r.is_err() { return; }
                let mut guard = r.unwrap();
                *guard = Box::new([2u8; 32]);
            });
            let b = second.join();
            let a = first.join();
        }
    "#;
    // 8 capture bytes + 33 bytes for the Arc backing and inline mutex/box
    // + 32 separately allocated bytes. The guard costs another 8 bytes.
    let at = |outside, inside| program.replace("OUTSIDE", outside).replace("INSIDE", inside);
    rejects("fixed_payload_exact", &at("73", "81"), SAME);
    diagnostics(
        "fixed_payload_before_lock_short",
        &at("72", "81"),
        &[SAME, "73 bytes exceeds budget 72 bytes"],
    );
    diagnostics(
        "fixed_payload_inside_lock_short",
        &at("73", "80"),
        &[SAME, "81 bytes exceeds budget 80 bytes"],
    );
}

#[test]
fn replacing_a_variable_sized_payload_gives_a_tight_bound_while_locked() {
    let program = writers(Write::ReplaceAndPush, ALIAS, REVERSED);
    // 16 bytes of frame, 49 of Arc backing and 40 for one occupied Vec slot
    // plus its box payload. A replacement leaves one box under either lock order.
    diagnostics("replaced_vector_exact", &program.replace("LIMIT", "105"), &[LINKED]);
    diagnostics("replaced_vector_short", &program.replace("LIMIT", "104"), &[LINKED, CHECKPOINT]);
}

#[test]
fn a_single_writer_starts_from_the_shared_vectors_published_contents() {
    diagnostics(
        "shared_guarded_vector_requires_an_interference_summary",
        r#"
        fn f() resources peak(memory) <= 2000 {
            let m = std::sync::Arc::new(std::sync::Mutex::new(Vec::<u8>::new()));
            let peer = std::sync::Arc::clone(&m);
            let child = std::thread::spawn(move || {
                let result = peer.lock();
                if result.is_err() { return; }
                let mut guard = result.unwrap();
                guard.push(1u8);
            });
            let done = child.join();
            drop(m);
        }
    "#,
        &["distinct mutexes = 1, linked acquisitions = 1"],
    );
}

#[test]
fn passing_a_guard_through_two_helpers_publishes_at_the_consuming_call() {
    let program = r#"
        type Guard<'a> = std::sync::MutexGuard<'a, Box<[u8; 32]>>;
        fn finish(g: Guard<'_>) resources peak(memory) <= 32 { drop(g); }
        fn forward(g: Guard<'_>) resources peak(memory) <= 64 { finish(g); }
        fn work() resources peak(memory) <= 4096 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Box::new([0u8; 32])));
            let peer = cell.clone();
            let job = std::thread::spawn(move || {
                let r = peer.lock();
                if r.is_err() { return; }
                let mut guard = r.unwrap();
                *guard = Box::new([1u8; 32]);
                forward(guard);
                assert(current(memory) <= LIMIT);
            });
            let done = job.join();
            drop(cell);
        }
    "#;
    let pending = "checked acquisitions = 1, distinct mutexes = 1";
    diagnostics(
        "nested_guard_release",
        &program.replace("LIMIT", "73"),
        &[pending, "mutex intervals awaiting global"],
    );
    diagnostics(
        "nested_guard_release_short",
        &program.replace("LIMIT", "72"),
        &[pending, "mutex intervals awaiting global", "73 bytes exceeds budget 72 bytes"],
    );
}

#[test]
fn an_extracted_mutex_carries_the_last_written_contents_on_normal_return() {
    // The standard functional specs leave both unwrap preconditions to the user.
    // Even on that normal exit the caller must cover the box inserted by this helper.
    let program = r#"
        fn recover() -> (m: std::sync::Mutex<Vec<Box<[u8; 32]>>>) resources peak(memory) <= 512 {
            let a = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));
            let peer = a.clone();
            let r = peer.lock();
            let mut g = r.unwrap();
            g.push(Box::new([0u8; 32]));
            drop(g);
            drop(peer);
            let recovered = std::sync::Arc::into_inner(a);
            recovered.unwrap()
        }
        fn work() resources peak(memory) <= 1024 {
            let m = recover();
            assert(current(memory) <= LIMIT);
        }
    "#;
    diagnostics(
        "extract_written_contents",
        &program.replace("LIMIT", "73"),
        &["precondition not satisfied", "mutex intervals awaiting global"],
    );
    diagnostics(
        "extract_written_contents_short",
        &program.replace("LIMIT", "72"),
        &[
            "precondition not satisfied",
            "mutex intervals awaiting global",
            "conditional memory budget exceeded",
        ],
    );
}

#[test]
fn try_lock_only_opens_the_payload_on_the_path_that_accesses_it() {
    let program = r#"
        fn work() resources peak(memory) <= 4096 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<Box<[u8; 32]>>::new()));
            let peer = cell.clone();
            let writer = std::thread::spawn(move || {
                match peer.try_lock() {
                    Ok(mut guard) => { guard.push(Box::new([1u8; 32])); },
                    Err(std::sync::TryLockError::WouldBlock) => {},
                    Err(std::sync::TryLockError::Poisoned(poison)) => { drop(poison); },
                }
            });
            let done = writer.join();
            drop(cell);
        }
    "#;
    diagnostics("try_lock_payload", program, &["distinct mutexes = 1, linked acquisitions = 1"]);
}

#[test]
fn an_inner_vector_argument_cannot_supply_the_type_of_the_whole_shared_cell() {
    rejects(
        "borrow_inside_boxed_payload",
        r#"
        fn append(v: &mut Vec<u8>) resources peak(memory) <= 64 { v.push(1u8); }
        fn work() resources peak(memory) <= 4096 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Box::new(Vec::<u8>::new())));
            let peer = cell.clone();
            let writer = std::thread::spawn(move || {
                let r = peer.lock();
                if r.is_err() { return; }
                let mut guard = r.unwrap();
                append(&mut **guard);
            });
            let done = writer.join();
        }
        "#,
        "a guard view inconsistent with its captured mutex payload",
    );
}
