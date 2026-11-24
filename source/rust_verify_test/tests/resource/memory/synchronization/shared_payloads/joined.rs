//! Direct native joins transport the selected child and the rest of the mutex
//! along the same release history, including early returns without an allocation.
use super::{CHECKPOINT, LINKED, diagnostics};

const BUDGET: &str = "conditional memory budget exceeded";

/// Either lock can run first. The receiver keeps a strong alias until both joins.
fn workers(element: &str, initial: &str, write: &str, remove: &str, receipt: &str) -> String {
    format!(
        r#"
        fn work() resources peak(memory) <= 4096 {{
            let cell = std::sync::Arc::new(std::sync::Mutex::new(Vec::<{element}>::{initial}));
            let keep = cell.clone();
            let peer = cell.clone();
            let producer = std::thread::spawn(move || {{
                let r = peer.lock();
                if r.is_err() {{ return; }}
                let mut guard = r.unwrap();
                {write}
            }});
            let consumer = std::thread::spawn(move || {{
                let r = cell.lock();
                if r.is_err() {{ return None; }}
                let mut guard = r.unwrap();
                {remove}
                drop(guard);
                item
            }});
            {receipt}
        }}
    "#
    )
}

const INSERT: &str = "guard.push(Box::new([1u8; 32]));";
const REMOVE: &str = "let item = guard.pop(); assert(current(memory) <= 106);";
const RECEIPT: &str = r#"
    let second = consumer.join();
    let first = producer.join();
    drop(first);
    assert(second.is_ok());
    let kept = second.unwrap();
    drop(keep);
    assert(current(memory) <= 41);
    drop(kept);
    assert(current(memory) <= 0);
"#;

/// The flag stays live in the joining frame. A successful pop carries its
/// 32-byte allocation independently of the mutex and both join handles.
#[test]
fn conditional_writes_survive_nested_consuming_helpers_and_join() {
    let guard = "type G<'a> = std::sync::MutexGuard<'a, Vec<Box<[u8; 32]>>>;";
    let helpers = format!(
        r#"
        {guard}
        fn finish(mut g: G<'_>, insert: bool) resources peak(memory) <= 512 {{
            if insert {{ g.push(Box::new([1u8; 32])); }} drop(g);
        }}
        fn forward(g: G<'_>, insert: bool) resources peak(memory) <= 1024 {{ finish(g, insert); }}
    "#
    );
    for (case, functions, write) in [
        ("direct", "", "if insert { guard.push(Box::new([1u8; 32])); }"),
        ("early", "", "if !insert { return; } guard.push(Box::new([1u8; 32]));"),
        ("nested", helpers.as_str(), "forward(guard, insert);"),
    ] {
        let receipt = RECEIPT.replace("assert(current(memory) <= 41);",
            "if insert { assert(current(memory) <= 42); } else { assert(current(memory) <= 10); }")
            .replace("<= 0", "<= 1");
        let body = workers("Box<[u8; 32]>", "new()", write, REMOVE, &receipt)
            .replace("fn work()", "fn work(insert: bool)");
        let program = format!("{functions} {body}");
        let mut expected = vec![LINKED];
        if !functions.is_empty() {
            expected.push("mutex intervals awaiting global");
        }
        diagnostics(&format!("conditional_{case}"), &program, &expected);
        expected.push(BUDGET);
        diagnostics(
            &format!("conditional_{case}_short"),
            &program.replace("<= 42", "<= 41"),
            &expected,
        );
    }
}

#[test]
fn a_conditional_guard_handoff_preserves_the_open_payload_on_its_some_arm() {
    let helper = r#"
        type G<'a> = std::sync::MutexGuard<'a, Vec<Box<[u8; 32]>>>;
        fn handoff<'a>(mut g: G<'a>, keep: bool) -> Option<G<'a>> resources peak(memory) <= 512 {
            g.push(Box::new([1u8; 32]));
            if keep { Some(g) } else { drop(g); None }
        }
    "#;
    let receipt = RECEIPT.replace("<= 41", "<= 42").replace("<= 0", "<= 1");
    for (name, action) in [
        (
            "match",
            "match returned { Some(mut held) => { let old = held.pop(); drop(old); drop(held); }, None => {} }",
        ),
        ("drop", "drop(returned);"),
    ] {
        let write = format!("let returned = handoff(guard, keep_guard); {action}");
        let body = workers("Box<[u8; 32]>", "new()", &write, REMOVE, &receipt)
            .replace("fn work()", "fn work(keep_guard: bool)");
        let program = format!("{helper} {body}");
        diagnostics(
            &format!("handoff_{name}"),
            &program,
            &[LINKED, "mutex intervals awaiting global"],
        );
        diagnostics(
            &format!("handoff_{name}_short"),
            &program.replace("<= 42", "<= 41"),
            &[LINKED, "mutex intervals awaiting global", BUDGET],
        );
    }
}

#[test]
fn a_helper_return_selects_the_escaped_allocation_and_the_remaining_cell_together() {
    let receipt = RECEIPT
        .replace(
            "assert(current(memory) <= 41);",
            "if take { assert(current(memory) <= 42); } else { assert(current(memory) <= 10); }",
        )
        .replace("<= 0", "<= 1");
    let body = workers("Box<[u8; 32]>", "new()", INSERT, "let item = pull(guard, take);", &receipt)
        .replace("fn work()", "fn work(take: bool)")
        .replace("drop(guard);", "");
    let helper = r#"
        type G<'a> = std::sync::MutexGuard<'a, Vec<Box<[u8; 32]>>>;
        fn pull(mut guard: G<'_>, take: bool) -> Option<Box<[u8; 32]>>
            resources peak(memory) <= 512 {
            if !take { drop(guard); return None; }
            RESULT
        }
    "#;
    for (case, result) in [
        ("incoming", "guard.pop()"),
        ("fresh", "let box_to_return = Box::new([7u8; 32]); drop(guard); Some(box_to_return)"),
    ] {
        let helper = helper.replace("RESULT", result);
        let program = format!("{helper} {body}");
        diagnostics(
            &format!("guard_return_{case}"),
            &program,
            &[LINKED, "mutex intervals awaiting global"],
        );
        diagnostics(
            &format!("guard_return_{case}_short"),
            &program.replace("<= 42", "<= 41"),
            &[LINKED, "mutex intervals awaiting global", BUDGET],
        );
    }
}

#[test]
fn returned_box_lives_past_unlock_join_and_last_mutex_owner() {
    let program = workers("Box<[u8; 32]>", "new()", INSERT, REMOVE, RECEIPT);
    diagnostics("returned_box", &program, &[LINKED]);
    diagnostics("returned_box_short", &program.replace("<= 41", "<= 40"), &[LINKED, BUDGET]);
    diagnostics(
        "returned_box_under_guard_short",
        &program.replace("<= 106", "<= 105"),
        &[LINKED, CHECKPOINT],
    );
}

#[test]
fn successful_join_of_an_empty_pop_retains_only_the_inline_option() {
    let program = workers(
        "Box<[u8; 32]>",
        "new()",
        "let other = guard.pop(); drop(other);",
        REMOVE,
        &RECEIPT.replace("<= 41", "<= 9"),
    );
    diagnostics("empty_return", &program, &[LINKED]);
    diagnostics("empty_return_short", &program.replace("<= 9", "<= 8"), &[LINKED, BUDGET]);
}

#[test]
fn unique_extraction_and_returned_nested_vectors_partition_the_reservation_and_children() {
    let write = r#"
        let small = Box::new(Vec::<u8>::with_capacity(3));
        let big = Box::new(Vec::<u8>::with_capacity(61));
        guard.push(small);
        guard.push(big);
    "#;
    let receipt = RECEIPT
        .replace(
            "drop(keep);",
            r#"
        let recovered = std::sync::Arc::into_inner(keep);
        assert(current(memory) <= 171);
        drop(recovered);
    "#,
        )
        .replace("<= 41", "<= 94");
    let program =
        workers("Box<Vec<u8>>", "with_capacity(2)", write, "let item = guard.pop();", &receipt);
    // The two slots remain reserved after the pop. Both possible lock orders
    // leave at most two boxed vectors across the returned Option and the mutex.
    diagnostics("extracted_and_returned", &program, &[LINKED]);
    diagnostics("both_owners_short", &program.replace("<= 171", "<= 170"), &[LINKED, BUDGET]);
    diagnostics("large_child_short", &program.replace("<= 94", "<= 93"), &[LINKED, BUDGET]);
    let reversed = program
        .replace("guard.push(small);", "guard.push(SWAP);")
        .replace("guard.push(big);", "guard.push(small);")
        .replace("SWAP", "big")
        .replace("<= 94", "<= 36");
    diagnostics("small_child_last", &reversed, &[LINKED]);
    diagnostics("small_child_short", &reversed.replace("<= 36", "<= 35"), &[LINKED, BUDGET]);
}

#[test]
fn two_joined_consumers_can_own_only_one_published_box() {
    let receipt = r#"
        let first = consumer.join().unwrap();
        let second = another.join().unwrap();
        let done = producer.join();
        drop(done);
        drop(keep);
        assert(current(memory) <= 50);
        drop(first);
        drop(second);
        assert(current(memory) <= 0);
    "#;
    let program = workers("Box<[u8; 32]>", "new()", INSERT, REMOVE, receipt)
        .replace("let keep =", "let extra = cell.clone(); let keep =")
        .replace(
            "let first = consumer.join()",
            r#"
            let another = std::thread::spawn(move || {
                let r = extra.lock();
                if r.is_err() { return None; }
                let mut guard = r.unwrap();
                let item = guard.pop();
                drop(guard);
                item
            });
            let first = consumer.join()"#,
        );
    // Two inline Options plus the only box, whichever consumer acquired it.
    let linked = "distinct mutexes = 1, linked acquisitions = 3";
    diagnostics("two_receipts", &program, &[linked]);
    diagnostics("two_receipts_short", &program.replace("<= 50", "<= 49"), &[linked, BUDGET]);
}

#[test]
fn the_waiting_caller_and_the_intact_completion_record_coexist() {
    // The returning holder inserts and removes the box under the same guard.
    // The cell is always empty at release. The pad lives only across this join.
    let receipt = RECEIPT.replace("consumer.join()", "{ let _pad = [0u8; 256]; consumer.join() }");
    let program = workers(
        "Box<[u8; 32]>",
        "new()",
        "let other = guard.pop(); drop(other);",
        &format!("{INSERT} {REMOVE}"),
        &receipt,
    );
    diagnostics("intact_completion", &program.replace("<= 4096", "<= 372"), &[LINKED]);
    diagnostics(
        "omitted_completion",
        &program.replace("<= 4096", "<= 371"),
        &[LINKED, "while retaining a completed worker result"],
    );
}

#[test]
fn a_live_writer_and_an_unresolved_result_history_remain_outside_the_interface() {
    let receipt = RECEIPT.replace("let first =", "assert(current(memory) <= 4096); let first =");
    super::rejects(
        "before_last_join",
        &workers("Box<[u8; 32]>", "new()", INSERT, REMOVE, &receipt),
        "a checkpoint on owned shared backing before composing its worker updates",
    );
    // A populated vector moved into the cell currently lacks a portable publication recipe.
    let program = workers("Box<[u8; 32]>", "new()", INSERT, REMOVE, RECEIPT)
        .replace("let cell =", "let mut initial = Vec::<Box<[u8; 32]>>::new(); initial.push(Box::new([0u8; 32])); let cell =")
        .replace("Mutex::new(Vec::<Box<[u8; 32]>>::new())", "Mutex::new(initial)");
    super::rejects(
        "unresolved_receipt",
        &program,
        "a joined outcome without a complete checked history",
    );
}

#[test]
fn a_popped_box_moves_from_the_mutex_through_completion_to_the_joiner() {
    use super::{exceeds, verifies};

    let receipt = r#"
        let second = consumer.join();
        let first = producer.join();
        let kept = second.unwrap();
        drop(keep);
        BEFORE
        let workspace = Vec::<u8>::with_capacity(1024);
        drop(workspace);
        AFTER
    "#;
    let source = workers("Box<[u8; 32]>", "new()", INSERT, "let item = guard.pop();", receipt);
    // The joiner can own the 9-byte Option and the 32-byte payload after the
    // cell itself is gone. Moving the actual drop changes this reachable peak.
    for (name, before, after, peak) in [
        ("retain_popped_box", "", "drop(kept);", 1106),
        ("release_popped_box", "drop(kept);", "", 1065),
    ] {
        let work = source.replace("BEFORE", before).replace("AFTER", after);
        verifies(name, &work.replace("4096", &peak.to_string()));
        exceeds(name, &work.replace("4096", &(peak - 1).to_string()));
    }
}
