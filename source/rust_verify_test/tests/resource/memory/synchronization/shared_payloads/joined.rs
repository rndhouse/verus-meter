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
