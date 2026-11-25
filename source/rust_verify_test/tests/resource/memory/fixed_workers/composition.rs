//! Whole-operation bounds through calls, delivery, critical sections and nested publication.
use super::{GUARDED, exceeds, pair, verifies};

#[test]
fn factoring_scratch_preserves_the_total_and_bills_additional_workspace() {
    let direct = "let v = Vec::<u8>::with_capacity(256); drop(v);";
    let equal = "fn scratch() resources peak(memory) <= 280 { BODY }";
    let work = pair("LIMIT", "left.clone()", "let g = LOCK.lock(); BODY drop(g);");
    // No scalar argument slot in the helper. Its sole Vec uses 24 + 256.
    let factored =
        format!("{} {}", equal.replace("BODY", direct), work.replace("BODY", "scratch();"));
    for (name, body) in [("direct", work.replace("BODY", direct)), ("factored", factored)] {
        verifies(name, &body.replace("LIMIT", "360"));
        exceeds(name, &body.replace("LIMIT", "359"));
    }
    let extra = "let extra = Vec::<u8>::with_capacity(256); BODY drop(extra);";
    let helper = equal.replace("280", "560").replace("BODY", &extra.replace("BODY", direct));
    let extra = format!("{helper} {}", work.replace("BODY", "scratch();"));
    verifies("additional_workspace", &extra.replace("LIMIT", "680"));
    exceeds("omitted_workspace", &extra.replace("LIMIT", "360"));
}

#[test]
fn skipped_and_repeated_acquisitions_do_not_retain_a_previous_guard() {
    let body = format!("if b > 0 {{ {GUARDED} }} {GUARDED}");
    verifies("repeat_or_skip", &pair("b + 160", "left.clone()", &body));
    let gap = "let g = LOCK.lock(); let v = Vec::<u8>::with_capacity(b as usize);
               drop(g); let next = LOCK.lock(); drop(v); drop(next);";
    verifies("reacquired", &pair("2 * b + 160", "left.clone()", gap));
    exceeds("unguarded_gap", &pair("b + 160", "left.clone()", gap));
}

#[test]
fn an_owned_result_can_outlive_its_guard_and_wait_for_a_delayed_join() {
    let source =
        include_str!("../../../../../../examples/resource/memory/concurrent/worker_result.rs");
    let short = source.replace("2 * (buffer_capacity as nat)", "(buffer_capacity as nat)");
    assert_ne!(source, short);
    let err = crate::verify_one_file("omitted_output", short, &["--no-cheating"]).unwrap_err();
    crate::common::assert_any_vir_error_msg(err, "memory budget exceeded");
}

#[test]
fn nested_publication_prices_only_the_outstanding_subtree() {
    let source = r#"
        fn work(b: u16) resources peak(memory) <= LIMIT {
            let outer = vstd::thread::spawn(move || {
                let child = vstd::thread::spawn(move || {
                    let child_scratch = Vec::<u8>::with_capacity(b as usize);
                    drop(child_scratch);
                });
                BEFORE
                let own_scratch = Vec::<u8>::with_capacity(b as usize);
                drop(own_scratch);
                AFTER
            });
            let done = outer.join();
        }
    "#;
    let join = "let done = child.join();";
    let together = source.replace("BEFORE", "").replace("AFTER", join);
    verifies("nested_overlap", &together.replace("LIMIT", "2 * b + 128"));
    exceeds("omitted_descendant", &together.replace("LIMIT", "b + 128"));
    let sequential = source.replace("BEFORE", join).replace("AFTER", "");
    verifies("nested_reuse", &sequential.replace("LIMIT", "b + 128"));
}

#[test]
fn the_publisher_keeps_its_mutex_identity_during_a_helper_call() {
    let source = r#"
        fn scratch(b: u16) resources peak(memory) <= b + 26 {
            let local = Vec::<u8>::with_capacity(b as usize);
            drop(local);
        }
        fn work(b: u16) resources peak(memory) <= b + 160 {
            let cell = std::sync::Arc::new(std::sync::Mutex::new(0u8));
            let peer = cell.clone();
            let worker = vstd::thread::spawn(move || {
                let guard = peer.lock();
                scratch(b);
                drop(guard);
            });
            let guard = cell.lock();
            ACTION
            let done = worker.join();
        }
    "#;
    verifies("publisher_held", &source.replace("ACTION", "scratch(b); drop(guard);"));
    exceeds("publisher_released", &source.replace("ACTION", "drop(guard); scratch(b);"));
}

fn assert_budget_failure_at(name: &str, source: String, site: &str) {
    let err = crate::verify_one_file(name, source, &["--no-cheating", "--multiple-errors=0"])
        .unwrap_err();
    assert!(
        err.errors.iter().any(|e| e.message.contains("memory budget exceeded")
            && e.spans.iter().any(|span| span.text.iter().any(|line| line.text.contains(site)))),
        "{:?}",
        err.errors
    );
}

#[test]
fn four_workers_require_the_guard_for_a_single_scratch_reservation() {
    let example =
        include_str!("../../../../../../examples/resource/memory/concurrent/mutex_lifetimes.rs");
    let unlocked = example.replace(
        "temporary(buffer_capacity);\n        drop(guard);",
        "drop(guard);\n        temporary(buffer_capacity);",
    );
    assert_ne!(example, unlocked);
    assert_budget_failure_at(
        "scratch_after_release",
        unlocked,
        "resources peak(memory) <= scratch_frames",
    );
}

#[test]
fn the_shared_vector_retains_all_four_buffers_after_join() {
    let example =
        include_str!("../../../../../../examples/resource/memory/concurrent/retained_buffers.rs");
    let checkpoint = "4 * (value_size(Vec<u8>) + value_size(Payload)));";
    for (name, bound) in [
        ("one_retained", "value_size(Vec<u8>) + value_size(Payload));"),
        (
            "one_byte_missing",
            "4 * value_size(Vec<u8>) + 3 * value_size(Payload) + value_size([u8; 255]));",
        ),
    ] {
        let short = example.replace(checkpoint, bound);
        assert_ne!(example, short);
        assert_budget_failure_at(name, short, "assert(current(memory)");
    }
}
