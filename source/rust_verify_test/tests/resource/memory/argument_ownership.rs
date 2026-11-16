//! Pending owning arguments overlap later evaluation until the callee runs.

use super::support::{rejects, verifies};
use crate::verify_one_file;

const HELPERS: &str = "
    fn make() -> Box<[u8;64]> resources peak(memory) <= 72 { Box::new([0u8;64]) }
    fn workspace() resources peak(memory) <= 128 { let scratch = [0u8;128]; }
    fn consume(first: Box<[u8;64]>, later: ()) resources peak(memory) <= 8 { drop(first); }
    fn forward(first: Box<[u8;64]>, later: ()) -> Box<[u8;64]>
        resources peak(memory) <= 8 { first }
    fn repeated_workspace() resources peak(memory) <= 129 {
        let mut i = 0u8;
        while i < 2 invariant i <= 2, decreases 2 - i, { workspace(); i += 1; }
    }
";

/// Use a generous later workspace to distinguish returned and consumed owners,
/// and require the independently calculated peak and its one-byte-short bound.
#[track_caller]
fn check_peak(name: &str, code: &str, peak: u64) {
    let code = format!("{HELPERS}\n{code}");
    verifies(name, &code.replace("BOUND", &format!("{peak}")));
    let code = code.replace("BOUND", &format!("{short}", short = peak - 1));
    let source = format!("use vstd::prelude::*; verus! {{ {code} }}");
    let error = verify_one_file(&format!("{name}_short"), source, &[]).unwrap_err();
    assert!(!error.errors.is_empty());
    for diagnostic in error.errors {
        assert!(diagnostic.code.is_none());
        assert!(
            diagnostic.message.contains("memory budget exceeded"),
            "{diagnostic:?}",
            diagnostic = diagnostic
        );
    }
}

#[test]
fn pending_owner_overlaps_later_calls_and_control_flow() {
    // Retained box: 8 + 32. Pending first argument: 8 + 64. Later helper: 128.
    // Branch input or caller/helper loop counter adds one byte during workspace.
    for (name, parameter, execution, peak) in [
        ("consume", "", "consume(make(), workspace());", 240),
        ("forward", "", "let result = forward(make(), workspace()); drop(result);", 240),
        ("nested", "", "consume(forward(make(), workspace()), workspace());", 240),
        (
            "branch",
            "flag: bool",
            "if flag { consume(make(), workspace()); }
                else { consume(make(), ()); }",
            241,
        ),
        (
            "operand_branch",
            "flag: bool",
            "consume(make(), if flag { workspace(); } else { () });",
            241,
        ),
        (
            "loop",
            "",
            "let mut i = 0u8;
            while i < 2 invariant i <= 2, decreases 2 - i, {
                consume(forward(make(), workspace()), workspace()); i += 1;
            };",
            241,
        ),
        ("loop_helper", "", "consume(make(), repeated_workspace());", 241),
    ] {
        let code = format!(
            "fn f({parameter}) resources peak(memory) <= BOUND {{
                let retained = Box::new([0u8;32]);
                {execution}
                {{ let after = [0u8;192]; }}
            }}"
        );
        check_peak(&format!("pending_owner_{name}"), &code, peak);
    }
}

#[test]
fn inline_argument_loops_keep_pending_and_returned_owners() {
    for (name, body, peak) in [
        ("normal", "workspace(); i += 1;", 241),
        ("branch", "if i == 0 { workspace(); } else { workspace(); } i += 1;", 241),
        (
            "nested",
            "let mut j = 0u8;
            while j < 2 invariant j <= 2, decreases 2-j, { workspace(); j += 1; }
            i += 1;",
            242,
        ),
    ] {
        for (callee, result, suffix, peak) in
            [("consume", "", "", peak), ("forward", "let result = ", "drop(result);", 304)]
        {
            // Pending owner 72 + caller root 40 + workspace 128 + loop
            // counters. Forwarding instead overlaps 72 + 40 + later 192.
            let code = format!(
                "fn f() resources peak(memory) <= BOUND {{
                let retained = Box::new([0u8;32]);
                {result}{callee}(make(), {{
                    let mut i = 0u8;
                    while i < 2 invariant i <= 2, decreases 2 - i, {{
                        {body}
                    }}
                }});
                {{ let after = [0u8;192]; }}
                {suffix}
            }}"
            );
            check_peak(&format!("pending_owner_inline_{name}_{callee}"), &code, peak);
        }
    }
}

#[test]
fn collection_state_changes_inside_arguments_still_require_binding() {
    rejects(
        "pending_owner_inline_vector_growth",
        &format!(
            "{HELPERS}
            fn f() resources peak(memory) <= 10000 {{
                consume(make(), {{
                    let mut values = Vec::<u32>::new(); values.push(1);
                }});
            }}"
        ),
        "vector allocation changes inside call arguments; bind the arguments first",
    );
}

#[test]
fn argument_loops_preserve_retained_collection_storage() {
    // Retained vector handle/backing/payload 64 + pending owner 72
    // + workspace 128 + counter 1 = 265; later scratch needs only 256.
    check_peak(
        "pending_owner_inline_retained_collection",
        "fn consume_collection(v: Vec<Box<[u8;32]>>) resources peak(memory) <= 24 { drop(v); }
        fn f() resources peak(memory) <= BOUND {
            let mut retained = Vec::<Box<[u8;32]>>::with_capacity(1);
            let child = Box::new([0u8;32]); retained.push(child);
            consume(make(), {
                let mut i = 0u8;
                while i < 2 invariant i <= 2, decreases 2-i, {
                    workspace(); i += 1;
                }
            });
            { let after = [0u8;192]; }
            consume_collection(retained);
        }",
        265,
    );
}

#[test]
fn forwarded_pending_owner_remains_live_after_call() {
    // A returned 72-byte owner and a retained 40-byte caller box overlap 192
    // bytes of later scratch: 304. Explicit drop then leaves only the 40 bytes.
    check_peak(
        "pending_owner_returned",
        "fn f() resources peak(memory) <= BOUND {
            let retained = Box::new([0u8;32]);
            let result = forward(make(), workspace());
            { let after = [0u8;192]; }
            drop(result);
            assert(current(memory) <= 40);
        }",
        304,
    );
}

#[test]
fn later_argument_slack_overlaps_pending_owner() {
    // The declared 160 bytes count even though only 128 are used: 40 + 72 + 160.
    check_peak(
        "pending_owner_slack",
        "fn slack_workspace() resources peak(memory) <= 160 { workspace(); }
        fn f() resources peak(memory) <= BOUND {
            let retained = Box::new([0u8;32]);
            consume(make(), slack_workspace());
        }",
        272,
    );
}

#[test]
fn later_owning_result_keeps_the_first_argument_pending() {
    for (name, result_type, finish, peak) in
        [("consumed", "()", "drop(first);", 240), ("returned", "Box<[u8;64]>", "first", 304)]
    {
        let after = if name == "consumed" {
            "{ let after = [0u8;192]; }"
        } else {
            "{ let after = [0u8;192]; } drop(result);"
        };
        let code = format!(
            "fn later() -> Box<[u8;16]> resources peak(memory) <= 128 {{
                workspace(); Box::new([0u8;16])
            }}
            fn select(first: Box<[u8;64]>, second: Box<[u8;16]>) -> {result_type}
                resources peak(memory) <= 16 {{ drop(second); {finish} }}
            fn f() resources peak(memory) <= BOUND {{
                let retained = Box::new([0u8;32]);
                let result = select(make(), later());
                {after}
            }}"
        );
        // Later's 128-byte allowance overlaps the retained 40 and pending 72.
        // If first is returned, those same 112 bytes overlap 192 after the call.
        check_peak(&format!("pending_owner_later_result_{name}"), &code, peak);
    }
}

#[test]
fn incoming_pending_owners_keep_independent_caller_lifetimes() {
    // The helper counts 16 handle bytes plus 128 workspace bytes; its caller
    // contributes both payloads (64 + 32) until the later argument completes.
    check_peak(
        "pending_owner_incoming",
        "fn relay(first: Box<[u8;64]>, retained: Box<[u8;32]>)
            resources peak(memory) <= 144 {
                consume(first, workspace()); drop(retained);
            }
        fn f() resources peak(memory) <= BOUND {
            relay(make(), Box::new([0u8;32]));
            { let after = [0u8;192]; }
            assert(current(memory) <= 0);
        }",
        240,
    );

    // Returning first preserves its 72 bytes after relay releases retained.
    check_peak(
        "pending_owner_incoming_returned",
        "fn relay(first: Box<[u8;64]>, retained: Box<[u8;32]>) -> Box<[u8;64]>
            resources peak(memory) <= 144 {
                let result = forward(first, workspace()); drop(retained); result
            }
        fn f() resources peak(memory) <= BOUND {
            let result = relay(make(), Box::new([0u8;32]));
            { let after = [0u8;256]; }
            drop(result);
            assert(current(memory) <= 0);
        }",
        328,
    );
}

#[test]
fn later_argument_drop_releases_only_the_other_incoming_owner() {
    // Retiring the 32-byte payload and its handle leaves the pending first
    // argument's 72 bytes overlapping the 128-byte workspace.
    check_peak(
        "pending_owner_other_drop",
        "fn relay(first: Box<[u8;64]>, retained: Box<[u8;32]>)
            resources peak(memory) <= 136 {
                consume(first, { drop(retained); workspace(); });
            }
        fn f() resources peak(memory) <= BOUND {
            relay(make(), Box::new([0u8;32]));
            assert(current(memory) <= 0);
        }",
        200,
    );
}

#[test]
fn pending_partial_move_keeps_parent_slot_and_sibling() {
    // The 16-byte parent slot remains; moving first adds an 8-byte pending
    // handle. Both original payloads (64 + 32) overlap the later 128 bytes.
    check_peak(
        "pending_owner_partial_move",
        "struct Pair { first: Box<[u8;64]>, second: Box<[u8;32]> }
        fn f() resources peak(memory) <= BOUND {
            let pair = Pair { first: make(), second: Box::new([0u8;32]) };
            consume(pair.first, workspace());
            { let after = [0u8;192]; }
            assert(current(memory) <= 48);
        }",
        248,
    );
}

#[test]
fn pending_collection_uses_the_prepared_transfer_interface() {
    for (name, result_type, finish, after, peak) in [
        ("consumed", "()", "drop(first);", "", 264),
        ("returned", "Vec<Box<[u8;64]>>", "first", "{ let after = [0u8;192]; } drop(result);", 328),
    ] {
        // The collection owns a 24-byte handle, 8-byte backing, and 64-byte
        // child. Its 96 bytes overlap either the later 128-byte allowance or
        // 192 bytes after return, alongside the retained 40-byte caller box.
        let code = format!(
            "fn select(first: Vec<Box<[u8;64]>>, later: ()) -> {result_type}
                resources peak(memory) <= 24 {{ {finish} }}
            fn f() resources peak(memory) <= BOUND {{
                let retained = Box::new([0u8;32]);
                let mut pending = Vec::<Box<[u8;64]>>::with_capacity(1);
                let child = make(); pending.push(child);
                let result = select(pending, workspace());
                {after}
                assert(current(memory) <= 40);
            }}"
        );
        check_peak(&format!("pending_collection_{name}"), &code, peak);
    }
}
