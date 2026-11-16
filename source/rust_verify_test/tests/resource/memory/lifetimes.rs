use super::support::{rejects, verifies};
use crate::common::*;
use crate::verify_one_file;

#[test]
fn result_does_not_overlap_earlier_scratch() {
    verifies(
        "late_result",
        "fn f() -> [u32;4] resources peak(memory) <= 64 {
        { let scratch = [0u32;16]; } [0u32;4]
    } fn caller() resources peak(memory) <= 64 { let result = f(); }",
    );
}

#[test]
fn existing_destination_keeps_early_call_work() {
    let err = verify_one_file(
        "field_result",
        code_str! {
            use vstd::prelude::*;
            verus! {
                struct Data { values: [u32;4] }
                fn f() -> [u32;4] resources peak(memory) <= 64 {
                    { let scratch = [0u32;16]; } [0u32;4]
                }
                fn caller() resources peak(memory) <= 64 { let result = Data { values: f() }; }
            }
        }
        .to_string(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err, "peak 80 bytes exceeds budget 64 bytes");
}

#[test]
fn moves_transfer_one_value() {
    verifies(
        "move_chain",
        "struct Data { values: [u32;4] }
        fn f() -> Data resources peak(memory) <= 16 {
            let first = Data { values: [0u32;4] }; let second = first;
            let third = second; third
        }",
    );
}

#[test]
fn local_branch_result_remains_live_after_join() {
    verifies(
        "branch_local",
        "struct Data { value: u32 }
        fn f(flag: bool) resources peak(memory) <= 13 {
            let a = Data { value: 1 }; let b = Data { value: 2 };
            let selected = if flag { a } else { b };
            let scratch = 0u32;
        }",
    );
}

#[test]
fn explicit_drop_ends_handle_and_allocation() {
    verifies(
        "drop_lifetime",
        "fn f() resources peak(memory) <= 64 {
        let b = Box::new([0u32;4]); drop(b); let scratch = [0u32;16];
    }",
    );
}

#[test]
fn consumed_input_does_not_overlap_later_helper_work() {
    verifies(
        "consumed_call",
        "fn consume(b: Box<[u32;16]>) resources peak(memory) <= 128 {
        drop(b); let scratch = [0u32;32];
    }
    fn f() resources peak(memory) <= 128 { let b = Box::new([0u32;16]); consume(b); }",
    );
}

#[test]
fn nested_calls_preserve_input_release() {
    verifies(
        "nested_consumed_call",
        "fn inner(b: Box<[u32;16]>) resources peak(memory) <= 128 {
        drop(b); let scratch = [0u32;32];
    }
    fn outer(b: Box<[u32;16]>) resources peak(memory) <= 128 { inner(b); }
    fn f() resources peak(memory) <= 128 { let b = Box::new([0u32;16]); outer(b); }",
    );
}

#[test]
fn keeping_input_alive_still_costs_memory() {
    let err = verify_one_file(
        "retained_input",
        code_str! {
            use vstd::prelude::*;
            verus! {
                fn consume(b: Box<[u32;16]>) resources peak(memory) <= 136 { let scratch = [0u32;32]; }
                fn f() resources peak(memory) <= 136 { let b = Box::new([0u32;16]); consume(b); }
            }
        }
        .to_string(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err, "peak 200 bytes exceeds budget 136 bytes");
}

#[test]
fn section_consumption_ends_outer_value_lifetime() {
    verifies(
        "section_move",
        "struct Data { values: [u32;4] }
        fn f() resources peak(memory) <= 16 {
            let original = Data { values: [0u32;4] };
            resources peak(memory) <= 0 { let moved = original; }
            let next = [0u32;4];
        }",
    );
}

#[test]
fn standalone_move_ends_value_lifetime() {
    verifies(
        "discard_move",
        "struct Data { values: [u32;4] }
        fn f() resources peak(memory) <= 16 {
            let original = Data { values: [0u32;4] }; original;
            let next = [0u32;4];
        }",
    );
}

#[test]
fn unused_copy_keeps_original_value_live() {
    let err = verify_one_file(
        "discard_copy",
        code_str! {
            use vstd::prelude::*;
            verus! { fn f() resources peak(memory) <= 16 {
                let original = [0u32;4]; original; let next = [0u32;4];
            } }
        }
        .to_string(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err, "peak 32 bytes exceeds budget 16 bytes");
}

/// Check statement cleanup with a later workspace large enough to expose any
/// incorrectly retained result, and a surviving owner that must still count.
fn discarded_owner_peak(name: &str, code: &str, peak: u64) {
    verifies(name, &code.replace("BOUND", &format!("{peak}")));
    rejects(
        &format!("{name}_short"),
        &code.replace("BOUND", &format!("{short}", short = peak - 1)),
        "memory budget exceeded",
    );
}

#[test]
fn discarded_partial_move_preserves_parent_slot_and_sibling() {
    // After discarding first: 16 bytes for pair, 64 for its surviving child,
    // and 128 for workspace. The extracted handle's temporary has ended.
    discarded_owner_peak(
        "discarded_partial_move",
        "struct Pair { first: Box<[u8;16]>, second: Box<[u8;64]> }
        fn f() resources peak(memory) <= BOUND {
            let pair = Pair { first: Box::new([0u8;16]), second: Box::new([0u8;64]) };
            pair.first;
            let workspace = [0u8;128];
        }",
        208,
    );
}

#[test]
fn discarded_partial_move_exports_only_surviving_input_lifetime() {
    // The helper's 144-byte allowance overlaps the 64-byte surviving input.
    // Its discarded 16-byte input no longer overlaps the workspace.
    discarded_owner_peak(
        "discarded_partial_move_helper",
        "struct Pair { first: Box<[u8;16]>, second: Box<[u8;64]> }
        fn take(pair: Pair) -> Box<[u8;64]> resources peak(memory) <= 144 {
            pair.first;
            { let workspace = [0u8;128]; }
            pair.second
        }
        fn f() resources peak(memory) <= BOUND {
            let pair = Pair { first: Box::new([0u8;16]), second: Box::new([0u8;64]) };
            let result = take(pair);
        }",
        208,
    );
}

#[test]
fn discarded_call_results_end_at_statement_boundaries() {
    // A 72-byte retained box overlaps either the helper's declared 104-byte
    // allowance or the later 128-byte workspace. The discarded result is gone.
    for (name, execution, peak) in [
        ("call", "make();", 200),
        ("block", "{ let temporary = make(); temporary };", 200),
        ("section", "resources peak(memory) <= 104 { make(); }", 200),
        ("branch", "if flag { make(); } else { make(); }", 201),
        (
            "loop",
            "let mut i = 0u8; while i < 2 invariant i <= 2, decreases 2 - i,
                { make(); i += 1; }",
            201,
        ),
    ] {
        let parameter = if name == "branch" { "flag: bool" } else { "" };
        let code = format!(
            "fn make() -> Box<[u8;32]> resources peak(memory) <= 104 {{
                {{ let scratch = [0u8;96]; }}
                Box::new([0u8;32])
            }}
            fn f({parameter}) resources peak(memory) <= BOUND {{
                let retained = Box::new([0u8;64]);
                {execution}
                let workspace = [0u8;128];
            }}"
        );
        discarded_owner_peak(&format!("discarded_result_{name}"), &code, peak);
    }
}

#[test]
fn discarded_value_break_releases_only_its_result() {
    // The loop result has a 32-byte payload and an 8-byte handle. Both end
    // before the workspace; the separately retained 72 bytes remain live.
    discarded_owner_peak(
        "discarded_owner_break",
        "#[verifier::exec_allows_no_decreases_clause]
        fn f() resources peak(memory) <= BOUND {
            let retained = Box::new([0u8;64]);
            loop { break Box::new([0u8;32]); };
            let workspace = [0u8;128];
        }",
        200,
    );
}
