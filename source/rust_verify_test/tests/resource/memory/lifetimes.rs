use super::support::verifies;
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
    assert!(!err.errors.is_empty());
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
fn different_return_sources_do_not_create_a_third_value() {
    verifies(
        "branch_result",
        "struct Data { value: u32 }
        fn f(a: Data, b: Data, flag: bool) -> Data resources peak(memory) <= 9 {
            if flag { a } else { b }
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
    assert!(!err.errors.is_empty());
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
    assert_any_vir_error_msg(err, "peak 32 bytes exceeds budget 16 bytes");
}
