use crate::common::*;
use crate::verify_one_file;

#[test]
fn order_includes_calls_nested_in_arguments() {
    verify_one_file(
        "nested_call_order",
        code_str! {
            use vstd::prelude::*;
            verus! {
                fn caller() -> (r: u32) ensures r == 3, resources memory <= 12 { increment(seed()) }
                fn increment(x: u32) -> (r: u32) requires x < u32::MAX,
                    ensures r == x + 1, resources memory <= 8 { x + 1 }
                fn seed() -> (r: u32) ensures r == 2, resources memory <= 4 { 2 }
            }
        }
        .to_string(),
        &[],
    )
    .unwrap();
}

#[test]
fn body_budget_queries_are_not_executable_edges() {
    verify_one_file(
        "query_edges",
        code_str! {
            use vstd::prelude::*;
            verus! {
                fn first() resources memory <= 0 { assert(peak(memory) <= mem_peak(second)); }
                fn second() resources memory <= 0 { assert(peak(memory) <= mem_peak(first)); }
            }
        }
        .to_string(),
        &[],
    )
    .unwrap();
}

#[test]
fn ghost_initializers_and_proof_bodies_do_not_add_work() {
    verify_one_file(
        "ghost_edges",
        code_str! {
            use vstd::prelude::*;
            verus! {
                spec fn value() -> u32 { 3 }
                fn f() resources memory <= 0 {
                    let ghost n = value();
                    proof { assert(n == 3); }
                }
            }
        }
        .to_string(),
        &[],
    )
    .unwrap();
}

#[test]
fn unreachable_exec_calls_still_participate_in_recursion_policy() {
    let err = verify_one_file(
        "unreachable_cycle",
        code_str! {
            use vstd::prelude::*;
            verus! { fn f() resources memory <= 0 { if false { f(); } } }
        }
        .to_string(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err, "recursive memory contracts");
}

#[test]
fn cycle_through_a_constructor_is_rejected_at_a_call() {
    let err = verify_one_file(
        "constructor_cycle",
        code_str! {
            use vstd::prelude::*;
            verus! {
                struct Data { value: u32 }
                fn first() -> Data resources memory <= 8 { Data { value: second() } }
                fn second() -> u32 resources memory <= 8 { let data = first(); data.value }
            }
        }
        .to_string(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err.clone(), "recursive memory contracts");
    assert!(err.errors[0].spans.iter().any(|span| {
        span.is_primary
            && span
                .text
                .iter()
                .any(|line| line.text.contains("second()") || line.text.contains("first()"))
    }));
}
