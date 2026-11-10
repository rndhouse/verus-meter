//! Spec formulas must prove real bounds, without becoming executable work or assumptions.

use super::support::{rejects, verifies};

#[test]
fn conditional_spec_budget() {
    verifies(
        "conditional",
        r#"
        spec fn bytes(large: bool) -> nat { if large { 32 } else { 16 } }
        fn f(large: bool) resources mem_peak <= mem_size(large) + bytes(large) {
            if large { let a = [0u32; 8]; } else { let b = [0u32; 4]; }
        }
    "#,
    );
}

#[test]
fn insufficient_spec_budget() {
    rejects(
        "insufficient",
        r#"
        spec fn bytes(large: bool) -> nat { if large { 31 } else { 16 } }
        fn f(large: bool) resources mem_peak <= mem_size(large) + bytes(large) {
            if large { let a = [0u32; 8]; } else { let b = [0u32; 4]; }
        }
    "#,
        "conditional memory budget exceeded",
    );
}

#[test]
fn symbolic_arguments_and_call_composition() {
    verifies(
        "composition",
        r#"
        spec fn bytes(n: nat) -> nat { 24 + 4 * n }
        fn allocate(n: usize)
            requires n <= 100,
            resources mem_peak <= mem_size(n) + bytes(n as nat),
        { let v = Vec::<u32>::with_capacity(n); }
        fn delegate(n: usize)
            requires n <= 100,
            resources mem_peak <= mem_size(n) + mem_peak(allocate(n)),
        { allocate(n); }
        fn caller() resources mem_peak <= 48 { delegate(2); }
    "#,
    );
}

#[test]
fn caller_must_pay_declared_spec_bound() {
    rejects(
        "caller",
        r#"
        spec fn bytes() -> nat { 32 }
        fn helper() resources mem_peak <= bytes() { let a = [0u32; 4]; }
        fn caller() resources mem_peak <= 31 { helper(); }
    "#,
        "conditional memory budget exceeded",
    );
}

#[test]
fn spec_body_uses_verus_match_and_nested_calls() {
    verifies(
        "match",
        r#"
        enum Choice { Small, Large }
        spec fn chosen(c: Choice) -> nat {
            match c { Choice::Small => 16, Choice::Large => 32 }
        }
        spec fn bytes(large: bool) -> nat {
            chosen(if large { Choice::Large } else { Choice::Small })
        }
        fn f() resources mem_peak <= bytes(false) { let a = [0u32; 4]; }
    "#,
    );
}

#[test]
fn qualified_and_nested_spec_calls() {
    verifies(
        "qualified",
        r#"
        mod budgets {
            use vstd::prelude::*;
            pub open spec fn base() -> nat { 16 }
            pub open spec fn twice(n: nat) -> nat { 2 * n }
        }
        fn f() resources mem_peak <= budgets::twice(budgets::base()) { let a = [0u32; 8]; }
    "#,
    );
}

#[test]
fn u64_spec_result() {
    verifies(
        "u64",
        r#"
        spec fn bytes() -> u64 { 16 }
        fn f() resources mem_peak <= bytes() { let a = [0u32; 4]; }
    "#,
    );
}

#[test]
fn oversized_nat_result_is_rejected_even_for_empty_body() {
    rejects(
        "overflow",
        r#"
        spec fn bytes() -> nat { 18446744073709551616 }
        fn f() resources mem_peak <= bytes() {}
    "#,
        "memory budget arithmetic exceeds u64",
    );
}

#[test]
fn executable_budget_call_is_rejected() {
    rejects(
        "exec",
        r#"
        fn bytes() -> u64 { 16 }
        fn f() resources mem_peak <= bytes() {}
    "#,
        "memory budgets require a local, nongeneric spec function",
    );
}

#[test]
fn executable_argument_is_rejected() {
    rejects(
        "exec_arg",
        r#"
        fn select() -> bool { true }
        spec fn bytes(b: bool) -> nat { if b { 16 } else { 0 } }
        fn f() resources mem_peak <= bytes(select()) {}
    "#,
        "memory budget spec functions must return nat or u64",
    );
}

#[test]
fn mutable_parameter_is_rejected() {
    rejects(
        "mutable",
        r#"
        spec fn bytes(b: bool) -> nat { if b { 16 } else { 0 } }
        fn f(mut b: bool) resources mem_peak <= bytes(b) { b = false; }
    "#,
        "immutable Boolean or native integer input parameters",
    );
}

#[test]
fn signed_result_is_rejected() {
    rejects(
        "signed",
        r#"
        spec fn bytes() -> int { -1 }
        fn f() resources mem_peak <= bytes() {}
    "#,
        "memory budget spec functions must return nat or u64",
    );
}

#[test]
fn argument_free_query_needs_an_envelope() {
    rejects(
        "envelope",
        r#"
        spec fn bytes() -> nat { 16 }
        fn helper() resources mem_peak <= bytes() {}
        fn f() resources mem_peak <= mem_peak(helper) {}
    "#,
        "runtime memory budgets require mem_peak(helper(arguments))",
    );
}

#[test]
fn section_still_requires_a_fixed_budget() {
    rejects(
        "section",
        r#"
        spec fn bytes() -> nat { 16 }
        fn f() resources mem_peak <= 16 { resources mem_peak <= bytes() { let a = [0u32; 4]; } }
    "#,
        "section and checkpoint bounds remain fixed",
    );
}

#[test]
fn uninterpreted_budget_is_rejected() {
    rejects(
        "uninterpreted",
        r#"
        uninterp spec fn bytes() -> nat;
        fn f() resources mem_peak <= bytes() {}
    "#,
        "memory budgets require a local, nongeneric spec function",
    );
}

#[test]
fn recursive_spec_still_needs_a_termination_proof() {
    rejects(
        "termination",
        r#"
        spec fn bytes(n: nat) -> nat { bytes(n) }
        fn f() resources mem_peak <= bytes(0) {}
    "#,
        "recursive function must have a `decreases` clause",
    );
}

#[test]
fn unselected_spec_bound_need_not_fit_u64() {
    verifies(
        "unselected",
        r#"
        spec fn enormous() -> nat { 18446744073709551616 }
        fn f(large: bool)
            requires !large,
            resources mem_peak <= 1 + if large { enormous() } else { 0 },
        {}
    "#,
    );
}

#[test]
fn spec_budget_example_compiles() {
    crate::verify_one_file(
        "spec_budgets",
        include_str!("../../../../../examples/resource/memory/spec_budgets.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn model_sizes_inside_spec_bodies() {
    verifies(
        "sizes",
        r#"
        struct Buffer { words: [u32; 4], ready: bool }
        spec fn bytes() -> nat { mem_size(Buffer) }
        fn f() resources mem_peak <= bytes() { let b = Buffer { words: [0u32;4], ready: false }; }
    "#,
    );
}

#[test]
fn parameter_size_inside_spec_body() {
    verifies(
        "param_size",
        r#"
        spec fn bytes(n: u32) -> nat { mem_size(n) }
        fn f() resources mem_peak <= bytes(0) { let n = 0u32; }
    "#,
    );
}

#[test]
fn returned_formula_captures_parameters() {
    verifies(
        "formula",
        r#"
        spec fn formula(per_item: nat) -> spec_fn(nat) -> nat {
            |n: nat| mem_size(Vec<u32>) + per_item * n
        }
        fn f(n: usize)
            requires n <= 100,
            resources mem_peak <= mem_size(n) + formula(4)(n as nat),
        { let values = Vec::<u32>::with_capacity(n); }
        fn caller() resources mem_peak <= 40 { f(2); }
    "#,
    );
}

#[test]
fn returned_formula_cannot_underbudget() {
    rejects(
        "small_formula",
        r#"
        spec fn formula() -> spec_fn(nat) -> nat { |n: nat| n }
        fn f() resources mem_peak <= formula()(15) { let data = [0u32;4]; }
    "#,
        "conditional memory budget exceeded",
    );
}

#[test]
fn size_query_in_formula_argument() {
    verifies(
        "size_argument",
        r#"
        spec fn bytes(n: nat) -> nat { n }
        fn f() resources mem_peak <= bytes(mem_size([u32;4])) { let a = [0u32;4]; }
    "#,
    );
}

#[test]
fn size_query_does_not_evaluate_argument() {
    rejects(
        "unevaluated",
        r#"
        fn make() -> u32 { 1 }
        spec fn bytes() -> nat { mem_size(make()) }
        fn f() resources mem_peak <= bytes() {}
    "#,
        "expected",
    );
}
