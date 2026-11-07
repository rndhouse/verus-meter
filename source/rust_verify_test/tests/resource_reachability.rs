#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

fn verifies(name: &str, body: &str) {
    verify_one_file(name, format!("use vstd::prelude::*; verus! {{ {body} }}"), &[]).unwrap();
}
#[test]
fn fixed_budget_uses_preconditions() {
    verifies(
        "fixed_precondition",
        "fn f(n: u32) requires n < 4, mem_peak <= 4 {
        if n >= 4 { let large = [0u8;64]; }
    }",
    );
}
#[test]
fn fixed_budget_uses_loop_invariants() {
    verifies(
        "fixed_loop",
        "fn f(mut i: u32) requires i <= 4, mem_peak <= 4 {
        while i < 4 invariant i <= 4, decreases 4 - i, {
            if i >= 4 { let large = [0u8;64]; }
            i = i + 1;
        }
    }",
    );
}
#[test]
fn fixed_sections_and_checkpoints_use_reachability() {
    verifies(
        "fixed_section",
        "fn f(n: u32) requires n < 4, mem_peak <= 4 {
        mem_peak <= 0 { if n >= 4 { let large = [0u8;64]; } }
        assert(current(mem_peak) <= 4);
    }",
    );
}
#[test]
fn reachable_cost_still_fails() {
    let err = verify_one_file(
        "reachable",
        "use vstd::prelude::*; verus! {
        fn f(n: u32) requires n <= 4, mem_peak <= 4 { if n >= 4 { let large = [0u8;64]; } }
    }"
        .into(),
        &[],
    )
    .unwrap_err();
    assert!(err.errors.iter().any(|e| e.message.contains("peak 68 bytes exceeds budget 4 bytes")));
}
