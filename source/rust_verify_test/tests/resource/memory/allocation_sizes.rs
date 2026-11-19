//! Exact charges observed by callers of helpers that return allocations.

use super::support::{rejects, verifies};
use crate::common::assert_vir_error_msg;
use crate::verify_one_file;

// Keep peak allowances loose so a failing checkpoint isolates retained bytes.
fn allowances(source: &str) -> String {
    const SIZE_HELPER_BYTES: u64 = 256;
    const BUILDER_BYTES: u64 = 1024;
    const FORWARDER_BYTES: u64 = 1280;
    const CALLER_BYTES: u64 = 1536;
    source
        .replace("SIZE_HELPER_BYTES", &SIZE_HELPER_BYTES.to_string())
        .replace("BUILDER_BYTES", &BUILDER_BYTES.to_string())
        .replace("FORWARDER_BYTES", &FORWARDER_BYTES.to_string())
        .replace("CALLER_BYTES", &CALLER_BYTES.to_string())
}

#[test]
fn complementary_capacities_survive_forwarding_and_extraction() {
    let code = allowances(
        r#"
        struct Batch { reversed: bool, buffers: Vec<Vec<u8>> }

        fn make(a: u8, b: u8, flag: bool) -> (out: Vec<Vec<u8>>)
            ensures out.len() == 2,
            resources peak(memory) <= BUILDER_BYTES,
        {
            let first = if flag { a } else { b };
            let second = if flag { b } else { a };
            let mut out = Vec::with_capacity(2);
            let x = Vec::<u8>::with_capacity(first as usize);
            out.push(x);
            let y = Vec::<u8>::with_capacity(second as usize);
            out.push(y);
            out
        }

        fn relay(a: u8, b: u8, flag: bool) -> (out: Batch)
            ensures out.buffers.len() == 2, out.reversed == flag,
            resources peak(memory) <= FORWARDER_BYTES,
        { Batch { reversed: flag, buffers: make(a, b, flag) } }

        fn caller(a: u8, b: u8, flag: bool)
            requires a > 0, b > 0, a as int + b as int == 32,
            resources peak(memory) <= CALLER_BYTES,
        {
            let mut out = relay(a, b, flag);
            // Three scalar inputs, the returned flag, three vector handles and 32 backing bytes.
            assert(current(memory) <= 108);
            let reversed = out.reversed;
            let item = out.buffers.pop().unwrap();
            drop(out);
            if reversed && b == 7 { assert(current(memory) <= 35); }
            if !reversed && a == 5 { assert(current(memory) <= 33); }
        }
    "#,
    );
    verifies("complementary_capacities", &code);
    rejects(
        "complementary_short",
        &code.replace("<= 108", "<= 107"),
        "conditional memory budget exceeded",
    );
    rejects(
        "selected_child_short",
        &code.replace("<= 35", "<= 34"),
        "conditional memory budget exceeded",
    );
}

#[test]
fn slice_rebinding_keeps_the_zero_and_positive_visit_sizes() {
    let code = allowances(
        r#"
        fn select_len(a: &[u8], b: &[u8], count: u8) -> (n: usize)
            ensures n <= a.len() + b.len(),
            resources peak(memory) <= SIZE_HELPER_BYTES,
        {
            let mut s = a;
            let mut i = 0u8;
            while i < count
                invariant i <= count,
                decreases count - i,
            {
                s = b;
                i += 1;
            }
            s.len()
        }

        fn build(a: &[u8], b: &[u8], count: u8) -> (v: Vec<Vec<u8>>)
            requires a.len() == 1, b.len() == 32,
            ensures v.len() == 1,
            resources peak(memory) <= BUILDER_BYTES,
        {
            let n = select_len(a, b, count);
            let inner = Vec::<u8>::with_capacity(n);
            let mut out = Vec::with_capacity(1);
            out.push(inner);
            out
        }

        fn caller(a: &[u8], b: &[u8], count: u8)
            requires a.len() == 1, b.len() == 32,
            resources peak(memory) <= CALLER_BYTES,
        {
            let v = build(a, b, count);
            // The two slice references, count, and two vector handles occupy 81 bytes.
            if count == 0 { assert(current(memory) <= 82); }
            else { assert(current(memory) <= 113); }
        }
    "#,
    );
    verifies("slice_exit_size", &code);
    for (name, exact, short) in [("zero", "<= 82", "<= 81"), ("positive", "<= 113", "<= 112")] {
        rejects(
            &format!("slice_exit_{name}_short"),
            &code.replace(exact, short),
            "conditional memory budget exceeded",
        );
    }
    // Even with zero visits a condition can rebind the slice on the false test.
    let effectful = code
        .replace(
            "while i < count",
            "while { if count == 0 && s.len() == a.len() { s = b; } i < count }",
        )
        .replace("\n                s = b;", "\n                s = a;");
    let err = verify_one_file(
        "effectful_slice_condition",
        format!("use vstd::prelude::*; verus! {{ {effectful} }}"),
        &[],
    )
    .unwrap_err();
    assert_missing_capacity(err, "let n = select_len");
    let specified = effectful
        .replace(
            "ensures n <= a.len() + b.len(),",
            "ensures n == if count == 0 { b.len() } else { a.len() },",
        )
        .replace("invariant i <= count,", "invariant i <= count, s == a,")
        .replace("if count == 0 { assert", "if count > 0 { assert");
    verifies("specified_slice_condition", &specified);
}

#[test]
fn last_write_sizes_the_allocation_until_a_push_replaces_its_backing() {
    let code = allowances(
        r#"
        fn build(visits: u8) -> (out: Vec<Vec<u8>>)
            requires visits <= 2,
            ensures out.len() == 1,
            resources peak(memory) <= BUILDER_BYTES,
        {
            let mut size = 7u8;
            let mut i = 0u8;
            while i < visits
                invariant i <= visits <= 2, size <= 7,
                decreases visits - i,
            {
                size = i;
                i += 1;
            }
            let capacity = size as usize;
            let mut child = Vec::<u8>::with_capacity(capacity);
            size = 15;
            child.push(size);
            let mut out = Vec::with_capacity(1);
            out.push(child);
            out
        }

        fn caller(visits: u8)
            requires visits <= 2,
            resources peak(memory) <= CALLER_BYTES,
        {
            let out = build(visits);
            // One input and two vector handles use 49 bytes. The three backing sizes
            // are seven, eight (a push into an empty reservation), and one.
            if visits == 0 { assert(current(memory) <= 56); }
            if visits == 1 { assert(current(memory) <= 57); }
            if visits == 2 { assert(current(memory) <= 50); }
        }
    "#,
    );
    verifies("last_write_charge", &code);
    rejects(
        "grown_backing_short",
        &code.replace("<= 57", "<= 56"),
        "conditional memory budget exceeded",
    );
}

#[test]
fn exact_postcondition_can_supply_an_unsupported_loop_result() {
    let code = allowances(
        r#"
        fn observed(seed: u8, visits: u8) -> (n: u8)
            ensures n == seed,
            resources peak(memory) <= SIZE_HELPER_BYTES,
        {
            let mut n = seed;
            let mut i = 0u8;
            while i < visits
                invariant i <= visits, n == seed,
                decreases visits - i,
            {
                if n == seed { n = seed; } else { n = 0; }
                i += 1;
            }
            n
        }

        fn build(seed: u8, visits: u8) -> (out: Vec<Vec<u8>>)
            ensures out.len() == 1,
            resources peak(memory) <= BUILDER_BYTES,
        {
            let n = observed(seed, visits);
            let child = Vec::<u8>::with_capacity(n as usize);
            let mut out = Vec::with_capacity(1);
            out.push(child);
            out
        }

        fn caller(visits: u8) resources peak(memory) <= CALLER_BYTES {
            let out = build(7, visits);
            assert(current(memory) <= 56);
        }
    "#,
    );
    verifies("postcondition_capacity", &code);
    rejects(
        "postcondition_capacity_short",
        &code.replace("<= 56", "<= 55"),
        "conditional memory budget exceeded",
    );
    verifies("returns_capacity", &code.replace("ensures n == seed,", "returns seed,"));
    rejects(
        "unproved_capacity_equality",
        &code.replace("ensures n == seed,", "ensures n == 0,"),
        "postcondition not satisfied",
    );
    let missing = code.replace("ensures n == seed,", "ensures n <= seed,");
    let err = verify_one_file(
        "unknown_capacity",
        format!("use vstd::prelude::*; verus! {{ {missing} }}"),
        &[],
    )
    .unwrap_err();
    assert_missing_capacity(err, "while i < visits");
}

fn assert_missing_capacity(err: crate::common::TestErr, source_line: &str) {
    let diagnostic = &err.errors[0];
    assert!(
        diagnostic.spans.iter().any(|span| span.label.as_deref()
            == Some("the exact size relationship could not be inferred here")
            && span.text.iter().any(|line| line.text.contains(source_line))),
        "{}",
        diagnostic.rendered
    );
    assert_vir_error_msg(err, "cannot infer the allocation size from its capacity");
}
