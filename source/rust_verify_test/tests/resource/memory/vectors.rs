use super::support::{rejects, verifies};
use crate::common::*;
use crate::verify_one_file;

test_verify_one_file! {
    #[test] fixed_capacity verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= mem_size(Vec<u32>) + 2 * mem_size(u32) {
            let mut values = Vec::<u32>::with_capacity(2);
            values.push(1); values.push(2);
            assert(values[0] == 1 && values[1] == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] push_over_capacity verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= mem_size(Vec<u32>) + mem_size(u32) {
            let mut values = Vec::<u32>::with_capacity(1);
            values.push(1); values.push(2);
        }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded")
}

test_verify_one_file! {
    #[test] unused_capacity_counts verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 31 { let values = Vec::<u32>::with_capacity(2); }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 31 bytes")
}

test_verify_one_file! {
    #[test] pop_reuses_capacity verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 28 {
            let mut values = Vec::<u32>::with_capacity(1);
            values.push(1); values.pop(); values.push(2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] move_and_drop verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 76 {
            let mut values = Vec::<u32>::with_capacity(1);
            values.push(1);
            let moved = values; drop(moved);
            let another = Vec::<u32>::with_capacity(1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_pushes verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 48 {
            let mut values = Vec::<u32>::with_capacity(4);
            let mut i: usize = 0;
            while i < 4 invariant i <= 4, values.len() == i, decreases 4 - i, {
                values.push(7); i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrow_slice verus_code! {
        use vstd::prelude::*;
        fn read(values: &[u32]) mem_peak <= mem_size(values) {}
        fn fill(values: &mut [u32]) requires values.len() > 0, ensures final(values)[0] == 9, mem_peak <= mem_size(values) { values[0] = 9; }
        fn f() mem_peak <= 44 {
            let mut values = Vec::<u32>::with_capacity(1);
            values.push(1); read(values.as_slice()); fill(values.as_mut_slice());
            assert(values[0] == 9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] index_and_length verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 40 {
            let mut values = Vec::<u32>::with_capacity(1);
            values.push(1);
            let n = values.len(); let value = values[0];
            assert(n == 1 && value == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] runtime_capacity verus_code! {
        use vstd::prelude::*;
        fn f(capacity: usize)
            requires capacity > 0, capacity <= 16,
            mem_peak <= mem_size(capacity) + mem_size(Vec<u32>) + capacity * mem_size(u32),
        {
            let mut values = Vec::<u32>::with_capacity(capacity);
            values.push(7);
            assert(values[0] == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] runtime_capacity_fixed_bound verus_code! {
        use vstd::prelude::*;
        fn f(capacity: usize) requires capacity <= 4, mem_peak <= 48 {
            let values = Vec::<u32>::with_capacity(capacity);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] runtime_capacity_exceeds_bound verus_code! {
        use vstd::prelude::*;
        fn f(capacity: usize) requires capacity <= 5, mem_peak <= 48 {
            let values = Vec::<u32>::with_capacity(capacity);
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}

test_verify_one_file! {
    #[test] runtime_budget_must_fit_u64 verus_code! {
        use vstd::prelude::*;
        fn f(capacity: usize) mem_peak <= mem_size(capacity) + capacity * mem_size(u64) {}
    } => Err(err) => assert!(!err.errors.is_empty() && err.errors.iter().all(|e| e.message.contains("memory budget arithmetic exceeds u64")))
}

test_verify_one_file! {
    #[test] runtime_budget_call verus_code! {
        use vstd::prelude::*;
        fn helper(capacity: usize) requires capacity <= 4,
            mem_peak <= mem_size(capacity) + mem_size(Vec<u32>) + capacity * mem_size(u32),
        { let values = Vec::<u32>::with_capacity(capacity); }
        fn caller(capacity: usize) requires capacity <= 4,
            mem_peak <= mem_size(capacity) + mem_peak(helper(capacity)),
        { helper(capacity); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] runtime_checkpoint verus_code! {
        use vstd::prelude::*;
        fn f(capacity: usize) requires capacity <= 4, mem_peak <= 48 {
            let values = Vec::<u32>::with_capacity(capacity);
            drop(values);
            assert(current(mem_peak) <= 47);
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}

#[test]
fn empty_vector_has_no_backing_charge() {
    verifies("empty_vector", "fn f() mem_peak <= 24 { let v = Vec::<u32>::new(); }");
    verifies(
        "new_can_grow",
        "fn f() mem_peak <= 100 { let mut v = Vec::<u32>::new(); v.push(1); }",
    );
}

#[test]
fn moves_preserve_capacity() {
    verifies(
        "moves_preserve_capacity",
        "fn f() mem_peak <= 52 { let v = Vec::<u32>::with_capacity(1); let mut moved = v; moved.push(1); }",
    );
    verifies(
        "moved_full",
        "fn f() mem_peak <= 52 { let mut v = Vec::<u32>::with_capacity(1); v.push(1); let mut moved = v; moved.push(2); }",
    );
}

#[test]
fn pop_does_not_release_backing() {
    rejects(
        "pop_keeps_backing",
        "fn f() mem_peak <= 55 { let mut v = Vec::<u32>::with_capacity(1); v.push(1); v.pop(); let second = Vec::<u32>::with_capacity(1); }",
        "memory budget exceeded",
    );
}

#[test]
fn runtime_moves_and_drop() {
    verifies(
        "runtime_moves_and_drop",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= mem_size(cap) + 3 * mem_size(Vec<u32>) + cap * mem_size(u32) { let v = Vec::<u32>::with_capacity(cap); let moved = v; drop(moved); let second = Vec::<u32>::with_capacity(cap); }",
    );
}

#[test]
fn runtime_scopes_reuse() {
    verifies(
        "runtime_scopes_reuse",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= mem_size(cap) + mem_size(Vec<u32>) + cap * mem_size(u32) { { let v = Vec::<u32>::with_capacity(cap); } { let v = Vec::<u32>::with_capacity(cap); } }",
    );
}

#[test]
fn runtime_overlap_rejected() {
    rejects(
        "runtime_overlap",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= mem_size(cap) + 2 * mem_size(Vec<u32>) + cap * mem_size(u32) { let a = Vec::<u32>::with_capacity(cap); let b = Vec::<u32>::with_capacity(cap); }",
        "conditional memory budget exceeded",
    );
}

#[test]
fn runtime_backing_retained_across_call() {
    rejects(
        "runtime_backing_call",
        "fn helper() mem_peak <= 16 { let data = [0u8; 16]; } fn f(cap: usize) requires cap <= 4, mem_peak <= 48 { let v = Vec::<u32>::with_capacity(cap); helper(); }",
        "conditional memory budget exceeded",
    );
    verifies(
        "runtime_backing_call_ok",
        "fn helper() mem_peak <= 16 { let data = [0u8; 16]; } fn f(cap: usize) requires cap <= 4, mem_peak <= 64 { let v = Vec::<u32>::with_capacity(cap); helper(); }",
    );
}

#[test]
fn dynamic_parent_and_section() {
    verifies(
        "dynamic_parent_and_section",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= mem_size(cap) + mem_size(Vec<u32>) + cap * mem_size(u32) + 40 { let parent = Vec::<u32>::with_capacity(cap); mem_peak <= 40 { let child = Vec::<u32>::with_capacity(cap); } }",
    );
    rejects(
        "dynamic_section_short",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= 100 { mem_peak <= 39 { let child = Vec::<u32>::with_capacity(cap); } }",
        "conditional memory budget exceeded",
    );
}

#[test]
fn runtime_loop_reuses_allocations() {
    verifies(
        "runtime_loop_reuse",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= 56 { let mut i: usize = 0; while i < 2 invariant i <= 2, cap <= 4, decreases 2 - i, { let v = Vec::<u32>::with_capacity(cap); i = i + 1; } }",
    );
}

#[test]
fn loop_needs_evidence_for_capacity() {
    rejects(
        "loop_no_length_invariant",
        "fn f() mem_peak <= 48 { let mut v = Vec::<u32>::with_capacity(4); let mut i: usize = 0; while i < 4 invariant i <= 4, decreases 4 - i, { v.push(1); i = i + 1; } }",
        "memory budget exceeded",
    );
}

#[test]
fn conditional_pushes_follow_proofs() {
    verifies(
        "conditional_push",
        "fn f(flag: bool) mem_peak <= 29 { let mut v = Vec::<u32>::with_capacity(1); if flag { v.push(1); } else { v.push(2); } }",
    );
}

#[test]
fn zero_size_elements_can_grow_without_backing_storage() {
    verifies(
        "zero_size_push",
        "fn f() mem_peak <= 24 { let mut v = Vec::<()>::with_capacity(1); v.push(()); }",
    );
    verifies(
        "zero_size_grows",
        "fn f() mem_peak <= 24 { let mut v = Vec::<()>::with_capacity(1); v.push(()); v.push(()); }",
    );
}

#[test]
fn wide_integer_elements() {
    verifies(
        "wide_vector",
        "fn f() mem_peak <= 56 { let mut v = Vec::<i128>::with_capacity(2); v.push(-1i128); v.push(2i128); }",
    );
}

#[test]
fn fixed_struct_elements() {
    verifies(
        "struct_vector",
        "struct Item { n: u32, ready: bool } fn f() mem_peak <= 29 { let mut v = Vec::<Item>::with_capacity(1); v.push(Item { n: 7, ready: true }); }",
    );
}

#[test]
fn reject_unsupported_vector_operations() {
    rejects(
        "vector_reserve",
        "fn f() mem_peak <= 100 { let mut v = Vec::<u32>::with_capacity(1); v.reserve(2); }",
        "does not support",
    );
    rejects(
        "vector_reassign",
        "fn f() mem_peak <= 100 { let mut v = Vec::<u32>::with_capacity(1); v = Vec::<u32>::with_capacity(2); }",
        "reassignment of heap owners",
    );
    verifies("vector_owner_param", "fn f(v: Vec<u32>) mem_peak <= 24 {}");
    verifies("vector_ref_param", "fn f(v: &mut Vec<u32>) mem_peak <= 8 {}");
    rejects(
        "vector_nested_owner",
        "fn f() mem_peak <= 100 { let v = Vec::<Box<u32>>::with_capacity(1); }",
        "owning or reference-valued vector elements",
    );
    rejects(
        "vector_conditional_drop",
        "fn f(flag: bool) mem_peak <= 100 { let v = Vec::<u32>::with_capacity(1); if flag { drop(v); } }",
        "moving or dropping an enclosing heap owner",
    );
}

#[test]
fn runtime_queries_require_arguments() {
    rejects(
        "query_runtime_envelope",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= mem_size(cap) + cap {} fn g() mem_peak <= mem_peak(f) {}",
        "runtime memory budgets require mem_peak(helper(arguments))",
    );
}

#[test]
fn quantities_require_stable_unsigned_inputs() {
    rejects(
        "named_constant_quantity",
        "const BUDGET: u64 = 16; fn f() mem_peak <= BUDGET {}",
        "memory budget predicates currently support scalar input comparisons and Boolean operators",
    );
    rejects(
        "signed_quantity",
        "fn f(n: i32) mem_peak <= mem_size(n) + n {}",
        "memory quantities require immutable unsigned integers",
    );
    rejects(
        "mutable_quantity",
        "fn f(mut n: usize) mem_peak <= mem_size(n) + n {}",
        "immutable Boolean or native integer input parameters",
    );
    rejects(
        "mutable_capacity",
        "fn f(mut n: usize) mem_peak <= 100 { let v = Vec::<u32>::with_capacity(n); }",
        "immutable Boolean or native integer input parameters",
    );
}

#[test]
fn vector_examples() {
    verify_one_file(
        "vector_example",
        include_str!("../../../../../examples/resource/memory/vectors.rs").into(),
        &["--compile"],
    )
    .unwrap();
    let err = verify_one_file(
        "vector_growth",
        include_str!("../../../../../examples/resource/memory/expected-failures/vector_growth.rs")
            .into(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err.clone(), "memory budget exceeded");
    assert!(
        err.errors.iter().flat_map(|e| &e.spans).any(
            |s| s.is_primary && s.text.iter().any(|line| line.text.contains("values.push(20)"))
        )
    );
}

#[test]
fn direct_index_mutation_and_slice_local() {
    verifies(
        "vector_index_mut",
        "fn f() mem_peak <= 44 { let mut v = Vec::<u32>::with_capacity(1); v.push(1); v[0] = 9; let slice = v.as_slice(); assert(slice[0] == 9); }",
    );
}

#[test]
fn runtime_constant_call_has_a_fixed_envelope() {
    verifies(
        "constant_call_envelope",
        "fn f(cap: usize) requires cap <= 4, mem_peak <= mem_size(cap) + cap {} fn g() mem_peak <= mem_peak(f(4)) { f(4); } fn h() mem_peak <= mem_peak(g) { g(); }",
    );
}

#[test]
fn hidden_runtime_overflow_is_rejected() {
    rejects(
        "hidden_runtime_overflow",
        "fn f(n: usize) mem_peak <= mem_size(n) + (n + 18446744073709551615) * 0 {}",
        "memory budget arithmetic exceeds u64",
    );
}

#[test]
fn conditional_arithmetic_is_guarded() {
    verifies(
        "guarded_runtime_arithmetic",
        "fn f(n: usize) mem_peak <= mem_size(n) + if n <= 4 { n * 4 } else { 0 } {}",
    );
}

#[test]
fn aliases_keep_vector_identity() {
    verifies(
        "vector_alias",
        "use std::vec::Vec as Buffer; use std::mem::drop as release; fn f() mem_peak <= 28 { let mut v = Buffer::<u32>::with_capacity(1); v.push(1); release(v); }",
    );
}

#[test]
fn local_capacity_is_stable() {
    verifies(
        "local_capacity",
        "fn f() mem_peak <= 36 { let capacity: usize = 1; let mut v = Vec::<u32>::with_capacity(capacity); v.push(1); }",
    );
}

#[test]
fn checkpoint_includes_retained_dynamic_backing_and_call() {
    rejects(
        "dynamic_call_checkpoint",
        "fn helper(flag: bool) mem_peak <= mem_size(flag) + if flag { 8 } else { 0 } { if flag { let a = [0u8; 8]; } } fn f(cap: usize, flag: bool) requires cap <= 4, mem_peak <= 100 { let v = Vec::<u32>::with_capacity(cap); helper(flag); assert(current(mem_peak) <= 57); }",
        "conditional memory budget exceeded",
    );
}

#[test]
fn symbolic_checkpoint_after_repeated_branches() {
    let branches = "if flag {}\n".repeat(32);
    let body = format!(
        "fn f(cap: usize, flag: bool) requires cap <= 4, mem_peak <= 49 {{
            let v = Vec::<u32>::with_capacity(cap);
            {branches}
            assert(current(mem_peak) <= BOUND);
        }}"
    );
    verifies("repeated_symbolic_branches", &body.replace("BOUND", "49"));
    rejects(
        "repeated_symbolic_branches_short",
        &body.replace("BOUND", "48"),
        "conditional memory budget exceeded",
    );
}

#[test]
fn symbolic_checkpoint_retains_costs_from_both_branches() {
    let body = "fn f(cap: usize, flag: bool)
        requires cap == 4, SELECTOR,
        mem_peak <= 100,
    {
        let v = Vec::<u32>::with_capacity(cap);
        if flag { let a = [0u8; 24]; } else { let b = [0u8; 32]; }
        assert(current(mem_peak) <= BOUND);
    }";
    verifies("symbolic_branch_costs", &body.replace("SELECTOR", "true").replace("BOUND", "81"));
    for (selector, bound) in [("flag", "72"), ("!flag", "80")] {
        rejects(
            "symbolic_branch_costs_short",
            &body.replace("SELECTOR", selector).replace("BOUND", bound),
            "conditional memory budget exceeded",
        );
    }
}
