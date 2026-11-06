#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

fn assert_memory_failure(err: TestErr) {
    assert!(!err.errors.is_empty());
    assert!(err.errors.iter().any(|e| e.message.contains("conditional memory budget exceeded")));
}

test_verify_one_file! {
    #[test] constant_call_query verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= mem_peak(helper(false)) { helper(false); assert(current(mem_peak) <= mem_peak(helper(false))); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] large_call_query verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= mem_peak(helper(true)) { helper(true); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] small_allowance_rejects_large_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= mem_peak(helper(false)) { helper(true); }
    } => Err(err) => assert_vir_error_msg(err, "peak 33 bytes exceeds budget 17 bytes")
}

test_verify_one_file! {
    #[test] one_byte_short verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= 16 { helper(false); }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds budget 16 bytes")
}

test_verify_one_file! {
    #[test] argument_free_query_retains_envelope verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= mem_peak(helper) { helper(true); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] caller_precondition_specializes_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, mem_peak <= 18 { helper(flag); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] missing_precondition_fails_at_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) mem_peak <= 18 { helper(flag); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] conditional_branch_specializes_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) mem_peak <= 18 { if !flag { helper(flag); } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] immutable_local_selects_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= 18 { let small = false; helper(small); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_choice_must_fit verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= 18 { let large = true; helper(large); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] forwarded_contracts_compose verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn middle(flag: bool) mem_peak <= mem_size(flag) + mem_peak(helper(flag)) { helper(flag); }
fn outer(flag: bool) mem_peak <= mem_size(flag) + mem_peak(middle(flag)) { middle(flag); }
fn f() mem_peak <= mem_peak(outer(false)) { outer(false); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] conditional_caller_must_cover_callee verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) mem_peak <= mem_size(flag) + mem_peak(helper(!flag)) { helper(flag); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] caller_storage_stays_live verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= mem_peak(helper(false)) { let kept = [0u32; 4]; helper(false); }
    } => Err(err) => assert_vir_error_msg(err, "peak 33 bytes exceeds budget 17 bytes")
}

test_verify_one_file! {
    #[test] caller_storage_with_symbolic_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, mem_peak <= 18 { let kept = [0u32; 4]; helper(flag); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] constant_call_in_section verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= 33 { let kept = [0u32; 4]; mem_peak <= mem_peak(helper(false)) { helper(false); } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] symbolic_call_in_section verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, mem_peak <= 18 { mem_peak <= 17 { helper(flag); } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] section_bound_is_independently_enforced verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) mem_peak <= 100 { mem_peak <= 17 { helper(flag); } }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] symbolic_checkpoint_remains_conservative verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, mem_peak <= 18 { helper(flag); assert(current(mem_peak) <= 18); }
    } => Err(err) => assert_vir_error_msg(err, "mem_peak assertion failed: peak 34 bytes exceeds bound 18 bytes")
}

test_verify_one_file! {
    #[test] mutable_selector_falls_back verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= 18 { let mut flag = false; helper(flag); }
    } => Err(err) => assert_vir_error_msg(err, "peak 34 bytes exceeds budget 18 bytes")
}

test_verify_one_file! {
    #[test] mutable_selector_accepts_envelope verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= 34 { let mut flag = false; helper(flag); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] side_effecting_selector_falls_back verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= 17 { helper({ assert(true); false }); }
    } => Err(err) => assert_vir_error_msg(err, "value-returning blocks")
}

test_verify_one_file! {
    #[test] query_rejects_mutable_input verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(mut flag: bool) mem_peak <= mem_size(flag) + mem_peak(helper(flag)) { helper(flag); }
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently require immutable")
}

test_verify_one_file! {
    #[test] query_rejects_side_effects verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() mem_peak <= mem_peak(helper({ let flag = false; flag })) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently support")
}

test_verify_one_file! {
    #[test] query_does_not_call_or_require_preconditions verus_code! {
use vstd::prelude::*;
fn unused(flag: bool) requires false, mem_peak <= if flag { 33 } else { 17 } { assert(false); }
fn f() mem_peak <= mem_peak(unused(false)) { let data = [0u32; 4]; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] actual_call_still_requires_precondition verus_code! {
use vstd::prelude::*;
fn unused(flag: bool) requires false, mem_peak <= if flag { 33 } else { 17 } {}
fn f() mem_peak <= mem_peak(unused(false)) { unused(false); }
    } => Err(err) => assert_vir_error_msg(err, "precondition not satisfied")
}

test_verify_one_file! {
    #[test] declaration_slack_is_preserved verus_code! {
use vstd::prelude::*;
fn unused(flag: bool) mem_peak <= if flag { 33 } else { 17 } {}
fn f() mem_peak <= 1 { unused(false); }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds budget 1 bytes")
}

test_verify_one_file! {
    #[test] earlier_argument_slots_overlap_later_calls verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn sink(data: [u32; 4], done: ()) mem_peak <= 16 {}
fn f() mem_peak <= mem_peak(helper(false)) { sink([0u32; 4], helper(false)); }
    } => Err(err) => assert_vir_error_msg(err, "peak 33 bytes exceeds budget 17 bytes")
}

test_verify_one_file! {
    #[test] earlier_argument_slots_overlap_symbolic_calls verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn sink(data: [u32; 4], done: ()) mem_peak <= 16 {}
fn f(flag: bool) requires !flag, mem_peak <= 18 { sink([0u32; 4], helper(flag)); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] borrowed_other_argument_is_supported verus_code! {
use vstd::prelude::*;
fn work(flag: bool, data: &mut [u32; 4]) mem_peak <= mem_size(flag) + mem_size(data) + if flag { 32 } else { 16 } {
    if flag { let scratch = [0u32; 8]; } else { let scratch = [0u32; 4]; }
    data[0] = 9;
}
fn f(flag: bool) requires !flag, mem_peak <= 42 { let mut data = [0u32; 4]; work(flag, &mut data); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] multiple_scalar_arguments_and_comparisons verus_code! {
use vstd::prelude::*;
fn work(count: u32, flag: bool) mem_peak <= 5 + if count <= 4 && !flag { 16 } else { 32 } {
    if count > 4 || flag { let data = [0u32; 8]; } else { let data = [0u32; 4]; }
}
fn f() mem_peak <= mem_peak(work(4u32, false)) { work(4u32, false); assert(current(mem_peak) <= 21); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] specialized_cycles_still_rejected verus_code! {
use vstd::prelude::*;
fn f(flag: bool) mem_peak <= 1 + 0 * mem_peak(f(false)) {}
    } => Err(err) => assert_vir_error_msg(err, "circular mem_peak reference")
}

test_verify_one_file! {
    #[test] specialization_cannot_hide_invalid_branch verus_code! {
use vstd::prelude::*;
fn f(flag: bool) mem_peak <= if flag { 18446744073709551615u64 + 1 } else { 1 } {}
fn g() mem_peak <= mem_peak(f(false)) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] call_cycle_still_rejected verus_code! {
use vstd::prelude::*;
fn f(flag: bool) mem_peak <= if flag { 100 } else { 100 } { f(false); }
    } => Err(err) => assert_vir_error_msg(err, "recursive storage contracts")
}

test_verify_one_file! {
    #[test] fixed_local_costs_remain_structural verus_code! {
use vstd::prelude::*;
fn helper(large: bool) mem_peak <= mem_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, mem_peak <= 18 { helper(flag); if false { let big = [0u32; 100]; } }
    } => Err(err) => assert_vir_error_msg(err, "peak 401 bytes exceeds budget 18 bytes")
}

test_verify_one_file! {
    #[test] invalid_query_even_when_unused verus_code! {
use vstd::prelude::*;
fn f(flag: bool) mem_peak <= 1 {}
fn g() mem_peak <= 0 * mem_peak(f({ let b = false; b })) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently support")
}

#[test]
fn call_budgets_example() {
    verify_one_file(
        "call_budgets_example",
        include_str!("../../../examples/resource/memory/call_budgets.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] aliases_and_zero_argument_queries verus_code! {
        mod inner { pub fn work(flag: bool) mem_peak <= if flag { 33 } else { 17 } {} }
        use inner::work as renamed;
        fn forward() mem_peak <= mem_peak(renamed(false)) { renamed(false); }
        fn f() mem_peak <= mem_peak(forward()) { forward(); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] later_argument_cannot_change_a_specialized_selector verus_code! {
        fn change(flag: &mut bool) mem_peak <= mem_size(flag) { *flag = true; }
        fn work(flag: bool, done: ()) mem_peak <= if flag { 33 } else { 17 } {}
        fn f() mem_peak <= 18 {
            let mut flag = false;
            work(flag, change(&mut flag));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 34 bytes exceeds budget 18 bytes")
}

test_verify_one_file! {
    #[test] symbolic_calls_in_reusable_loop verus_code! {
        fn work(flag: bool) mem_peak <= if flag { 33 } else { 17 } {}
        fn f(flag: bool, mut run: bool) requires !flag, mem_peak <= 19 {
            while run invariant !flag, decreases if run { 1int } else { 0int }, {
                work(flag);
                run = false;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] constant_conditional_contract_keeps_proof_semantics verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= if false { 1 } else { 0 } {
            if false { let data = [0u32; 4]; }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] direct_call_builtin_is_not_an_ordinary_spec_function verus_code! {
        fn helper() mem_peak <= 0 {}
        fn f() { let x = verus_builtin::resource_mem_peak_call(helper()); }
    } => Err(err) => assert_vir_error_msg(err, "mem_size and mem_peak are only allowed inside a mem_peak clause or checkpoint")
}
