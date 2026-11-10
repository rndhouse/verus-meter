use crate::common::*;
use crate::verify_one_file;

fn assert_memory_failure(err: TestErr) {
    assert!(!err.errors.is_empty());
    assert!(err.errors.iter().any(|e| e.message.contains("conditional memory budget exceeded")));
}

test_verify_one_file! {
    #[test] unused_conditional_maximum_can_exceed_live_storage_range verus_code! {
        fn helper(flag: bool)
            resources peak(memory) <= if flag { 18446744073709551615 } else { 1 },
        {}
        fn caller(flag: bool) requires !flag, resources peak(memory) <= 2 {
            helper(flag);
            helper(flag);
            let later = 0u8;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] selected_conditional_maximum_must_still_fit verus_code! {
        fn helper(flag: bool)
            resources peak(memory) <= if flag { 18446744073709551615 } else { 1 },
        {}
        fn caller(flag: bool) requires flag, resources peak(memory) <= 18446744073709551615 {
            helper(flag);
        }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] unused_conditional_maximum_with_dynamic_backing verus_code! {
        use vstd::prelude::*;
        fn helper(flag: bool)
            resources peak(memory) <= if flag { 18446744073709551615 } else { 1 },
        {}
        fn caller(cap: usize, flag: bool)
            requires cap <= 4, !flag,
            resources peak(memory) <= 50,
        {
            let owner = Vec::<u32>::with_capacity(cap);
            helper(flag);
            drop(owner);
            let later = [0u8; 8];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] large_conditional_envelope_keeps_dynamic_backing_charged verus_code! {
        use vstd::prelude::*;
        fn helper(flag: bool)
            resources peak(memory) <= if flag { 18446744073709551615 } else { 1 },
        {}
        fn caller(cap: usize, flag: bool)
            requires cap <= 4, !flag,
            resources peak(memory) <= 49,
        {
            let owner = Vec::<u32>::with_capacity(cap);
            helper(flag);
        }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] unused_conditional_maximum_with_return_destination verus_code! {
        fn helper(flag: bool) -> (result: u8)
            ensures result == 7,
            resources peak(memory) <= if flag { 18446744073709551615 } else { 2 },
        { 7 }
        fn caller(flag: bool) requires !flag, resources peak(memory) <= 3 {
            let result = helper(flag);
            assert(result == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unused_conditional_maximum_inside_section verus_code! {
        fn helper(flag: bool)
            resources peak(memory) <= if flag { 18446744073709551615 } else { 1 },
        {}
        fn caller(flag: bool) requires !flag, resources peak(memory) <= 3 {
            resources peak(memory) <= 2 {
                let local = 0u8;
                helper(flag);
            }
            assert(peak(memory) <= 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unselected_conditional_envelope_does_not_inflate_checkpoint verus_code! {
        fn helper(flag: bool)
            resources peak(memory) <= if flag { 18446744073709551615 } else { 1 },
        {}
        fn caller(flag: bool) requires !flag, resources peak(memory) <= 2 {
            helper(flag);
            assert(peak(memory) <= 18446744073709551615);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] conditional_call_after_argument_drop verus_code! {
        use vstd::prelude::*;
        fn helper(flag: bool, done: ())
            resources peak(memory) <= value_size(flag) + if flag { 32 } else { 0 },
        {
            if flag { let scratch = [0u8; 32]; }
        }
        fn caller(flag: bool) resources peak(memory) <= 42 {
            let owner = Box::new([0u8; 32]);
            helper(flag, { drop(owner); });
            assert(peak(memory) <= 42);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] argument_storage_before_drop_still_counts verus_code! {
        use vstd::prelude::*;
        fn helper(flag: bool, done: ())
            resources peak(memory) <= value_size(flag) + if flag { 32 } else { 0 },
        {
            if flag { let scratch = [0u8; 32]; }
        }
        fn caller(flag: bool) resources peak(memory) <= 41 {
            let owner = Box::new([0u8; 32]);
            helper(flag, { drop(owner); });
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 42 bytes exceeds budget 41 bytes")
}

test_verify_one_file! {
    #[test] conditional_call_after_dynamic_argument_drop verus_code! {
        use vstd::prelude::*;
        fn helper(flag: bool, done: ())
            resources peak(memory) <= value_size(flag) + if flag { 32 } else { 0 },
        {
            if flag { let scratch = [0u8; 32]; }
        }
        fn caller(cap: usize, flag: bool) requires cap <= 4, resources peak(memory) <= 66 {
            let owner = Vec::<u32>::with_capacity(cap);
            helper(flag, { drop(owner); });
            assert(peak(memory) <= 66);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] runtime_call_after_argument_drop verus_code! {
        use vstd::prelude::*;
        fn helper(cap: usize, done: ())
            requires cap <= 4,
            resources peak(memory) <= value_size(cap) + value_size(Vec<u32>) + cap * value_size(u32),
        {
            let scratch = Vec::<u32>::with_capacity(cap);
        }
        fn caller(cap: usize) requires cap <= 4, resources peak(memory) <= 64 {
            let owner = Box::new([0u8; 32]);
            helper(cap, { drop(owner); });
            assert(peak(memory) <= 64);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] conditional_return_after_argument_drop verus_code! {
        use vstd::prelude::*;
        fn helper(flag: bool, done: ()) -> (result: u32)
            ensures result == 7,
            resources peak(memory) <= value_size(flag) + value_size(u32) + if flag { 32 } else { 0 },
        {
            if flag { let scratch = [0u8; 32]; }
            7
        }
        fn initialized(flag: bool) resources peak(memory) <= 46 {
            let owner = Box::new([0u8; 32]);
            let result = helper(flag, { drop(owner); });
            assert(result == 7);
            assert(peak(memory) <= 46);
        }
        fn discarded(flag: bool) resources peak(memory) <= 46 {
            let owner = Box::new([0u8; 32]);
            helper(flag, { drop(owner); });
            assert(peak(memory) <= 46);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] argument_drop_keeps_other_owners_charged verus_code! {
        use vstd::prelude::*;
        fn helper(flag: bool, done: ())
            resources peak(memory) <= value_size(flag) + if flag { 64 } else { 0 },
        {
            if flag { let scratch = [0u8; 64]; }
        }
        fn caller(flag: bool) resources peak(memory) <= 105 {
            let released = Box::new([0u8; 32]);
            let retained = Box::new([0u8; 32]);
            helper(flag, { drop(released); });
        }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] constant_call_query verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= peak(helper(false)) { helper(false); assert(peak(memory) <= peak(helper(false))); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] large_call_query verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= peak(helper(true)) { helper(true); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] small_allowance_rejects_large_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= peak(helper(false)) { helper(true); }
    } => Err(err) => assert_vir_error_msg(err, "peak 33 bytes exceeds budget 17 bytes")
}

test_verify_one_file! {
    #[test] one_byte_short verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= 16 { helper(false); }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds budget 16 bytes")
}

test_verify_one_file! {
    #[test] argument_free_query_retains_envelope verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= peak(helper) { helper(true); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] caller_precondition_specializes_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, resources peak(memory) <= 18 { helper(flag); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] missing_precondition_fails_at_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) resources peak(memory) <= 18 { helper(flag); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] conditional_branch_specializes_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) resources peak(memory) <= 18 { if !flag { helper(flag); } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] immutable_local_selects_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= 18 { let small = false; helper(small); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_choice_must_fit verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= 18 { let large = true; helper(large); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] forwarded_contracts_compose verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn middle(flag: bool) resources peak(memory) <= value_size(flag) + peak(helper(flag)) { helper(flag); }
fn outer(flag: bool) resources peak(memory) <= value_size(flag) + peak(middle(flag)) { middle(flag); }
fn f() resources peak(memory) <= peak(outer(false)) { outer(false); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] conditional_caller_must_cover_callee verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) resources peak(memory) <= value_size(flag) + peak(helper(!flag)) { helper(flag); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] caller_storage_stays_live verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= peak(helper(false)) { let kept = [0u32; 4]; helper(false); }
    } => Err(err) => assert_vir_error_msg(err, "peak 33 bytes exceeds budget 17 bytes")
}

test_verify_one_file! {
    #[test] caller_storage_with_symbolic_call verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, resources peak(memory) <= 18 { let kept = [0u32; 4]; helper(flag); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] constant_call_in_section verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= 33 { let kept = [0u32; 4]; resources peak(memory) <= peak(helper(false)) { helper(false); } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] symbolic_call_in_section verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, resources peak(memory) <= 18 { resources peak(memory) <= 17 { helper(flag); } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] section_bound_is_independently_enforced verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) resources peak(memory) <= 100 { resources peak(memory) <= 17 { helper(flag); } }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] symbolic_checkpoint_preserves_selected_allowance verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, resources peak(memory) <= 18 { helper(flag); assert(peak(memory) <= 18); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutable_selector_falls_back verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= 18 { let mut flag = false; helper(flag); }
    } => Err(err) => assert_vir_error_msg(err, "peak 34 bytes exceeds budget 18 bytes")
}

test_verify_one_file! {
    #[test] mutable_selector_accepts_envelope verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= 34 { let mut flag = false; helper(flag); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] side_effecting_selector_falls_back verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= 17 { helper({ assert(true); false }); }
    } => Err(err) => assert_vir_error_msg(err, "peak 33 bytes exceeds budget 17 bytes")
}

test_verify_one_file! {
    #[test] query_rejects_mutable_input verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(mut flag: bool) resources peak(memory) <= value_size(flag) + peak(helper(flag)) { helper(flag); }
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently require immutable")
}

test_verify_one_file! {
    #[test] query_rejects_side_effects verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f() resources peak(memory) <= peak(helper({ let flag = false; flag })) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently support")
}

test_verify_one_file! {
    #[test] query_does_not_call_or_require_preconditions verus_code! {
use vstd::prelude::*;
fn unused(flag: bool) requires false, resources peak(memory) <= if flag { 33 } else { 17 } { assert(false); }
fn f() resources peak(memory) <= peak(unused(false)) { let data = [0u32; 4]; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] actual_call_still_requires_precondition verus_code! {
use vstd::prelude::*;
fn unused(flag: bool) requires false, resources peak(memory) <= if flag { 33 } else { 17 } {}
fn f() resources peak(memory) <= peak(unused(false)) { unused(false); }
    } => Err(err) => assert_vir_error_msg(err, "precondition not satisfied")
}

test_verify_one_file! {
    #[test] declaration_slack_is_preserved verus_code! {
use vstd::prelude::*;
fn unused(flag: bool) resources peak(memory) <= if flag { 33 } else { 17 } {}
fn f() resources peak(memory) <= 1 { unused(false); }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds budget 1 bytes")
}

test_verify_one_file! {
    #[test] earlier_argument_slots_overlap_later_calls verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn sink(data: [u32; 4], done: ()) resources peak(memory) <= 16 {}
fn f() resources peak(memory) <= peak(helper(false)) { sink([0u32; 4], helper(false)); }
    } => Err(err) => assert_vir_error_msg(err, "peak 33 bytes exceeds budget 17 bytes")
}

test_verify_one_file! {
    #[test] earlier_argument_slots_overlap_symbolic_calls verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn sink(data: [u32; 4], done: ()) resources peak(memory) <= 16 {}
fn f(flag: bool) requires !flag, resources peak(memory) <= 18 { sink([0u32; 4], helper(flag)); }
    } => Err(err) => assert_memory_failure(err)
}

test_verify_one_file! {
    #[test] borrowed_other_argument_is_supported verus_code! {
use vstd::prelude::*;
fn work(flag: bool, data: &mut [u32; 4]) resources peak(memory) <= value_size(flag) + ref_size(data) + if flag { 32 } else { 16 } {
    if flag { let scratch = [0u32; 8]; } else { let scratch = [0u32; 4]; }
    data[0] = 9;
}
fn f(flag: bool) requires !flag, resources peak(memory) <= 42 { let mut data = [0u32; 4]; work(flag, &mut data); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] multiple_scalar_arguments_and_comparisons verus_code! {
use vstd::prelude::*;
fn work(count: u32, flag: bool) resources peak(memory) <= 5 + if count <= 4 && !flag { 16 } else { 32 } {
    if count > 4 || flag { let data = [0u32; 8]; } else { let data = [0u32; 4]; }
}
fn f() resources peak(memory) <= peak(work(4u32, false)) { work(4u32, false); assert(peak(memory) <= 21); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] specialized_cycles_still_rejected verus_code! {
use vstd::prelude::*;
fn f(flag: bool) resources peak(memory) <= 1 + 0 * peak(f(false)) {}
    } => Err(err) => assert_vir_error_msg(err, "circular peak reference")
}

test_verify_one_file! {
    #[test] specialization_cannot_hide_invalid_branch verus_code! {
use vstd::prelude::*;
fn f(flag: bool) resources peak(memory) <= if flag { 18446744073709551615u64 + 1 } else { 1 } {}
fn g() resources peak(memory) <= peak(f(false)) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] call_cycle_still_rejected verus_code! {
use vstd::prelude::*;
fn f(flag: bool) resources peak(memory) <= if flag { 100 } else { 100 } { f(false); }
    } => Err(err) => assert_vir_error_msg(err, "recursive memory contracts")
}

test_verify_one_file! {
    #[test] fixed_local_costs_use_reachability verus_code! {
use vstd::prelude::*;
fn helper(large: bool) resources peak(memory) <= value_size(large) + if large { 32 } else { 16 } {
    if large { let scratch = [0u32; 8]; }
    else { let scratch = [0u32; 4]; }
}
fn f(flag: bool) requires !flag, resources peak(memory) <= 18 { helper(flag); if false { let big = [0u32; 100]; } }
    } => Ok(())
}

test_verify_one_file! {
    #[test] invalid_query_even_when_unused verus_code! {
use vstd::prelude::*;
fn f(flag: bool) resources peak(memory) <= 1 {}
fn g() resources peak(memory) <= 0 * peak(f({ let b = false; b })) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently support")
}

#[test]
fn call_budgets_example() {
    verify_one_file(
        "call_budgets_example",
        include_str!("../../../../../examples/resource/memory/contracts/call_budgets.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] aliases_and_zero_argument_queries verus_code! {
        mod inner { pub fn work(flag: bool) resources peak(memory) <= if flag { 33 } else { 17 } {} }
        use inner::work as renamed;
        fn forward() resources peak(memory) <= peak(renamed(false)) { renamed(false); }
        fn f() resources peak(memory) <= peak(forward()) { forward(); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] later_argument_cannot_change_a_specialized_selector verus_code! {
        fn change(flag: &mut bool) resources peak(memory) <= ref_size(flag) { *flag = true; }
        fn work(flag: bool, done: ()) resources peak(memory) <= if flag { 33 } else { 17 } {}
        fn f() resources peak(memory) <= 18 {
            let mut flag = false;
            work(flag, change(&mut flag));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 34 bytes exceeds budget 18 bytes")
}

test_verify_one_file! {
    #[test] symbolic_calls_in_reusable_loop verus_code! {
        fn work(flag: bool) resources peak(memory) <= if flag { 33 } else { 17 } {}
        fn f(flag: bool, mut run: bool) requires !flag, resources peak(memory) <= 19 {
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
        fn f() resources peak(memory) <= if false { 1 } else { 0 } {
            if false { let data = [0u32; 4]; }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] direct_call_builtin_is_not_an_ordinary_spec_function verus_code! {
        fn helper() resources peak(memory) <= 0 {}
        fn f() { let x = verus_builtin::resource_peak_call(helper()); }
    } => Err(err) => assert_vir_error_msg(err, "peak is only allowed inside a memory clause or checkpoint")
}
