use crate::common::*;
use crate::verify_one_file;

fn assert_memory_failure(err: TestErr, source: &str) {
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].message.contains("conditional memory budget exceeded"));
    assert!(
        err.errors[0]
            .spans
            .iter()
            .any(|span| span.is_primary && span.text.iter().any(|line| line.text.contains(source)))
    );
}

test_verify_one_file! {
    #[test] shadowing_does_not_change_the_input_bound verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool) resources peak(memory) <= 2 + if flag { 32 } else { 16 } {
            let flag = true;
            if flag { let scratch = [0u32; 8]; }
        }
    } => Err(err) => assert_memory_failure(err, "let scratch")
}

test_verify_one_file! {
    #[test] preceding_proofs_can_connect_a_local_choice_to_the_input verus_code! {
        use vstd::prelude::*;
        fn f(large: bool) resources peak(memory) <= 2 + if large { 32 } else { 16 } {
            let small = !large;
            assert(small == !large);
            if small { let scratch = [0u32; 4]; }
            else { let scratch = [0u32; 8]; }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unit_initializer_calls_are_checked verus_code! {
        use vstd::prelude::*;
        fn helper() resources peak(memory) <= 16 {}
        fn f(flag: bool) resources peak(memory) <= owned_size(flag) + if flag { 32 } else { 16 } {
            let unit: () = helper();
            let scratch = [0u32; 4];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] earlier_parameters_remain_live_during_later_argument_calls verus_code! {
        use vstd::prelude::*;
        fn helper() resources peak(memory) <= 16 {}
        fn callee(data: [u32; 4], unit: ()) resources peak(memory) <= owned_size(data) {}
        fn f(flag: bool) resources peak(memory) <= owned_size(flag) + if flag { 32 } else { 16 } {
            callee([0u32; 4], helper());
        }
    } => Err(err) => assert_memory_failure(err, "helper()")
}

test_verify_one_file! {
    #[test] struct_declarations_are_checked verus_code! {
        use vstd::prelude::*;
        struct Buffer { data: [u32; 8] }
        fn f(flag: bool) resources peak(memory) <= owned_size(flag) + if flag { owned_size(Buffer) } else { 16 } {
            let buffer = Buffer { data: [0u32; 8] };
        }
    } => Err(err) => assert_memory_failure(err, "let buffer")
}

test_verify_one_file! {
    #[test] spec_function_predicates_are_not_silently_trusted verus_code! {
        spec fn choose(flag: bool) -> bool { flag }
        fn f(flag: bool) resources peak(memory) <= if choose(flag) { 1 } else { 0 } {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently support")
}

test_verify_one_file! {
    #[test] scalar_input_types_and_equality verus_code! {
        use vstd::prelude::*;
        fn f(count: usize, small: bool) requires small == (count == 0),
            resources peak(memory) <= owned_size(count) + owned_size(small) + if count != 0 { 32 } else { 16 },
        {
            if small { let scratch = [0u32; 4]; }
            else { let scratch = [0u32; 8]; }
        }
    } => Ok(())
}

#[test]
fn conditional_workspace_example() {
    verify_one_file(
        "conditional_workspace_example",
        include_str!("../../../../../examples/resource/memory/contracts/conditional.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] calls_use_the_selected_allowance verus_code! {
        use vstd::prelude::*;
        fn helper(large: bool) resources peak(memory) <= owned_size(large) + if large { 32 } else { 16 } {
            if large { let scratch = [0u32; 8]; }
            else { let scratch = [0u32; 4]; }
        }
        fn caller() resources peak(memory) <= 17 { helper(false); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrowed_call_arguments_remain_valid verus_code! {
        use vstd::prelude::*;
        fn helper(data: &mut [u32; 4]) resources peak(memory) <= ref_size(data) { data[0] = 9; }
        fn f(flag: bool) resources peak(memory) <= owned_size(flag) + owned_size([u32; 4]) + if flag { mem_peak(helper) } else { mem_peak(helper) } {
            let mut data = [0u32; 4];
            helper(&mut data);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] calls_must_fit_the_selected_allowance verus_code! {
        fn helper() resources peak(memory) <= 32 {}
        fn f(flag: bool) resources peak(memory) <= owned_size(flag) + if flag { 32 } else { 16 } {
            helper(); // FAILS
        }
    } => Err(err) => assert_memory_failure(err, "helper();")
}

test_verify_one_file! {
    #[test] standalone_aggregates_are_checked verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool) resources peak(memory) <= owned_size(flag) + if flag { 32 } else { 16 } {
            [0u32; 8]; // FAILS
        }
    } => Err(err) => assert_memory_failure(err, "[0u32; 8]")
}

test_verify_one_file! {
    #[test] loop_allocations_use_the_input_bound verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool, mut run: bool) resources peak(memory) <= 2 + if flag { 32 } else { 16 } {
            while run decreases if run { 1int } else { 0int }, {
                if flag { let scratch = [0u32; 8]; }
                else { let scratch = [0u32; 4]; }
                run = false;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_over_budget_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool, mut run: bool) resources peak(memory) <= 2 + if flag { 32 } else { 16 } {
            while run decreases if run { 1int } else { 0int }, {
                let scratch = [0u32; 8]; // FAILS
                run = false;
            }
        }
    } => Err(err) => assert_memory_failure(err, "let scratch")
}

test_verify_one_file! {
    #[test] smaller_branch_bound_is_enforced verus_code! {
        use vstd::prelude::*;
        fn f(large: bool) resources peak(memory) <= owned_size(large) + if large { 32 } else { 16 } {
            if large { let scratch = [0u32; 8]; }
            else { let scratch = [0u32; 8]; } // FAILS
        }
    } => Err(err) => assert_memory_failure(err, "let scratch")
}

test_verify_one_file! {
    #[test] scalar_comparisons_need_not_be_spelled_identically verus_code! {
        use vstd::prelude::*;
        fn f(count: u32) resources peak(memory) <= owned_size(count) + if count <= 4 { 16 } else { 32 } {
            if count > 4 { let scratch = [0u32; 8]; }
            else { let scratch = [0u32; 4]; }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] preconditions_eliminate_unreachable_costs verus_code! {
        use vstd::prelude::*;
        fn f(count: u32) requires count <= 4,
            resources peak(memory) <= owned_size(count) + if count <= 4 { 16 } else { 0 },
        {
            if count > 4 { let scratch = [0u32; 1024]; }
            else { let scratch = [0u32; 4]; }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unconditional_storage_must_fit_both_cases verus_code! {
        use vstd::prelude::*;
        fn f(large: bool) resources peak(memory) <= owned_size(large) + if large { 32 } else { 16 } {
            let scratch = [0u32; 8]; // FAILS
        }
    } => Err(err) => assert_memory_failure(err, "let scratch")
}

test_verify_one_file! {
    #[test] parameters_count_even_without_allocations verus_code! {
        fn f(flag: bool) resources peak(memory) <= if flag { 1 } else { 0 } {} // FAILS
    } => Err(err) => assert_memory_failure(err, "fn f")
}

test_verify_one_file! {
    #[test] conditional_sections_are_not_silently_maximized verus_code! {
        fn f(flag: bool) resources peak(memory) <= 1 { resources peak(memory) <= if flag { 0 } else { 1 } {} }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory bounds currently require a function contract")
}

test_verify_one_file! {
    #[test] conditional_checkpoints_are_not_silently_maximized verus_code! {
        fn f(flag: bool) resources peak(memory) <= 1 { assert(peak(memory) <= if flag { 1 } else { 0 }); }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory bounds currently require a function contract")
}

test_verify_one_file! {
    #[test] mutable_predicate_inputs_are_rejected verus_code! {
        fn f(mut flag: bool) resources peak(memory) <= if flag { 1 } else { 0 } { flag = true; }
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently require immutable")
}

test_verify_one_file! {
    #[test] side_effecting_predicates_are_rejected verus_code! {
        fn f(flag: bool) resources peak(memory) <= if { let other = true; other } { 1 } else { 0 } {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget predicates currently support")
}

test_verify_one_file! {
    #[test] branch_budget_overflow_is_rejected verus_code! {
        fn f(flag: bool) resources peak(memory) <= if flag { 18446744073709551615u64 + 1 } else { 1 } {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] cycle_in_either_budget_branch_is_rejected verus_code! {
        fn f(flag: bool) resources peak(memory) <= if flag { 1 } else { 0 * mem_peak(f) } {}
    } => Err(err) => assert_vir_error_msg(err, "circular mem_peak reference")
}

test_verify_one_file! {
    #[test] conditional_bounds_do_not_prove_functional_claims verus_code! {
        fn f(flag: bool) resources peak(memory) <= if flag { 1 } else { 1 } {
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] fixed_sections_compose_with_conditional_function verus_code! {
        use vstd::prelude::*;
        fn f(large: bool) resources peak(memory) <= owned_size(large) + if large { 32 } else { 16 } {
            if large { resources peak(memory) <= 32 { let scratch = [0u32; 8]; } }
            else { resources peak(memory) <= 16 { let scratch = [0u32; 4]; } }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] boolean_formula_and_nested_budget verus_code! {
        use vstd::prelude::*;
        fn f(a: bool, b: bool) resources peak(memory) <= 2 + if a && !b { 32 } else { if b { 16 } else { 0 } } {
            if a && !b { let scratch = [0u32; 8]; }
            else { if b { let scratch = [0u32; 4]; } }
        }
    } => Ok(())
}
