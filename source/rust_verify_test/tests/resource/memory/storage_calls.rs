use crate::common::*;
use crate::verify_one_file;

fn caller_example() -> String {
    include_str!("../../../../../examples/resource/memory/algorithms/calls.rs").replace(
        "#[path = \"insertion_sort.rs\"]\nmod sorting;",
        &format!(
            "mod sorting {{ {} }}",
            include_str!("../../../../../examples/resource/memory/algorithms/insertion_sort.rs")
        ),
    )
}

#[test]
fn complete_sorting_call_chain() {
    verify_one_file("complete_sorting_call_chain", caller_example(), &[]).unwrap();
}

#[test]
fn complete_sorting_call_chain_one_byte_short() {
    let code = caller_example().replace("value_size([u32; 8])", "31u64");
    let err = verify_one_file("complete_sorting_call_chain_one_byte_short", code, &[]).unwrap_err();
    assert_vir_error_msg(err, "peak 76 bytes exceeds budget 75 bytes");
}

test_verify_one_file! {
    #[test] caller_slots_overlap_callee_peak verus_code! {
        fn caller() resources peak(memory) <= 16 {
            let local = 1u32;
            callee(local);
        }
        fn callee(x: u32) resources peak(memory) <= 12 { let y = x; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] caller_plus_callee_one_byte_short verus_code! {
        fn caller() resources peak(memory) <= 15 {
            let local = 1u32;
            callee(local);
        }
        fn callee(x: u32) resources peak(memory) <= 12 { let y = x; }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds budget 15 bytes")
}

test_verify_one_file! {
    #[test] scalar_arguments_use_parameter_storage verus_code! {
        fn leaf(a: u32, b: u32) resources peak(memory) <= 8 {}
        fn caller() resources peak(memory) <= 7 { leaf(1, 2); }
    } => Err(err) => assert_vir_error_msg(err, "peak 8 bytes exceeds budget 7 bytes")
}

test_verify_one_file! {
    #[test] earlier_arguments_survive_later_evaluation verus_code! {
        fn leaf(a: u32, b: u32) resources peak(memory) <= 8 {}
        fn caller() resources peak(memory) <= 15 {
            let x = 1u32;
            let y = 2u32;
            leaf(x, x + y);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds budget 15 bytes")
}

test_verify_one_file! {
    #[test] callee_declared_bound_is_used verus_code! {
        fn leaf() resources peak(memory) <= 40 {}
        fn caller() resources peak(memory) <= 39 { leaf(); }
    } => Err(err) => assert_vir_error_msg(err, "peak 40 bytes exceeds budget 39 bytes")
}

test_verify_one_file! {
    #[test] sequential_calls_reuse_storage verus_code! {
        fn leaf() resources peak(memory) <= 40 {}
        fn caller() resources peak(memory) <= 40 { leaf(); leaf(); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] transitive_contracts verus_code! {
        fn outer() resources peak(memory) <= 20 {
            let local = 1u32;
            middle();
        }
        fn middle() resources peak(memory) <= 16 {
            let local = 1u32;
            leaf();
        }
        fn leaf() resources peak(memory) <= 12 { let x = 1u32; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] invalid_callee_contract_is_checked verus_code! {
        fn caller() resources peak(memory) <= 100 { leaf(); }
        fn leaf() resources peak(memory) <= 0 { let x = 1u32; }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] invalid_unreachable_callee_contract_is_checked verus_code! {
        fn caller() resources peak(memory) <= 100 { if false { leaf(); } }
        fn leaf() resources peak(memory) <= 0 { let x = 1u32; }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] functional_preconditions_still_checked verus_code! {
        fn leaf(x: u32) requires x > 0, resources peak(memory) <= 4 {}
        fn caller() resources peak(memory) <= 8 { leaf(0); }
    } => Err(err) => assert_vir_error_msg(err, "precondition not satisfied")
}

test_verify_one_file! {
    #[test] functional_callee_proof_still_checked verus_code! {
        fn caller() resources peak(memory) <= 0 { leaf(); }
        fn leaf() ensures false, resources peak(memory) <= 0 {}
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file! {
    #[test] self_recursion_cannot_justify_zero_budget verus_code! {
        fn recursive() resources peak(memory) <= 0 { recursive(); }
    } => Err(err) => assert_vir_error_msg(err, "recursive memory contracts")
}

test_verify_one_file! {
    #[test] mutual_recursion_cannot_justify_zero_budget verus_code! {
        fn first() resources peak(memory) <= 0 { second(); }
        fn second() resources peak(memory) <= 0 { first(); }
    } => Err(err) => assert_vir_error_msg(err, "recursive memory contracts")
}

test_verify_one_file! {
    #[test] lifetime_extended_argument_temporary_rejected verus_code! {
        use vstd::prelude::*;
        fn leaf(x: &[u32]) resources peak(memory) <= 16 {}
        fn caller() resources peak(memory) <= 1000 { leaf(&[0u32; 4]); }
    } => Err(err) => assert_vir_error_msg(err, "borrowed temporary")
}

test_verify_one_file! {
    #[test] mutable_array_to_slice_call verus_code! {
        use vstd::prelude::*;
        fn leaf(x: &mut [u32])
            requires old(x).len() > 0,
            ensures final(x)@[0] == 42,
            resources peak(memory) <= 52,
        { x[0] = 42; }
        fn caller() resources peak(memory) <= 68 {
            let mut array = [0u32; 4];
            leaf(&mut array);
            assert(array[0] == 42);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] shared_array_to_slice_call verus_code! {
        use vstd::prelude::*;
        fn leaf(x: &[u32]) resources peak(memory) <= 16 {}
        fn caller() resources peak(memory) <= 32 {
            let array = [0u32; 4];
            leaf(&array);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] coercion_and_handoff_keep_backing_array_live verus_code! {
        use vstd::prelude::*;
        fn leaf(x: &[u32]) resources peak(memory) <= 16 {}
        fn caller() resources peak(memory) <= 31 {
            let array = [0u32; 4];
            leaf(&array);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 31 bytes")
}

test_verify_one_file! {
    #[test] direct_unsizing_helper_is_not_coercion_syntax verus_code! {
        use vstd::prelude::*;
        fn caller() resources peak(memory) <= 1000 {
            let array = [0u32; 4];
            let slice = vstd::array::array_as_slice(&array);
        }
    } => Err(err) => assert_vir_error_msg(err, "does not support calls")
}

test_verify_one_file! {
    #[test] generic_callees_remain_rejected verus_code! {
        fn leaf<T>() {}
        fn caller() resources peak(memory) <= 0 { leaf::<u32>(); }
    } => Err(err) => assert_vir_error_msg(err, "does not support calls")
}

test_verify_one_file! {
    #[test] borrowed_slice_local_and_reborrow verus_code! {
        use vstd::prelude::*;
        fn leaf(x: &mut [u32]) resources peak(memory) <= 16 {}
        fn caller() resources peak(memory) <= 48 {
            let mut array = [0u32; 4];
            let slice: &mut [u32] = &mut array;
            leaf(slice);
            leaf(slice);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] summary_addition_overflow_is_rejected verus_code! {
        fn leaf() resources peak(memory) <= 18446744073709551615 {}
        fn caller() resources peak(memory) <= 18446744073709551615 {
            let local = 0u32;
            leaf();
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}

test_verify_one_file! {
    #[test] array_value_argument_copies_are_charged verus_code! {
        use vstd::prelude::*;
        fn leaf(x: [u32; 4]) resources peak(memory) <= 16 {}
        fn caller() resources peak(memory) <= 31 {
            let array = [0u32; 4];
            leaf(array);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 31 bytes")
}

test_verify_one_file! {
    #[test] callee_below_parameter_size_is_rejected verus_code! {
        fn caller() resources peak(memory) <= 100 { leaf(0); }
        fn leaf(x: u32) resources peak(memory) <= 0 {}
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] implicit_reborrow_handoff_is_charged verus_code! {
        use vstd::prelude::*;
        fn leaf(x: &mut [u32]) resources peak(memory) <= 16 {}
        fn caller(x: &mut [u32]) resources peak(memory) <= 31 { leaf(x); }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 31 bytes")
}

test_verify_one_file! {
    #[test] shared_coercion_charges_only_source_slots verus_code! {
        use vstd::prelude::*;
        fn caller() resources peak(memory) <= 31 {
            let array = [0u32; 4];
            let slice: &[u32] = &array;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 31 bytes")
}

test_verify_one_file! {
    #[test] unreachable_recursion_is_still_rejected verus_code! {
        fn recursive() resources peak(memory) <= 1 {
            if false { recursive(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive memory contracts")
}
