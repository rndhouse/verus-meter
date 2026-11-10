use super::support::exact_peak;
use crate::common::*;
use crate::verify_one_file;

#[test]
fn slice_loop_workspace_exact_budget() {
    // Iterations reuse the local value's storage; one byte less must still fail.
    exact_peak(
        "slice_loop_workspace",
        r"fn visit(values: &mut [u32]) resources peak(memory) <= BUDGET {
            let mut i = 0usize;
            while i < values.len()
                invariant i <= values.len(),
                decreases values.len() - i,
            {
                let saved = values[i];
                values[i] = saved;
                i += 1;
            }
        }",
        28,
    );
}

test_verify_one_file! {
    #[test] memory_contract_does_not_bypass_loop_invariant verus_code! {
        use vstd::prelude::*;
        fn visit(values: &mut [u32])
            requires old(values).len() > 0,
            resources peak(memory) <= ref_size(values) + value_size(usize),
        {
            let mut i = 0usize;
            while i < values.len()
                invariant
                    i <= values.len(),
                    i == 0, // FAILS
                decreases values.len() - i,
            {
                values[i] = 0;
                i += 1;
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] usize_slot_has_model_word_size verus_code! {
        fn f(x: usize) resources peak(memory) <= 7 {}
    } => Err(err) => assert_vir_error_msg(err, "peak 8 bytes exceeds budget 7 bytes")
}

test_verify_one_file! {
    #[test] arbitrary_length_slice_is_descriptor_only verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32]) resources peak(memory) <= 16 {}
        fn g(x: &[u32]) resources peak(memory) <= 16 {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] slice_descriptor_is_not_zero verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32]) resources peak(memory) <= 15 {}
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds budget 15 bytes")
}

test_verify_one_file! {
    #[test] scalar_arithmetic_exact_budget verus_code! {
        fn f(x: u32, y: u32)
            requires x <= 10, y <= 10,
            resources peak(memory) <= 12,
        { let z = x + y; assert(z == x + y); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] arithmetic_result_local_is_charged verus_code! {
        fn f(x: u32, y: u32)
            requires x <= 10, y <= 10,
            resources peak(memory) <= 11,
        { let z = x + y; }
    } => Err(err) => assert_vir_error_msg(err, "peak 12 bytes exceeds budget 11 bytes")
}

test_verify_one_file! {
    #[test] overflow_checks_remain_active verus_code! {
        fn f(x: u32) resources peak(memory) <= 100 {
            let z = x + 1; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] compound_assignment_keeps_parameter_charge verus_code! {
        fn f(mut i: usize) requires i < 10, resources peak(memory) <= 7 {
            i += 1;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 8 bytes exceeds budget 7 bytes")
}

test_verify_one_file! {
    #[test] slice_read_exact_budget verus_code! {
        use vstd::prelude::*;
        fn f(x: &[u32], i: usize)
            requires i < x.len(),
            resources peak(memory) <= 28,
        { let value = x[i]; assert(value == x@[i as int]); }
        fn g(x: &mut [u32], i: usize)
            requires i < old(x).len(),
            resources peak(memory) <= 28,
        { let value = x[i]; assert(value == x@[i as int]); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] indexed_read_charges_destination_local verus_code! {
        use vstd::prelude::*;
        fn f(x: &[u32], i: usize)
            requires i < x.len(),
            resources peak(memory) <= 27,
        { let value = x[i]; }
    } => Err(err) => assert_vir_error_msg(err, "peak 28 bytes exceeds budget 27 bytes")
}

test_verify_one_file! {
    #[test] slice_write_exact_budget verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32], i: usize, value: u32)
            requires i < old(x).len(),
            ensures final(x)@ == old(x)@.update(i as int, value),
            resources peak(memory) <= 28,
        { x[i] = value; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] indexed_assignment_keeps_all_parameters verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32], i: usize, j: usize)
            requires i < old(x).len(), j < old(x).len(),
            resources peak(memory) <= 31,
        { x[i] = x[j]; }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 31 bytes")
}

test_verify_one_file! {
    #[test] copy_between_indices_exact_budget verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32], i: usize, j: usize)
            requires i < old(x).len(), j < old(x).len(),
            ensures final(x)@ == old(x)@.update(i as int, old(x)@[j as int]),
            resources peak(memory) <= 32,
        { x[i] = x[j]; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] bounds_checks_remain_active verus_code! {
        use vstd::prelude::*;
        fn f(x: &[u32], i: usize) resources peak(memory) <= 60 {
            let value = x[i]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] shared_dereference_charges_reference_and_local verus_code! {
        fn f(x: &u32) resources peak(memory) <= 11 { let value = *x; }
    } => Err(err) => assert_vir_error_msg(err, "peak 12 bytes exceeds budget 11 bytes")
}

test_verify_one_file! {
    #[test] copying_borrowed_array_charges_the_copy verus_code! {
        use vstd::prelude::*;
        fn f(x: &[u32; 64]) resources peak(memory) <= 263 { let copy = *x; }
    } => Err(err) => assert_vir_error_msg(err, "peak 264 bytes exceeds budget 263 bytes")
}

test_verify_one_file! {
    #[test] named_place_borrows_are_supported verus_code! {
        fn f() resources peak(memory) <= 12 {
            let x = 0u32;
            let reference = &x;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrowed_array_temporary_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 10000 { let reference = &[0u32; 64]; }
    } => Err(err) => assert_vir_error_msg(err, "borrowed temporary")
}

test_verify_one_file! {
    #[test] borrowed_mutable_temporary_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 10000 { let reference = &mut [0u32; 64]; }
    } => Err(err) => assert_vir_error_msg(err, "borrowed temporary")
}

test_verify_one_file! {
    #[test] user_method_named_len_is_not_an_intrinsic verus_code! {
        struct Other {}
        impl Other { fn len(&self) -> usize { 0 } }
        fn f() resources peak(memory) <= 10000 { let n = (Other {}).len(); }
    } => Err(err) => assert_vir_error_msg(err, "does not support calls")
}

test_verify_one_file! {
    #[test] primitive_slice_length verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32]) resources peak(memory) <= 24 {
            let n = x.len();
            assert(n == x@.len());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] slice_length_charges_result_local verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32]) resources peak(memory) <= 23 { let n = x.len(); }
    } => Err(err) => assert_vir_error_msg(err, "peak 24 bytes exceeds budget 23 bytes")
}

test_verify_one_file! {
    #[test] array_indexing_does_not_copy_the_array verus_code! {
        use vstd::prelude::*;
        fn f(mut a: [u32; 64], i: usize, value: u32)
            requires i < 64,
            resources peak(memory) <= 268,
        { a[i] = value; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] compound_assignment_through_reference verus_code! {
        fn f(x: &mut usize)
            requires *old(x) < 10,
            resources peak(memory) <= 7,
        { *x += 1; }
    } => Err(err) => assert_vir_error_msg(err, "peak 8 bytes exceeds budget 7 bytes")
}

test_verify_one_file! {
    #[test] element_borrow_retains_backing_storage verus_code! {
        use vstd::prelude::*;
        fn f(x: &mut [u32])
            requires old(x).len() > 0,
            ensures final(x)@ == old(x)@.update(0, 42u32),
            resources peak(memory) <= 24,
        {
            let element = &mut x[0];
            *element = 42;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_references_are_explicitly_rejected verus_code! {
        fn f(x: &&u32) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "nested references")
}
