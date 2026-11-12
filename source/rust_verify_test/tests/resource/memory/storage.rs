use crate::common::*;
use crate::verify_one_file;

// Only one declared array is live at a time.
test_verify_one_file! {
    #[test] separate_scopes_reuse_storage verus_code! {
        use vstd::prelude::*;
        fn example()
            resources peak(memory) <= 256,
        {
            { let first = [0u32; 64]; }
            { let second = [0u32; 64]; }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] overlapping_scopes_exceed_same_budget verus_code! {
        use vstd::prelude::*;
        fn example()
            resources peak(memory) <= 256,
        {
            let first = [0u32; 64];
            let second = [0u32; 64];
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 512 bytes exceeds budget 256 bytes")
}

test_verify_one_file! {
    #[test] exact_budget_passes verus_code! {
        use vstd::prelude::*;
        fn example()
            resources peak(memory) <= 512,
        {
            let first = [0u32; 64];
            let second = [0u32; 64];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] one_byte_short_fails verus_code! {
        use vstd::prelude::*;
        fn example()
            resources peak(memory) <= 255,
        {
            let first = [0u32; 64];
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 256 bytes exceeds budget 255 bytes")
}

test_verify_one_file! {
    #[test] alternatives_use_maximum verus_code! {
        use vstd::prelude::*;
        fn example(condition: bool)
            resources peak(memory) <= 257,
        {
            if condition {
                let first = [0u32; 64];
            } else {
                let second = [0u32; 32];
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_body_storage_is_reusable verus_code! {
        use vstd::prelude::*;
        fn example(mut condition: bool)
            resources peak(memory) <= 257,
        {
            while condition
                decreases if condition { 1int } else { 0int },
            {
                let scratch = [0u32; 64];
                condition = false;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_data_is_erased verus_code! {
        use vstd::prelude::*;
        fn example()
            resources peak(memory) <= 256,
        {
            let ghost huge = [0u32; 4096usize];
            proof { let other = [0u32; 8192usize]; }
            let scratch = [0u32; 64];
            assert(true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] parameter_storage_is_counted verus_code! {
        use vstd::prelude::*;
        fn example(input: [u32; 64])
            resources peak(memory) <= 255,
        {}
    } => Err(err) => assert_vir_error_msg(err, "peak 256 bytes exceeds budget 255 bytes")
}

test_verify_one_file! {
    #[test] unknown_call_is_rejected verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn unknown() {}
        fn example()
            resources peak(memory) <= 100000,
        { unknown(); }
    } => Err(err) => assert_vir_error_msg(err, "does not support calls")
}

test_verify_one_file! {
    #[test] checked_zero_storage_call verus_code! {
        use vstd::prelude::*;
        fn leaf() resources peak(memory) <= 0 {}
        fn example() resources peak(memory) <= 0 { leaf(); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] explicit_unit_return verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 0 { return; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unsupported_type_is_rejected verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 1000 { let x = 'x'; }
    } => Err(err) => assert_vir_error_msg(err, "does not support this type")
}

test_verify_one_file! {
    #[test] unchecked_body_is_rejected verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn example() resources peak(memory) <= 0 { let x = [0u32; 64]; }
    } => Err(err) => assert_vir_error_msg(err, "does not support this function")
}

test_verify_one_file! {
    #[test] shadowing_does_not_release_old_slot verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 256 {
            let scratch = [0u32; 64];
            let scratch = [0u32; 64];
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 512 bytes exceeds budget 256 bytes")
}

test_verify_one_file! {
    #[test] array_literal_uses_only_its_destination verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 8 { let x = [1u32, 2u32]; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] initializer_copy_is_counted verus_code! {
        use vstd::prelude::*;
        fn example(input: [u32; 64]) resources peak(memory) <= 511 {
            let copy = input;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 512 bytes exceeds budget 511 bytes")
}

test_verify_one_file! {
    #[test] uninitialized_slots_are_charged verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 255 {
            let scratch: [u32; 64];
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 256 bytes exceeds budget 255 bytes")
}

test_verify_one_file! {
    #[test] outer_slot_survives_inner_scope verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 511 {
            let outer = [0u32; 64];
            { let inner = [0u32; 64]; }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 512 bytes exceeds budget 511 bytes")
}

test_verify_one_file! {
    #[test] executable_statement_temporary_is_charged verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 255 { [0u32; 64]; }
    } => Err(err) => assert_vir_error_msg(err, "peak 256 bytes exceeds budget 255 bytes")
}

test_verify_one_file! {
    #[test] executable_statement_temporary_exact_budget verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 256 { [0u32; 64]; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] zero_length_repeat_has_no_storage verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 0 { let empty = [0u32; 0]; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] boolean_parameters_and_local_are_charged verus_code! {
        use vstd::prelude::*;
        fn example(a: bool, b: bool) resources peak(memory) <= 3 {
            let result = a == b;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] boolean_local_underbudget verus_code! {
        use vstd::prelude::*;
        fn example(a: bool, b: bool) resources peak(memory) <= 2 {
            let result = a == b;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 3 bytes exceeds budget 2 bytes")
}

test_verify_one_file! {
    #[test] scalar_comparison verus_code! {
        use vstd::prelude::*;
        fn example(x: u32) requires x <= 10, resources peak(memory) <= 5 {
            let small = x < 8u32;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] short_circuit_boolean_results verus_code! {
        use vstd::prelude::*;
        fn example(a: bool, b: bool) resources peak(memory) <= 3 {
            let conjunction = a && !b;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] functional_proof_still_required verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 0 {
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] memory_proofs_respect_trusted_assumptions verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 0 {
            assume(false);
            let scratch = [0u32; 64];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unreachable_calls_are_still_rejected verus_code! {
        use vstd::prelude::*;
        fn leaf() {}
        fn example() resources peak(memory) <= 1000 {
            if false { leaf(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "does not support calls")
}

test_verify_one_file! {
    #[test] array_helper_call_is_not_array_syntax verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 1000 {
            let scratch: [u32; 64] = vstd::array::array_fill_for_copy_types(0u32);
        }
    } => Err(err) => assert_vir_error_msg(err, "does not support calls")
}

test_verify_one_file! {
    #[test] immediate_break verus_code! {
        use vstd::prelude::*;
        fn example(condition: bool) resources peak(memory) <= 1000 {
            while condition decreases 1int, { break; }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unsupported_reference_targets_are_rejected verus_code! {
        use vstd::prelude::*;
        fn example(x: &char) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "does not support this type")
}

test_verify_one_file! {
    #[test] value_returning_blocks_use_destination verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 8 {
            let x = { let y = 0u32; y };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] erased_functions_cannot_have_resource_contracts verus_code! {
        use vstd::prelude::*;
        proof fn example() resources peak(memory) <= 0 {}
    } => Err(err) => assert_vir_error_msg(err, "does not support this function")
}

test_verify_one_file! {
    #[test] external_functions_cannot_claim_resource_contracts verus_code! {
        use vstd::prelude::*;
        #[verifier::external]
        fn example() resources peak(memory) <= 0 { let scratch = [0u32; 64]; }
    } => Err(err) => assert_vir_error_msg(err, "resource contracts require a verified function body")
}

test_verify_one_file! {
    #[test] duplicate_internal_budgets_are_rejected verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 1000 {
            verus_builtin::memory_budget(0);
        }
    } => Err(err) => assert_vir_error_msg(err, "only one memory clause allowed")
}

test_verify_one_file! {
    #[test] unannotated_code_keeps_existing_behavior verus_code! {
        use vstd::prelude::*;
        fn leaf() {}
        fn example() { let x = 0u64; leaf(); }
    } => Ok(())
}

// The clause keyword remains available as an ordinary function name.
test_verify_one_file! {
    #[test] resources_name_in_logical_clauses verus_code! {
        spec fn resources(n: u32) -> bool { n == 0 }
        fn example(n: u32)
            requires resources(n),
            ensures resources(n),
            resources peak(memory) <= value_size(n),
        {
            assert(resources(n));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] resources_name_in_executable_calls verus_code! {
        fn resources() resources peak(memory) <= 0 {}
        fn example() resources peak(memory) <= peak(resources) {
            resources();
            resources peak(memory) <= 0 {}
        }
    } => Ok(())
}
