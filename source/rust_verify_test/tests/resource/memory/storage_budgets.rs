use crate::common::*;
use crate::verify_one_file;

test_verify_one_file! {
    #[test] former_helper_budget_query_has_no_builtin_alias verus_code! {
        fn helper() resources peak(memory) <= 0 {}
        fn caller() resources peak(memory) <= mem_peak(helper) {}
    } => Err(err) => assert_rust_error_msg(err, "cannot find function `mem_peak`")
}

test_verify_one_file! {
    #[test] ordinary_peak_names_remain_logical_outside_resource_queries verus_code! {
        spec fn peak(value: u32) -> u32 { value }
        fn f() resources peak(memory) <= owned_size(u32) {
            assert(peak(7) == 7);
            let peak = 0u32;
            assert(peak <= 0);
            assert(peak(memory) <= owned_size(u32));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] value_type_and_arithmetic verus_code! {
        use vstd::prelude::*;
        fn f(x: u32, flag: bool)
            resources peak(memory) <= owned_size(x) + owned_size(flag)
                + owned_size([u32; 4]),
        {
            let scratch = [0u32; 4];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] noncopy_parameter_is_not_consumed verus_code! {
        struct Data { x: u32 }
        fn f(data: Data) resources peak(memory) <= 2 * owned_size(data) {
            let moved = data;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reference_query_excludes_backing_data verus_code! {
        struct Large { data: [u32; 100] }
        fn f(buffer: &mut Large) resources peak(memory) <= ref_size(buffer) {}
        fn g(buffer: &[u32]) resources peak(memory) <= ref_size(buffer) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] type_query_uses_unpadded_struct_layout verus_code! {
        struct Data { x: u32, flag: bool }
        fn f(x: Data) resources peak(memory) <= owned_size(Data) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] qualified_forward_function_reference verus_code! {
        fn caller() resources peak(memory) <= peak(helpers::leaf) {
            helpers::leaf();
        }
        mod helpers {
            pub fn leaf() resources peak(memory) <= 10 {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] alias_uses_resolved_function_identity verus_code! {
        use helpers::leaf as renamed;
        fn caller() resources peak(memory) <= peak(renamed) { renamed(); }
        mod helpers {
            pub fn leaf() resources peak(memory) <= 10 {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] declared_slack_not_measured_peak verus_code! {
        fn caller() resources peak(memory) <= peak(leaf) {
            let local = 0u32;
            leaf();
        }
        fn leaf() resources peak(memory) <= 10 {}
    } => Err(err) => assert_vir_error_msg(err, "peak 14 bytes exceeds budget 10 bytes")
}

test_verify_one_file! {
    #[test] parameter_shadows_function verus_code! {
        fn leaf() resources peak(memory) <= 100 {}
        fn f(leaf: u32) resources peak(memory) <= owned_size(leaf) {
            let x = 0u32;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 8 bytes exceeds budget 4 bytes")
}

test_verify_one_file! {
    #[test] referenced_body_is_still_checked verus_code! {
        fn f() resources peak(memory) <= peak(leaf) {}
        fn leaf() resources peak(memory) <= 0 { let x = 0u32; }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] missing_contract_is_rejected verus_code! {
        fn leaf() {}
        fn f() resources peak(memory) <= peak(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "peak requires a declared resource contract")
}

test_verify_one_file! {
    #[test] self_budget_cycle verus_code! {
        fn f() resources peak(memory) <= peak(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular peak reference")
}

test_verify_one_file! {
    #[test] mutual_budget_cycle_without_calls verus_code! {
        fn f() resources peak(memory) <= peak(g) {}
        fn g() resources peak(memory) <= peak(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular peak reference")
}

test_verify_one_file! {
    #[test] zero_does_not_hide_budget_cycle verus_code! {
        fn f() resources peak(memory) <= 0 * peak(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular peak reference")
}

test_verify_one_file! {
    #[test] addition_overflow verus_code! {
        fn f() resources peak(memory) <= 18446744073709551615u64 + owned_size(u32) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] multiplication_overflow verus_code! {
        fn f() resources peak(memory) <= 18446744073709551615u64 * 2 {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] maximum_literal_and_zero_product verus_code! {
        fn f() resources peak(memory) <= 18446744073709551615u64 + 0 {}
        fn g() resources peak(memory) <= 0 * peak(f) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] generic_function_query_rejected verus_code! {
        fn generic<T>() {}
        fn f() resources peak(memory) <= peak(generic::<u32>) {}
    } => Err(err) => assert_vir_error_msg(err, "generic function memory budgets are not supported")
}

test_verify_one_file! {
    #[test] external_body_budget_rejected verus_code! {
        #[verifier::external_body]
        fn leaf() resources peak(memory) <= 8 {}
        fn f() resources peak(memory) <= peak(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "expected a safe, nongeneric exec function")
}

test_verify_one_file! {
    #[test] unsupported_type_query_rejected verus_code! {
        fn f() resources peak(memory) <= owned_size(char) {}
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] peak_query_outside_header_rejected verus_code! {
        fn helper() resources peak(memory) <= 0 {}
        proof fn f() {
            let n = verus_builtin::resource_peak(&helper);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak is only allowed inside a memory clause or checkpoint")
}

test_verify_one_file! {
    #[test] qualified_type_and_alias verus_code! {
        mod data {
            pub struct Buffer { pub values: [u32; 4], pub ready: bool }
            pub type Alias = Buffer;
        }
        fn f(buffer: data::Buffer) resources peak(memory) <= owned_size(data::Alias) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] parameter_name_takes_precedence_over_type verus_code! {
        struct Buffer { values: [u32; 4] }
        fn f(Buffer: bool) resources peak(memory) <= owned_size(Buffer) { let extra = 0u32; }
        fn g(Buffer: bool, data: crate::Buffer)
            resources peak(memory) <= owned_size(Buffer) + owned_size(crate::Buffer),
        {}
    } => Err(err) => assert_vir_error_msg(err, "peak 5 bytes exceeds budget 1 bytes")
}

test_verify_one_file! {
    #[test] compound_type_queries verus_code! {
        fn f(array: &mut [u32; 4], slice: &[u32], owned: [u32; 3])
            resources peak(memory) <= ref_size(&mut [u32; 4]) + ref_size(&[u32])
                + owned_size([u32; 3]) + owned_size(()),
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] compound_query_still_requires_a_supported_type verus_code! {
        fn f() resources peak(memory) <= owned_size([[u32; 2]; 3]) {}
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] multiplication_precedes_addition verus_code! {
        fn f(data: [u32; 5]) resources peak(memory) <= 10 + 2 * owned_size(u32) {}
    } => Err(err) => assert_vir_error_msg(err, "peak 20 bytes exceeds budget 18 bytes")
}

test_verify_one_file! {
    #[test] parentheses_override_precedence verus_code! {
        fn f(data: [u32; 12]) resources peak(memory) <= (10 + 2) * owned_size(u32) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] peak_cannot_query_value_storage verus_code! {
        fn leaf() resources peak(memory) <= 100 {}
        fn f(leaf: u32) resources peak(memory) <= peak(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "peak expects a function with a declared resource contract")
}

test_verify_one_file! {
    #[test] owned_size_cannot_query_function_budget verus_code! {
        fn leaf() resources peak(memory) <= 100 {}
        fn f() resources peak(memory) <= owned_size(leaf) {}
    } => Err(err) => assert_rust_error_msg(err, "constant provided when a type was expected")
}

test_verify_one_file! {
    #[test] peak_builtin_outside_header_rejected verus_code! {
        fn leaf() resources peak(memory) <= 0 {}
        proof fn f() {
            let n = verus_builtin::resource_peak(&leaf);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak is only allowed inside a memory clause or checkpoint")
}

test_verify_one_file! {
    #[test] peak_function_name_in_other_clauses verus_code! {
        spec fn peak(x: u32) -> bool { x == 0 }
        fn f(x: u32)
            requires peak(x),
            ensures peak(x),
            resources peak(memory) <= owned_size(x),
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] model_size_in_proof verus_code! {
        proof fn f() {
            let n = owned_size(u32);
            assert(n == 4);
        }
    } => Ok(())
}
