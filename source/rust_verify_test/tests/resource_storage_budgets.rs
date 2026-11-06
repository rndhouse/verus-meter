#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] value_type_and_arithmetic verus_code! {
        use vstd::prelude::*;
        fn f(x: u32, flag: bool)
            resources peak_memory_bytes <= memory_budget(x) + memory_budget(flag)
                + memory_budget::<[u32; 4]>(),
        {
            let scratch = [0u32; 4];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] noncopy_parameter_is_not_consumed verus_code! {
        struct Data { x: u32 }
        fn f(data: Data) resources peak_memory_bytes <= 2 * memory_budget(data) {
            let moved = data;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reference_query_excludes_backing_data verus_code! {
        struct Large { data: [u32; 100] }
        fn f(buffer: &mut Large) resources peak_memory_bytes <= memory_budget(buffer) {}
        fn g(buffer: &[u32]) resources peak_memory_bytes <= memory_budget(buffer) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] type_query_uses_unpadded_struct_layout verus_code! {
        struct Data { x: u32, flag: bool }
        fn f(x: Data) resources peak_memory_bytes <= memory_budget::<Data>() {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] qualified_forward_function_reference verus_code! {
        fn caller() resources peak_memory_bytes <= memory_budget(helpers::leaf) {
            helpers::leaf();
        }
        mod helpers {
            pub fn leaf() resources peak_memory_bytes <= 10 {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] alias_uses_resolved_function_identity verus_code! {
        use helpers::leaf as renamed;
        fn caller() resources peak_memory_bytes <= memory_budget(renamed) { renamed(); }
        mod helpers {
            pub fn leaf() resources peak_memory_bytes <= 10 {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] declared_slack_not_measured_peak verus_code! {
        fn caller() resources peak_memory_bytes <= memory_budget(leaf) {
            let local = 0u32;
            leaf();
        }
        fn leaf() resources peak_memory_bytes <= 10 {}
    } => Err(err) => assert_vir_error_msg(err, "peak 14 bytes exceeds budget 10 bytes")
}

test_verify_one_file! {
    #[test] parameter_shadows_function verus_code! {
        fn leaf() resources peak_memory_bytes <= 100 {}
        fn f(leaf: u32) resources peak_memory_bytes <= memory_budget(leaf) {
            let x = 0u32;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 8 bytes exceeds budget 4 bytes")
}

test_verify_one_file! {
    #[test] referenced_body_is_still_checked verus_code! {
        fn f() resources peak_memory_bytes <= memory_budget(leaf) {}
        fn leaf() resources peak_memory_bytes <= 0 { let x = 0u32; }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] missing_contract_is_rejected verus_code! {
        fn leaf() {}
        fn f() resources peak_memory_bytes <= memory_budget(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "memory_budget requires a declared resource contract")
}

test_verify_one_file! {
    #[test] self_budget_cycle verus_code! {
        fn f() resources peak_memory_bytes <= memory_budget(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular memory_budget reference")
}

test_verify_one_file! {
    #[test] mutual_budget_cycle_without_calls verus_code! {
        fn f() resources peak_memory_bytes <= memory_budget(g) {}
        fn g() resources peak_memory_bytes <= memory_budget(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular memory_budget reference")
}

test_verify_one_file! {
    #[test] zero_does_not_hide_budget_cycle verus_code! {
        fn f() resources peak_memory_bytes <= 0 * memory_budget(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular memory_budget reference")
}

test_verify_one_file! {
    #[test] addition_overflow verus_code! {
        fn f() resources peak_memory_bytes <= 18446744073709551615u64 + memory_budget::<u32>() {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] multiplication_overflow verus_code! {
        fn f() resources peak_memory_bytes <= 18446744073709551615u64 * 2 {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] maximum_literal_and_zero_product verus_code! {
        fn f() resources peak_memory_bytes <= 18446744073709551615u64 + 0 {}
        fn g() resources peak_memory_bytes <= 0 * memory_budget(f) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] generic_function_query_rejected verus_code! {
        fn generic<T>() {}
        fn f() resources peak_memory_bytes <= memory_budget(generic::<u32>) {}
    } => Err(err) => assert_vir_error_msg(err, "generic function memory budgets are not supported")
}

test_verify_one_file! {
    #[test] external_body_budget_rejected verus_code! {
        #[verifier::external_body]
        fn leaf() resources peak_memory_bytes <= 8 {}
        fn f() resources peak_memory_bytes <= memory_budget(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "expected a safe, nongeneric exec function returning unit")
}

test_verify_one_file! {
    #[test] unsupported_type_query_rejected verus_code! {
        fn f() resources peak_memory_bytes <= memory_budget::<u64>() {}
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] budget_builtin_outside_header_rejected verus_code! {
        proof fn f() {
            let n = verus_builtin::memory_budget_type::<u32>();
        }
    } => Err(err) => assert_vir_error_msg(err, "memory_budget is only allowed inside a resources clause")
}
