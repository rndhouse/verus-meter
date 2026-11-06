#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] value_type_and_arithmetic verus_code! {
        use vstd::prelude::*;
        fn f(x: u32, flag: bool)
            resources peakmem <= sizeof(x) + sizeof(flag)
                + sizeof([u32; 4]),
        {
            let scratch = [0u32; 4];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] noncopy_parameter_is_not_consumed verus_code! {
        struct Data { x: u32 }
        fn f(data: Data) resources peakmem <= 2 * sizeof(data) {
            let moved = data;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reference_query_excludes_backing_data verus_code! {
        struct Large { data: [u32; 100] }
        fn f(buffer: &mut Large) resources peakmem <= sizeof(buffer) {}
        fn g(buffer: &[u32]) resources peakmem <= sizeof(buffer) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] type_query_uses_unpadded_struct_layout verus_code! {
        struct Data { x: u32, flag: bool }
        fn f(x: Data) resources peakmem <= sizeof(Data) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] qualified_forward_function_reference verus_code! {
        fn caller() resources peakmem <= peakmem(helpers::leaf) {
            helpers::leaf();
        }
        mod helpers {
            pub fn leaf() resources peakmem <= 10 {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] alias_uses_resolved_function_identity verus_code! {
        use helpers::leaf as renamed;
        fn caller() resources peakmem <= peakmem(renamed) { renamed(); }
        mod helpers {
            pub fn leaf() resources peakmem <= 10 {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] declared_slack_not_measured_peak verus_code! {
        fn caller() resources peakmem <= peakmem(leaf) {
            let local = 0u32;
            leaf();
        }
        fn leaf() resources peakmem <= 10 {}
    } => Err(err) => assert_vir_error_msg(err, "peak 14 bytes exceeds budget 10 bytes")
}

test_verify_one_file! {
    #[test] parameter_shadows_function verus_code! {
        fn leaf() resources peakmem <= 100 {}
        fn f(leaf: u32) resources peakmem <= sizeof(leaf) {
            let x = 0u32;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 8 bytes exceeds budget 4 bytes")
}

test_verify_one_file! {
    #[test] referenced_body_is_still_checked verus_code! {
        fn f() resources peakmem <= peakmem(leaf) {}
        fn leaf() resources peakmem <= 0 { let x = 0u32; }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] missing_contract_is_rejected verus_code! {
        fn leaf() {}
        fn f() resources peakmem <= peakmem(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "peakmem requires a declared resource contract")
}

test_verify_one_file! {
    #[test] self_budget_cycle verus_code! {
        fn f() resources peakmem <= peakmem(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular peakmem reference")
}

test_verify_one_file! {
    #[test] mutual_budget_cycle_without_calls verus_code! {
        fn f() resources peakmem <= peakmem(g) {}
        fn g() resources peakmem <= peakmem(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular peakmem reference")
}

test_verify_one_file! {
    #[test] zero_does_not_hide_budget_cycle verus_code! {
        fn f() resources peakmem <= 0 * peakmem(f) {}
    } => Err(err) => assert_vir_error_msg(err, "circular peakmem reference")
}

test_verify_one_file! {
    #[test] addition_overflow verus_code! {
        fn f() resources peakmem <= 18446744073709551615u64 + sizeof(u32) {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] multiplication_overflow verus_code! {
        fn f() resources peakmem <= 18446744073709551615u64 * 2 {}
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] maximum_literal_and_zero_product verus_code! {
        fn f() resources peakmem <= 18446744073709551615u64 + 0 {}
        fn g() resources peakmem <= 0 * peakmem(f) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] generic_function_query_rejected verus_code! {
        fn generic<T>() {}
        fn f() resources peakmem <= peakmem(generic::<u32>) {}
    } => Err(err) => assert_vir_error_msg(err, "generic function memory budgets are not supported")
}

test_verify_one_file! {
    #[test] external_body_budget_rejected verus_code! {
        #[verifier::external_body]
        fn leaf() resources peakmem <= 8 {}
        fn f() resources peakmem <= peakmem(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "expected a safe, nongeneric exec function returning unit")
}

test_verify_one_file! {
    #[test] unsupported_type_query_rejected verus_code! {
        fn f() resources peakmem <= sizeof(u64) {}
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] budget_builtin_outside_header_rejected verus_code! {
        proof fn f() {
            let n = verus_builtin::resource_sizeof_type::<u32>();
        }
    } => Err(err) => assert_vir_error_msg(err, "sizeof and peakmem are only allowed inside a resources clause")
}

test_verify_one_file! {
    #[test] qualified_type_and_alias verus_code! {
        mod data {
            pub struct Buffer { pub values: [u32; 4], pub ready: bool }
            pub type Alias = Buffer;
        }
        fn f(buffer: data::Buffer) resources peakmem <= sizeof(data::Alias) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] parameter_name_takes_precedence_over_type verus_code! {
        struct Buffer { values: [u32; 4] }
        fn f(Buffer: bool) resources peakmem <= sizeof(Buffer) { let extra = 0u32; }
        fn g(Buffer: bool, data: crate::Buffer)
            resources peakmem <= sizeof(Buffer) + sizeof(crate::Buffer),
        {}
    } => Err(err) => assert_vir_error_msg(err, "peak 5 bytes exceeds budget 1 bytes")
}

test_verify_one_file! {
    #[test] compound_type_queries verus_code! {
        fn f(array: &mut [u32; 4], slice: &[u32], owned: [u32; 3])
            resources peakmem <= sizeof(&mut [u32; 4]) + sizeof(&[u32])
                + sizeof([u32; 3]) + sizeof(()),
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] compound_query_still_requires_a_supported_type verus_code! {
        fn f() resources peakmem <= sizeof([[u32; 2]; 3]) {}
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] multiplication_precedes_addition verus_code! {
        fn f(data: [u32; 5]) resources peakmem <= 10 + 2 * sizeof(u32) {}
    } => Err(err) => assert_vir_error_msg(err, "peak 20 bytes exceeds budget 18 bytes")
}

test_verify_one_file! {
    #[test] parentheses_override_precedence verus_code! {
        fn f(data: [u32; 12]) resources peakmem <= (10 + 2) * sizeof(u32) {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] peakmem_cannot_query_value_storage verus_code! {
        fn leaf() resources peakmem <= 100 {}
        fn f(leaf: u32) resources peakmem <= peakmem(leaf) {}
    } => Err(err) => assert_vir_error_msg(err, "peakmem expects a function with a declared resource contract")
}

test_verify_one_file! {
    #[test] sizeof_cannot_query_function_budget verus_code! {
        fn leaf() resources peakmem <= 100 {}
        fn f() resources peakmem <= sizeof(leaf) {}
    } => Err(err) => assert_rust_error_msg(err, "constant provided when a type was expected")
}

test_verify_one_file! {
    #[test] peakmem_builtin_outside_header_rejected verus_code! {
        fn leaf() resources peakmem <= 0 {}
        proof fn f() {
            let n = verus_builtin::resource_peakmem(&leaf);
        }
    } => Err(err) => assert_vir_error_msg(err, "sizeof and peakmem are only allowed inside a resources clause")
}
