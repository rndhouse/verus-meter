#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] runtime_checkpoint_bound_is_rejected verus_code! {
        fn f(n: u64) mem_peak <= mem_size(n) {
            assert(current(mem_peak) <= n);
        }
    } => Err(err) => assert_vir_error_msg(err, "immutable Boolean or native integer input parameters")
}

test_verify_one_file! {
    #[test] current_function_calls_remain_logical_assertions verus_code! {
        spec fn current(x: u32) -> u32 { x }
        fn f(x: u32) mem_peak <= mem_size(x) {
            assert(current(x) == x);
            assert(current(mem_peak) <= mem_size(x));
        }
    } => Ok(())
}

#[test]
fn checkpoint_example() {
    verify_one_file(
        "checkpoint_example",
        include_str!("../../../examples/resource/memory/checkpoints.rs").into(),
        &[],
    )
    .unwrap();
}

#[test]
fn failing_checkpoint_points_to_assertion() {
    let err = verify_one_file(
        "failing_checkpoint_points_to_assertion",
        include_str!("../../../examples/resource/memory/expected-failures/checkpoint.rs").into(),
        &[],
    )
    .unwrap_err();
    assert!(err.errors[0].spans.iter().any(|span| span.is_primary
        && span.text.iter().any(|line| line.text.contains("assert(current(mem_peak)"))));
    assert_vir_error_msg(err, "mem_peak assertion failed: peak 32 bytes exceeds bound 16 bytes");
}

test_verify_one_file! {
    #[test] later_storage_does_not_affect_an_earlier_checkpoint verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 260 {
            let first = 0u32;
            assert(current(mem_peak) <= mem_size(first));
            let later = [0u32; 64];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] completed_scope_remains_in_peak verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 16 {
            { let scratch = [0u32; 4]; }
            assert(current(mem_peak) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] completed_call_remains_in_peak verus_code! {
        use vstd::prelude::*;
        fn helper() mem_peak <= 64 {}
        fn f() mem_peak <= mem_peak(helper) {
            helper();
            assert(current(mem_peak) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 64 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_queries_declared_function_bound verus_code! {
        use vstd::prelude::*;
        fn helper() mem_peak <= 64 {}
        fn f() mem_peak <= mem_peak(helper) {
            helper();
            assert(current(mem_peak) <= mem_peak(helper));
            assert(current(mem_peak) <= mem_peak(f));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] sibling_branches_have_separate_histories verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) mem_peak <= 257 {
            if condition {
                let large = [0u32; 64];
                assert(current(mem_peak) <= mem_size(condition) + mem_size(large));
            } else {
                let small = 0u32;
                assert(current(mem_peak) <= mem_size(condition) + mem_size(small));
            }
            assert(current(mem_peak) <= 257);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] joined_branches_retain_the_larger_peak verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) mem_peak <= 257 {
            if condition { let large = [0u32; 64]; }
            else { let small = 0u32; }
            assert(current(mem_peak) <= 5);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 257 bytes exceeds bound 5 bytes")
}

test_verify_one_file! {
    #[test] previous_loop_iteration_counts_at_top_of_body verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) mem_peak <= 17 {
            while run
                decreases if run { 1int } else { 0int },
            {
                assert(current(mem_peak) <= mem_size(run));
                let scratch = [0u32; 4];
                run = false;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds bound 1 bytes")
}

test_verify_one_file! {
    #[test] loop_peak_is_reused_and_not_reset verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) mem_peak <= 17 {
            assert(current(mem_peak) <= mem_size(run));
            while run
                decreases if run { 1int } else { 0int },
            {
                assert(current(mem_peak) <= mem_size(run) + mem_size([u32; 4]));
                let scratch = [0u32; 4];
                run = false;
            }
            assert(current(mem_peak) <= 17);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] outer_loop_history_reaches_nested_checkpoint verus_code! {
        use vstd::prelude::*;
        fn f(mut outer: bool, mut inner: bool) mem_peak <= 34 {
            while outer decreases if outer { 1int } else { 0int }, {
                while inner decreases if inner { 1int } else { 0int }, {
                    assert(current(mem_peak) <= 2);
                    inner = false;
                }
                let scratch = [0u32; 8];
                outer = false;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 34 bytes exceeds bound 2 bytes")
}

test_verify_one_file! {
    #[test] missing_contract_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() { assert(current(mem_peak) <= 0); }
    } => Err(err) => assert_vir_error_msg(err, "mem_peak checkpoints require a function-level mem_peak contract")
}

test_verify_one_file! {
    #[test] proof_only_checkpoint_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 0 { proof { assert(current(mem_peak) <= 0); } }
    } => Err(err) => assert_vir_error_msg(err, "mem_peak checkpoints require a verified exec function body")
}

test_verify_one_file! {
    #[test] checkpoint_does_not_prove_logical_claims verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 0 {
            assert(current(mem_peak) <= 0);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] checkpoint_does_not_replace_function_contract verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 0 {
            let x = 0u32;
            assert(current(mem_peak) <= mem_size(x));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] checkpoints_cannot_reset_history verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 16 {
            { let a = [0u32; 4]; }
            assert(current(mem_peak) <= 16);
            assert(current(mem_peak) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] local_size_query_does_not_move_data verus_code! {
        use vstd::prelude::*;
        struct Data { value: u32 }
        fn f() mem_peak <= 8 {
            let data = Data { value: 5 };
            assert(current(mem_peak) <= mem_size(data));
            let moved = data;
            assert(current(mem_peak) <= 2 * mem_size(moved));
            assert(moved.value == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_size_query_after_move_uses_only_type verus_code! {
        use vstd::prelude::*;
        struct Data { value: u32 }
        fn f() mem_peak <= 8 {
            let data = Data { value: 5 };
            let moved = data;
            assert(current(mem_peak) <= mem_size(data) + mem_size(moved));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_type_shadowing_ends_at_scope_exit verus_code! {
        use vstd::prelude::*;
        struct Buffer { value: u32 }
        fn f() mem_peak <= 16 {
            { let Buffer = [0u32; 4]; assert(current(mem_peak) <= mem_size(Buffer)); }
            assert(current(mem_peak) <= mem_size(Buffer));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 4 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_arithmetic_overflow_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 0 { assert(current(mem_peak) <= 18446744073709551615u64 + mem_size(u32)); }
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] checkpoint_rejects_unsupported_types verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 0 { assert(current(mem_peak) <= mem_size(char)); }
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] branch_checkpoint_keeps_the_common_prefix verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) mem_peak <= 17 {
            { let scratch = [0u32; 4]; }
            if condition {} else { assert(current(mem_peak) <= mem_size(condition)); }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds bound 1 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_rejects_missing_callee_contract verus_code! {
        fn helper() {}
        fn f() mem_peak <= 0 { assert(current(mem_peak) <= 0 * mem_peak(helper)); }
    } => Err(err) => assert_vir_error_msg(err, "mem_peak requires a declared resource contract")
}

test_verify_one_file! {
    #[test] external_body_checkpoint_is_rejected verus_code! {
        #[verifier::external_body]
        fn f() { assert(current(mem_peak) <= 0); }
    } => Err(err) => assert_vir_error_msg(err, "mem_peak checkpoints require a verified exec function body")
}

test_verify_one_file! {
    #[test] uninitialized_local_size_query_uses_only_type verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 16 {
            let array: [u32; 4];
            assert(current(mem_peak) <= mem_size(array));
            array = [0u32; 4];
        }
    } => Ok(())
}
