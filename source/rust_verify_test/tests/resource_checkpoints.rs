#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] current_function_calls_remain_logical_assertions verus_code! {
        spec fn current(x: u32) -> u32 { x }
        fn f(x: u32) peakmem <= sizeof(x) {
            assert(current(x) == x);
            assert(current(peakmem) <= sizeof(x));
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
        && span.text.iter().any(|line| line.text.contains("assert(current(peakmem)"))));
    assert_vir_error_msg(err, "peakmem assertion failed: peak 32 bytes exceeds bound 16 bytes");
}

test_verify_one_file! {
    #[test] later_storage_does_not_affect_an_earlier_checkpoint verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 260 {
            let first = 0u32;
            assert(current(peakmem) <= sizeof(first));
            let later = [0u32; 64];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] completed_scope_remains_in_peak verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 16 {
            { let scratch = [0u32; 4]; }
            assert(current(peakmem) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] completed_call_remains_in_peak verus_code! {
        use vstd::prelude::*;
        fn helper() peakmem <= 64 {}
        fn f() peakmem <= peakmem(helper) {
            helper();
            assert(current(peakmem) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 64 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_queries_declared_function_bound verus_code! {
        use vstd::prelude::*;
        fn helper() peakmem <= 64 {}
        fn f() peakmem <= peakmem(helper) {
            helper();
            assert(current(peakmem) <= peakmem(helper));
            assert(current(peakmem) <= peakmem(f));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] sibling_branches_have_separate_histories verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) peakmem <= 257 {
            if condition {
                let large = [0u32; 64];
                assert(current(peakmem) <= sizeof(condition) + sizeof(large));
            } else {
                let small = 0u32;
                assert(current(peakmem) <= sizeof(condition) + sizeof(small));
            }
            assert(current(peakmem) <= 257);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] joined_branches_retain_the_larger_peak verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) peakmem <= 257 {
            if condition { let large = [0u32; 64]; }
            else { let small = 0u32; }
            assert(current(peakmem) <= 5);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 257 bytes exceeds bound 5 bytes")
}

test_verify_one_file! {
    #[test] previous_loop_iteration_counts_at_top_of_body verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) peakmem <= 17 {
            while run
                decreases if run { 1int } else { 0int },
            {
                assert(current(peakmem) <= sizeof(run));
                let scratch = [0u32; 4];
                run = false;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds bound 1 bytes")
}

test_verify_one_file! {
    #[test] loop_peak_is_reused_and_not_reset verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) peakmem <= 17 {
            assert(current(peakmem) <= sizeof(run));
            while run
                decreases if run { 1int } else { 0int },
            {
                assert(current(peakmem) <= sizeof(run) + sizeof([u32; 4]));
                let scratch = [0u32; 4];
                run = false;
            }
            assert(current(peakmem) <= 17);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] outer_loop_history_reaches_nested_checkpoint verus_code! {
        use vstd::prelude::*;
        fn f(mut outer: bool, mut inner: bool) peakmem <= 34 {
            while outer decreases if outer { 1int } else { 0int }, {
                while inner decreases if inner { 1int } else { 0int }, {
                    assert(current(peakmem) <= 2);
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
        fn f() { assert(current(peakmem) <= 0); }
    } => Err(err) => assert_vir_error_msg(err, "peakmem checkpoints require a function-level peakmem contract")
}

test_verify_one_file! {
    #[test] proof_only_checkpoint_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 0 { proof { assert(current(peakmem) <= 0); } }
    } => Err(err) => assert_vir_error_msg(err, "peakmem checkpoints require a verified exec function body")
}

test_verify_one_file! {
    #[test] checkpoint_does_not_prove_logical_claims verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 0 {
            assert(current(peakmem) <= 0);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] checkpoint_does_not_replace_function_contract verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 0 {
            let x = 0u32;
            assert(current(peakmem) <= sizeof(x));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] checkpoints_cannot_reset_history verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 16 {
            { let a = [0u32; 4]; }
            assert(current(peakmem) <= 16);
            assert(current(peakmem) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] local_size_query_does_not_move_data verus_code! {
        use vstd::prelude::*;
        struct Data { value: u32 }
        fn f() peakmem <= 8 {
            let data = Data { value: 5 };
            assert(current(peakmem) <= sizeof(data));
            let moved = data;
            assert(current(peakmem) <= 2 * sizeof(moved));
            assert(moved.value == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_size_query_after_move_uses_only_type verus_code! {
        use vstd::prelude::*;
        struct Data { value: u32 }
        fn f() peakmem <= 8 {
            let data = Data { value: 5 };
            let moved = data;
            assert(current(peakmem) <= sizeof(data) + sizeof(moved));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_type_shadowing_ends_at_scope_exit verus_code! {
        use vstd::prelude::*;
        struct Buffer { value: u32 }
        fn f() peakmem <= 16 {
            { let Buffer = [0u32; 4]; assert(current(peakmem) <= sizeof(Buffer)); }
            assert(current(peakmem) <= sizeof(Buffer));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 4 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_arithmetic_overflow_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 0 { assert(current(peakmem) <= 18446744073709551615u64 + sizeof(u32)); }
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] checkpoint_rejects_unsupported_types verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 0 { assert(current(peakmem) <= sizeof(u64)); }
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] branch_checkpoint_keeps_the_common_prefix verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) peakmem <= 17 {
            { let scratch = [0u32; 4]; }
            if condition {} else { assert(current(peakmem) <= sizeof(condition)); }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds bound 1 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_rejects_missing_callee_contract verus_code! {
        fn helper() {}
        fn f() peakmem <= 0 { assert(current(peakmem) <= 0 * peakmem(helper)); }
    } => Err(err) => assert_vir_error_msg(err, "peakmem requires a declared resource contract")
}

test_verify_one_file! {
    #[test] external_body_checkpoint_is_rejected verus_code! {
        #[verifier::external_body]
        fn f() { assert(current(peakmem) <= 0); }
    } => Err(err) => assert_vir_error_msg(err, "peakmem checkpoints require a verified exec function body")
}

test_verify_one_file! {
    #[test] uninitialized_local_size_query_uses_only_type verus_code! {
        use vstd::prelude::*;
        fn f() peakmem <= 16 {
            let array: [u32; 4];
            assert(current(peakmem) <= sizeof(array));
            array = [0u32; 4];
        }
    } => Ok(())
}
