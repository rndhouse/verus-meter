use crate::common::*;
use crate::verify_one_file;

test_verify_one_file! {
    #[test] runtime_checkpoint_bound_is_rejected verus_code! {
        fn f(n: u64) resources peak(memory) <= owned_size(n) {
            assert(peak(memory) <= n);
        }
    } => Err(err) => assert_vir_error_msg(err, "immutable Boolean or native integer input parameters")
}

test_verify_one_file! {
    #[test] impl_parameters_in_checkpoints_and_sections verus_code! {
        struct Worker {}
        impl Worker {
            fn associated(n: u32) resources peak(memory) <= 2 * owned_size(n) {
                assert(peak(memory) <= owned_size(n));
                resources peak(memory) <= owned_size(n) {
                    let copy = n;
                    assert(peak(memory) <= owned_size(copy));
                }
                assert(peak(memory) <= 2 * owned_size(n));
            }
            fn method(&self, n: u32) resources peak(memory) <= ref_size(&Worker) + owned_size(n) {
                assert(peak(memory) <= ref_size(&Worker) + owned_size(n));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] impl_parameter_checkpoint_still_enforces_bound verus_code! {
        struct Worker {}
        impl Worker {
            fn work(n: u8) resources peak(memory) <= 5 {
                let extra = 0u32;
                assert(peak(memory) <= owned_size(n));
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 5 bytes exceeds bound 1 bytes")
}

test_verify_one_file! {
    #[test] impl_resource_bindings_are_scoped verus_code! {
        use vstd::prelude::*;
        type Buffer = [u8; 16];
        fn outer(Buffer: u32) resources peak(memory) <= owned_size(Buffer) {
            struct Worker {}
            impl Worker {
                fn with_parameter(Buffer: u32) resources peak(memory) <= owned_size(Buffer) {
                    assert(peak(memory) <= owned_size(Buffer));
                }
                fn without_parameter() resources peak(memory) <= owned_size(Buffer) {
                    let data = [0u8; 16];
                    assert(peak(memory) <= owned_size(Buffer));
                }
            }
            assert(peak(memory) <= owned_size(Buffer));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] current_function_calls_remain_logical_assertions verus_code! {
        spec fn current(x: u32) -> u32 { x }
        fn f(x: u32) resources peak(memory) <= owned_size(x) {
            assert(current(x) == x);
            assert(peak(memory) <= owned_size(x));
        }
    } => Ok(())
}

#[test]
fn checkpoint_example() {
    verify_one_file(
        "checkpoint_example",
        include_str!("../../../../../examples/resource/memory/contracts/checkpoints.rs").into(),
        &[],
    )
    .unwrap();
}

#[test]
fn failing_checkpoint_points_to_assertion() {
    let err = verify_one_file(
        "failing_checkpoint_points_to_assertion",
        include_str!("../../../../../examples/resource/memory/expected-failures/checkpoint.rs")
            .into(),
        &[],
    )
    .unwrap_err();
    assert!(err.errors[0].spans.iter().any(|span| span.is_primary
        && span.text.iter().any(|line| line.text.contains("assert(peak(memory)"))));
    assert_vir_error_msg(
        err,
        "peak(memory) assertion failed: peak 32 bytes exceeds bound 16 bytes",
    );
}

test_verify_one_file! {
    #[test] later_storage_does_not_affect_an_earlier_checkpoint verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 260 {
            let first = 0u32;
            assert(peak(memory) <= owned_size(first));
            let later = [0u32; 64];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] completed_scope_remains_in_peak verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 16 {
            { let scratch = [0u32; 4]; }
            assert(peak(memory) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] completed_call_remains_in_peak verus_code! {
        use vstd::prelude::*;
        fn helper() resources peak(memory) <= 64 {}
        fn f() resources peak(memory) <= peak(helper) {
            helper();
            assert(peak(memory) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 64 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_queries_declared_function_bound verus_code! {
        use vstd::prelude::*;
        fn helper() resources peak(memory) <= 64 {}
        fn f() resources peak(memory) <= peak(helper) {
            helper();
            assert(peak(memory) <= peak(helper));
            assert(peak(memory) <= peak(f));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] sibling_branches_have_separate_histories verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) resources peak(memory) <= 257 {
            if condition {
                let large = [0u32; 64];
                assert(peak(memory) <= owned_size(condition) + owned_size(large));
            } else {
                let small = 0u32;
                assert(peak(memory) <= owned_size(condition) + owned_size(small));
            }
            assert(peak(memory) <= 257);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] joined_branches_retain_the_larger_peak verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) resources peak(memory) <= 257 {
            if condition { let large = [0u32; 64]; }
            else { let small = 0u32; }
            assert(peak(memory) <= 5);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 257 bytes exceeds bound 5 bytes")
}

test_verify_one_file! {
    #[test] previous_loop_iteration_counts_at_top_of_body verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) resources peak(memory) <= 17 {
            while run
                decreases if run { 1int } else { 0int },
            {
                assert(peak(memory) <= owned_size(run));
                let scratch = [0u32; 4];
                run = false;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds bound 1 bytes")
}

test_verify_one_file! {
    #[test] loop_peak_is_reused_and_not_reset verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) resources peak(memory) <= 17 {
            assert(peak(memory) <= owned_size(run));
            while run
                decreases if run { 1int } else { 0int },
            {
                assert(peak(memory) <= owned_size(run) + owned_size([u32; 4]));
                let scratch = [0u32; 4];
                run = false;
            }
            assert(peak(memory) <= 17);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] outer_loop_history_reaches_nested_checkpoint verus_code! {
        use vstd::prelude::*;
        fn f(mut outer: bool, mut inner: bool) resources peak(memory) <= 34 {
            while outer decreases if outer { 1int } else { 0int }, {
                while inner decreases if inner { 1int } else { 0int }, {
                    assert(peak(memory) <= 2);
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
        fn f() { assert(peak(memory) <= 0); }
    } => Err(err) => assert_vir_error_msg(err, "memory checkpoints require a function-level memory contract")
}

test_verify_one_file! {
    #[test] proof_only_checkpoint_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 0 { proof { assert(peak(memory) <= 0); } }
    } => Err(err) => assert_vir_error_msg(err, "memory checkpoints require a verified exec function body")
}

test_verify_one_file! {
    #[test] checkpoint_does_not_prove_logical_claims verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 0 {
            assert(peak(memory) <= 0);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] checkpoint_does_not_replace_function_contract verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 0 {
            let x = 0u32;
            assert(peak(memory) <= owned_size(x));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 4 bytes exceeds budget 0 bytes")
}

test_verify_one_file! {
    #[test] checkpoints_cannot_reset_history verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 16 {
            { let a = [0u32; 4]; }
            assert(peak(memory) <= 16);
            assert(peak(memory) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] local_size_query_does_not_move_data verus_code! {
        use vstd::prelude::*;
        struct Data { value: u32 }
        fn f() resources peak(memory) <= 8 {
            let data = Data { value: 5 };
            assert(peak(memory) <= owned_size(data));
            let moved = data;
            assert(peak(memory) <= 2 * owned_size(moved));
            assert(moved.value == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_size_query_after_move_uses_only_type verus_code! {
        use vstd::prelude::*;
        struct Data { value: u32 }
        fn f() resources peak(memory) <= 8 {
            let data = Data { value: 5 };
            let moved = data;
            assert(peak(memory) <= owned_size(data) + owned_size(moved));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] local_type_shadowing_ends_at_scope_exit verus_code! {
        use vstd::prelude::*;
        struct Buffer { value: u32 }
        fn f() resources peak(memory) <= 16 {
            { let Buffer = [0u32; 4]; assert(peak(memory) <= owned_size(Buffer)); }
            assert(peak(memory) <= owned_size(Buffer));
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 4 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_arithmetic_overflow_is_rejected verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 0 { assert(peak(memory) <= 18446744073709551615u64 + owned_size(u32)); }
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] checkpoint_rejects_unsupported_types verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 0 { assert(peak(memory) <= owned_size(char)); }
    } => Err(err) => assert_vir_error_msg(err, "resource model")
}

test_verify_one_file! {
    #[test] branch_checkpoint_keeps_the_common_prefix verus_code! {
        use vstd::prelude::*;
        fn f(condition: bool) resources peak(memory) <= 17 {
            { let scratch = [0u32; 4]; }
            if condition {} else { assert(peak(memory) <= owned_size(condition)); }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 17 bytes exceeds bound 1 bytes")
}

test_verify_one_file! {
    #[test] checkpoint_rejects_missing_callee_contract verus_code! {
        fn helper() {}
        fn f() resources peak(memory) <= 0 { assert(peak(memory) <= 0 * peak(helper)); }
    } => Err(err) => assert_vir_error_msg(err, "peak requires a declared resource contract")
}

test_verify_one_file! {
    #[test] external_body_checkpoint_is_rejected verus_code! {
        #[verifier::external_body]
        fn f() { assert(peak(memory) <= 0); }
    } => Err(err) => assert_vir_error_msg(err, "memory checkpoints require a verified exec function body")
}

test_verify_one_file! {
    #[test] uninitialized_local_size_query_uses_only_type verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 16 {
            let array: [u32; 4];
            assert(peak(memory) <= owned_size(array));
            array = [0u32; 4];
        }
    } => Ok(())
}

// Releasing storage lowers the live query while preserving the historical peak.
test_verify_one_file! {
    #[test] current_memory_after_scope_exit verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 16 {
            assert(current(memory) <= 0);
            { let scratch = [0u32; 4]; assert(current(memory) <= 16); }
            assert(current(memory) <= 0);
            assert(peak(memory) <= 16);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] current_memory_rejects_live_storage verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 16 {
            let scratch = [0u32; 4];
            assert(current(memory) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "current(memory) assertion failed: live 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] current_memory_sections_exclude_parent_storage verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 32 {
            let outer = [0u32; 4];
            resources peak(memory) <= 16 {
                assert(current(memory) <= 0);
                { let inner = [0u32; 4]; assert(current(memory) <= 16); }
                assert(current(memory) <= 0);
                assert(peak(memory) <= 16);
            }
            assert(current(memory) <= 16);
            assert(peak(memory) <= 32);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] current_memory_does_not_import_previous_loop_peaks verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) resources peak(memory) <= 17 {
            while run
                decreases if run { 1int } else { 0int },
            {
                assert(current(memory) <= 1);
                { let scratch = [0u32; 4]; }
                assert(current(memory) <= 1);
                run = false;
            }
            assert(current(memory) <= 1);
            assert(peak(memory) <= 17);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] current_memory_includes_symbolic_heap_storage verus_code! {
        use vstd::prelude::*;
        fn f(n: usize)
            requires n <= 4,
            resources peak(memory) <= 32 + 4 * n,
        {
            { let values = Vec::<u32>::with_capacity(n);
              assert(current(memory) <= 48); }
            assert(current(memory) <= 8);
            assert(peak(memory) <= 48);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] current_memory_rejects_unbudgeted_heap_storage verus_code! {
        use vstd::prelude::*;
        fn f(n: usize)
            requires n == 4,
            resources peak(memory) <= 48,
        {
            let values = Vec::<u32>::with_capacity(n);
            assert(current(memory) <= 32); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] current_memory_requires_checked_function verus_code! {
        fn f() { assert(current(memory) <= 0); }
    } => Err(err) => assert_vir_error_msg(err, "memory checkpoints require a function-level memory contract")
}
