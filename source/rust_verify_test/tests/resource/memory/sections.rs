use crate::common::*;
use crate::verify_one_file;

test_verify_one_file! {
    #[test] runtime_section_bound_is_rejected verus_code! {
        fn f(n: u64) resources memory <= mem_size(n) {
            resources memory <= n {}
        }
    } => Err(err) => assert_vir_error_msg(err, "immutable Boolean or native integer input parameters")
}

#[test]
fn nested_workspace_example() {
    verify_one_file(
        "nested_workspace_example",
        include_str!("../../../../../examples/resource/memory/sections.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] section_budget_is_checked_independently verus_code! {
        use vstd::prelude::*;
        fn f() resources memory <= 128 {
            resources memory <= 16 { let scratch = [0u32; 8]; }
        }
    } => Err(err) => assert_vir_error_msg(err, "section memory budget exceeded: peak 32 bytes exceeds budget 16 bytes")
}

test_verify_one_file! {
    #[test] parent_retains_its_own_storage verus_code! {
        use vstd::prelude::*;
        fn f() resources memory <= 16 {
            let original = [0u32; 4];
            resources memory <= mem_size(original) { let copy = original; }
        }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded: peak 32 bytes exceeds budget 16 bytes")
}

test_verify_one_file! {
    #[test] nested_parent_covers_child_slack verus_code! {
        fn f() resources memory <= 128 {
            resources memory <= 64 {
                let own = 0u32;
                resources memory <= 64 {}
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "section memory budget exceeded: peak 68 bytes exceeds budget 64 bytes")
}

test_verify_one_file! {
    #[test] siblings_reuse_declared_allowances verus_code! {
        fn f() resources memory <= 64 {
            resources memory <= 64 {}
            resources memory <= 32 {}
            assert(peak(memory) <= 64);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] section_does_not_reset_parent_history verus_code! {
        fn f() resources memory <= 64 {
            resources memory <= 64 {}
            resources memory <= 0 { assert(peak(memory) <= 0); }
            assert(peak(memory) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 64 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] enclosing_loop_does_not_import_previous_section_history verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) resources memory <= 17 {
            while run decreases if run { 1int } else { 0int }, {
                resources memory <= 16 {
                    assert(peak(memory) <= 0);
                    let scratch = [0u32; 4];
                }
                run = false;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_within_section_retains_previous_iteration_peak verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) resources memory <= 17 {
            resources memory <= 16 {
                while run decreases if run { 1int } else { 0int }, {
                    assert(peak(memory) <= 0);
                    let scratch = [0u32; 4];
                    run = false;
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] calls_use_section_accounting verus_code! {
        use vstd::prelude::*;
        fn helper() resources memory <= 64 {}
        fn f() resources memory <= mem_size([u32; 4]) + mem_peak(helper) {
            let original = [0u32; 4];
            resources memory <= mem_peak(helper) {
                helper();
                assert(peak(memory) <= mem_peak(helper));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] callee_slack_is_not_hidden_by_section verus_code! {
        fn helper() resources memory <= 64 {}
        fn f() resources memory <= 64 { resources memory <= 32 { helper(); } }
    } => Err(err) => assert_vir_error_msg(err, "section memory budget exceeded: peak 64 bytes exceeds budget 32 bytes")
}

test_verify_one_file! {
    #[test] sections_cannot_hide_recursive_calls verus_code! {
        fn f() resources memory <= 0 { resources memory <= 0 { f(); } }
    } => Err(err) => assert_vir_error_msg(err, "recursive")
}

test_verify_one_file! {
    #[test] existing_data_can_be_changed_without_local_storage verus_code! {
        fn f() resources memory <= mem_size(u32) {
            let mut value = 0u32;
            resources memory <= 0 { value = 5; }
            assert(value == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] sections_preserve_functional_checks verus_code! {
        fn f() resources memory <= 0 {
            resources memory <= 0 { assert(false); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] section_requires_function_contract verus_code! {
        fn f() { resources memory <= 0 {} }
    } => Err(err) => assert_vir_error_msg(err, "memory sections require a function-level memory contract")
}

test_verify_one_file! {
    #[test] proof_section_is_rejected verus_code! {
        fn f() resources memory <= 0 { proof { resources memory <= 0 {} } }
    } => Err(err) => assert_vir_error_msg(err, "memory sections require a verified exec function body")
}

test_verify_one_file! {
    #[test] external_body_section_is_rejected verus_code! {
        #[verifier::external_body]
        fn f() { resources memory <= 0 {} }
    } => Err(err) => assert_vir_error_msg(err, "memory sections require a verified exec function body")
}

test_verify_one_file! {
    #[test] section_formula_overflow_is_rejected verus_code! {
        fn f() resources memory <= 0 { resources memory <= 18446744073709551615u64 + 1 {} }
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] parent_plus_section_overflow_is_rejected verus_code! {
        fn f(x: u32) resources memory <= 18446744073709551615u64 {
            resources memory <= 18446744073709551615u64 {}
        }
    } => Err(err) => assert_vir_error_msg(err, "storage totals exceeding u64")
}

test_verify_one_file! {
    #[test] raw_marker_cannot_reset_accounting_mid_block verus_code! {
        fn f() resources memory <= 4 {
            let local = 0u32;
            verus_builtin::resource_section(0);
        }
    } => Err(err) => assert_vir_error_msg(err, "section metadata outside the start of a block")
}

test_verify_one_file! {
    #[test] section_budget_uses_bindings_at_entry verus_code! {
        use vstd::prelude::*;
        fn f() resources memory <= 20 {
            let value = [0u32; 4];
            resources memory <= mem_size(value) {
                let value = 0u32;
                assert(peak(memory) <= mem_size(value));
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 20 bytes")
}

test_verify_one_file! {
    #[test] sections_in_branches_use_maximum verus_code! {
        fn f(condition: bool) resources memory <= 65 {
            if condition { resources memory <= 64 {} } else { resources memory <= 32 {} }
            assert(peak(memory) <= 65);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ordinary_blocks_keep_section_history verus_code! {
        use vstd::prelude::*;
        fn f() resources memory <= 16 {
            resources memory <= 16 {
                { let scratch = [0u32; 4]; }
                assert(peak(memory) <= 0);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}
