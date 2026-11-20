use crate::common::*;
use crate::verify_one_file;

test_verify_one_file! {
    #[test] parent_must_cover_even_an_empty_symbolic_section verus_code! {
        fn f(n: u64) resources peak(memory) <= value_size(n) {
            resources peak(memory) <= n {}
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}

test_verify_one_file! {
    #[test] slice_length_section_composes_with_result_size_and_callee_peak verus_code! {
        use vstd::prelude::*;
        fn checksum(byte: u8) -> u16 resources peak(memory) <= value_size(byte) + value_size(u16) {
            byte as u16
        }
        fn run(packed: &[u8], limit: u32)
            requires packed.len() <= limit,
            resources peak(memory) <= ref_size(packed) + value_size(limit)
                + limit * return_size(checksum) + peak(checksum),
        {
            resources peak(memory) <= packed.len() * return_size(checksum) + peak(checksum) {
                if packed.len() > 0 {
                    let result = checksum(0);
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] empty_input_section_has_zero_allowance verus_code! {
        use vstd::prelude::*;
        fn run(packed: &[u8]) requires packed.len() == 0, resources peak(memory) <= 64 {
            resources peak(memory) <= packed.len() { let scratch = 0u8; }
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}

test_verify_one_file! {
    #[test] section_snapshots_the_entry_length_before_the_vector_changes verus_code! {
        use vstd::prelude::*;
        fn run() resources peak(memory) <= 128 {
            let mut bytes = Vec::<u8>::with_capacity(1);
            resources peak(memory) <= bytes.len() {
                bytes.push(1);
                let scratch = 0u8;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}

test_verify_one_file! {
    #[test] vector_length_survives_a_shrink_inside_a_nested_section verus_code! {
        use vstd::prelude::*;
        fn run() resources peak(memory) <= value_size(Vec<u8>) + 1 + value_size(Option<u8>) {
            let mut bytes = Vec::<u8>::with_capacity(1);
            bytes.push(1);
            resources peak(memory) <= value_size(Option<u8>) {
                resources peak(memory) <= bytes.len() * value_size(Option<u8>) {
                    let removed = bytes.pop();
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] user_defined_len_cannot_supply_a_section_length verus_code! {
        struct Packet { size: u8 }
        impl Packet { fn len(&self) -> usize { self.size as usize } }
        fn run(packet: Packet) resources peak(memory) <= 64 {
            resources peak(memory) <= packet.len() {}
        }
    } => Err(err) => assert_vir_error_msg(err, "section length requires a named executable slice or vector")
}

test_verify_one_file! {
    #[test] bound_local_is_read_at_each_section_entry verus_code! {
        use vstd::prelude::*;
        fn run() resources peak(memory) <= 64 {
            let mut count = 0u8;
            while count < 2 invariant count <= 2, decreases 2 - count, {
                resources peak(memory) <= count {
                    count += 1;
                    if count > 1 { let scratch = 0u8; }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] overflowing_section_allowance_rejects_even_without_allocations verus_code! {
        fn run(n: u64) resources peak(memory) <= 18446744073709551615u64 {
            resources peak(memory) <= n * 2 {}
        }
    } => Err(err) => assert_any_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

#[test]
fn nested_workspace_example() {
    verify_one_file(
        "nested_workspace_example",
        include_str!("../../../../../examples/resource/memory/contracts/sections.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] section_budget_is_checked_independently verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 128 {
            resources peak(memory) <= 16 { let scratch = [0u32; 8]; }
        }
    } => Err(err) => assert_vir_error_msg(err, "section memory budget exceeded: peak 32 bytes exceeds budget 16 bytes")
}

test_verify_one_file! {
    #[test] parent_retains_its_own_storage verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 16 {
            let original = [0u32; 4];
            resources peak(memory) <= value_size(original) { let copy = original; }
        }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded: peak 32 bytes exceeds budget 16 bytes")
}

test_verify_one_file! {
    #[test] nested_parent_covers_child_slack verus_code! {
        fn f() resources peak(memory) <= 128 {
            resources peak(memory) <= 64 {
                let own = 0u32;
                resources peak(memory) <= 64 {}
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "section memory budget exceeded: peak 68 bytes exceeds budget 64 bytes")
}

test_verify_one_file! {
    #[test] siblings_reuse_declared_allowances verus_code! {
        fn f() resources peak(memory) <= 64 {
            resources peak(memory) <= 64 {}
            resources peak(memory) <= 32 {}
            assert(peak(memory) <= 64);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] section_does_not_reset_parent_history verus_code! {
        fn f() resources peak(memory) <= 64 {
            resources peak(memory) <= 64 {}
            resources peak(memory) <= 0 { assert(peak(memory) <= 0); }
            assert(peak(memory) <= 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 64 bytes exceeds bound 0 bytes")
}

test_verify_one_file! {
    #[test] enclosing_loop_does_not_import_previous_section_history verus_code! {
        use vstd::prelude::*;
        fn f(mut run: bool) resources peak(memory) <= 17 {
            while run decreases if run { 1int } else { 0int }, {
                resources peak(memory) <= 16 {
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
        fn f(mut run: bool) resources peak(memory) <= 17 {
            resources peak(memory) <= 16 {
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
        fn helper() resources peak(memory) <= 64 {}
        fn f() resources peak(memory) <= value_size([u32; 4]) + peak(helper) {
            let original = [0u32; 4];
            resources peak(memory) <= peak(helper) {
                helper();
                assert(peak(memory) <= peak(helper));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] callee_slack_is_not_hidden_by_section verus_code! {
        fn helper() resources peak(memory) <= 64 {}
        fn f() resources peak(memory) <= 64 { resources peak(memory) <= 32 { helper(); } }
    } => Err(err) => assert_vir_error_msg(err, "section memory budget exceeded: peak 64 bytes exceeds budget 32 bytes")
}

test_verify_one_file! {
    #[test] sections_cannot_hide_recursive_calls verus_code! {
        fn f() resources peak(memory) <= 0 { resources peak(memory) <= 0 { f(); } }
    } => Err(err) => assert_vir_error_msg(err, "recursive memory contracts")
}

test_verify_one_file! {
    #[test] existing_data_can_be_changed_without_local_storage verus_code! {
        fn f() resources peak(memory) <= value_size(u32) {
            let mut value = 0u32;
            resources peak(memory) <= 0 { value = 5; }
            assert(value == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] sections_preserve_functional_checks verus_code! {
        fn f() resources peak(memory) <= 0 {
            resources peak(memory) <= 0 { assert(false); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] section_requires_function_contract verus_code! {
        fn f() { resources peak(memory) <= 0 {} }
    } => Err(err) => assert_vir_error_msg(err, "memory sections require a function-level memory contract")
}

test_verify_one_file! {
    #[test] proof_section_is_rejected verus_code! {
        fn f() resources peak(memory) <= 0 { proof { resources peak(memory) <= 0 {} } }
    } => Err(err) => assert_vir_error_msg(err, "memory sections require a verified exec function body")
}

test_verify_one_file! {
    #[test] external_body_section_is_rejected verus_code! {
        #[verifier::external_body]
        fn f() { resources peak(memory) <= 0 {} }
    } => Err(err) => assert_vir_error_msg(err, "memory sections require a verified exec function body")
}

test_verify_one_file! {
    #[test] section_formula_overflow_is_rejected verus_code! {
        fn f() resources peak(memory) <= 0 { resources peak(memory) <= 18446744073709551615u64 + 1 {} }
    } => Err(err) => assert_vir_error_msg(err, "memory budget arithmetic exceeds u64")
}

test_verify_one_file! {
    #[test] parent_plus_section_overflow_is_rejected verus_code! {
        fn f(x: u32) resources peak(memory) <= 18446744073709551615u64 {
            resources peak(memory) <= 18446744073709551615u64 {}
        }
    } => Err(err) => assert_vir_error_msg(err, "storage totals exceeding u64")
}

test_verify_one_file! {
    #[test] raw_marker_cannot_reset_accounting_mid_block verus_code! {
        fn f() resources peak(memory) <= 4 {
            let local = 0u32;
            verus_builtin::resource_section(0);
        }
    } => Err(err) => assert_vir_error_msg(err, "section metadata outside the start of a block")
}

test_verify_one_file! {
    #[test] section_budget_uses_bindings_at_entry verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 20 {
            let value = [0u32; 4];
            resources peak(memory) <= value_size(value) {
                let value = 0u32;
                assert(peak(memory) <= value_size(value));
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 32 bytes exceeds budget 20 bytes")
}

test_verify_one_file! {
    #[test] sections_in_branches_use_maximum verus_code! {
        fn f(condition: bool) resources peak(memory) <= 65 {
            if condition { resources peak(memory) <= 64 {} } else { resources peak(memory) <= 32 {} }
            assert(peak(memory) <= 65);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ordinary_blocks_keep_section_history verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 16 {
            resources peak(memory) <= 16 {
                { let scratch = [0u32; 4]; }
                assert(peak(memory) <= 0);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds bound 0 bytes")
}
