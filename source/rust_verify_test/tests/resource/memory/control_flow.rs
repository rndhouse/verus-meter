//! Exit edges preserve lexical cleanup, returned ownership, and peak history.

use crate::common::*;
use crate::verify_one_file;

// A return transfers its result while releasing the other local allocations.
test_verify_one_file! {
    #[test] explicit_return_preserves_owning_result verus_code! {
        use vstd::prelude::*;
        fn build() -> Box<[u8; 16]>
            resources peak(memory) <= 64,
        {
            let scratch = Box::new([0u8; 32]);
            let result = Box::new([0u8; 16]);
            return result;
        }
        fn caller() resources peak(memory) <= 64 {
            let result = build();
            assert(current(memory) <= 24);
            drop(result);
            assert(current(memory) <= 0);
        }
    } => Ok(())
}

// A false condition can still mutate a collection before a single-visit body.
// Reject a caller bound that omits the child allocated by that condition.
#[test]
fn condition_effects_survive_a_skipped_single_visit() {
    let code = verus_code! {
        use vstd::prelude::*;
        fn append_and_stop(buffers: &mut Vec<Box<[u8; 16]>>) -> (again: bool)
            requires old(buffers).len() < 4,
            ensures !again, final(buffers).len() == old(buffers).len() + 1,
            resources peak(memory) <= 128,
        {
            let child = Box::new([0u8; 16]);
            buffers.push(child);
            false
        }
        #[verifier::exec_allows_no_decreases_clause]
        fn build() -> Vec<Box<[u8; 16]>> resources peak(memory) <= 256 {
            let mut buffers = Vec::with_capacity(4);
            while append_and_stop(&mut buffers) { break; }
            buffers
        }
        fn caller() resources peak(memory) <= 256 {
            let buffers = build();
            assert(current(memory) <= BOUND);
        }
    };
    verify_one_file("condition_charge", code.replace("BOUND", "72"), &[]).unwrap();
    let err =
        verify_one_file("condition_charge_short", code.replace("BOUND", "71"), &[]).unwrap_err();
    assert_vir_error_msg(err, "memory budget");
}

// The same collection can return at different points with different forests.
test_verify_one_file! {
    #[test] early_returns_keep_complete_collection_forests verus_code! {
        use vstd::prelude::*;
        fn build(short: bool) -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == if short { 1int } else { 2int },
            resources peak(memory) <= 128,
        {
            let mut buffers = Vec::<Box<[u8; 16]>>::with_capacity(2);
            let first = Box::new([0u8; 16]);
            buffers.push(first);
            if short { return buffers; }
            let second = Box::new([0u8; 16]);
            buffers.push(second);
            buffers
        }
        fn caller() resources peak(memory) <= 160 {
            let mut buffers = build(false);
            let last = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// Single visits retain their actual entry facts through nested value breaks.
test_verify_one_file! {
    #[test] value_breaks_release_nested_scopes verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn build() -> Box<[u8; 16]>
            resources peak(memory) <= 64,
        {
            'outer: loop {
                let scratch = Box::new([0u8; 32]);
                loop {
                    let result = Box::new([0u8; 16]);
                    break 'outer result;
                }
            }
        }
        fn caller() resources peak(memory) <= 64 {
            let result = build();
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// Continue cleans its iteration's locals; break cleans them on the exit path.
test_verify_one_file! {
    #[test] break_and_continue_cleanup verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn example() resources peak(memory) <= 76 {
            let mut i = 0u32;
            while i < 4 {
                let scratch = Box::new([0u8; 64]);
                i += 1;
                if i == 2 { continue; }
                if i == 3 { break; }
            }
            assert(current(memory) <= 4);
        }
    } => Ok(())
}

// Discarding a scalar loop result ends its temporary inline lifetime too.
test_verify_one_file! {
    #[test] discarded_loop_values_release_result_storage verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn example() resources peak(memory) <= 4 {
            loop { break 7u32; };
            assert(current(memory) <= 0);
        }
        #[verifier::exec_allows_no_decreases_clause]
        fn specified(input: u8) -> (result: u8)
            requires input < 10,
            ensures result == input + 1,
            resources peak(memory) <= 2,
        {
            loop
                invariant_except_break input < 10,
                ensures input < 10,
            {
                break input + 1;
            }
        }
    } => Ok(())
}

// Repeated value exits need an explicit result projection beyond a counted
// ownership recurrence; a byte budget cannot provide that projection.
test_verify_one_file! {
    #[test] repeated_value_breaks_require_a_result_transformation verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn example(count: u16) -> Box<[u8; 16]> resources peak(memory) <= 100000 {
            let result = Box::new([0u8; 16]);
            let mut i = 0u16;
            loop {
                if i >= count { break result; }
                i += 1;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "value-producing breaks in reusable loops")
}

// The allocation before an exit still contributes to the function's peak.
test_verify_one_file! {
    #[test] exited_paths_keep_peak_checks verus_code! {
        use vstd::prelude::*;
        fn example(stop: bool) resources peak(memory) <= 72 {
            if stop {
                let scratch = Box::new([0u8; 64]);
                return;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 73 bytes exceeds budget 72 bytes")
}

// A completed section's allowance and its escaping result have distinct lives.
test_verify_one_file! {
    #[test] returning_from_a_section_preserves_result_and_cleanup verus_code! {
        use vstd::prelude::*;
        fn build() -> Box<[u8; 16]>
            resources peak(memory) <= 88,
        {
            let outer = Box::new([0u8; 32]);
            resources peak(memory) <= 48 {
                let scratch = [0u8; 16];
                let result = Box::new([0u8; 16]);
                return result;
            }
        }
        fn caller() resources peak(memory) <= 88 {
            let result = build();
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// Breaking out of a section releases its work before continuing after the loop.
test_verify_one_file! {
    #[test] section_break_restores_parent_accounting verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn example() resources peak(memory) <= 104 {
            let outer = Box::new([0u8; 32]);
            loop {
                resources peak(memory) <= 64 {
                    let scratch = Box::new([0u8; 48]);
                    break;
                }
            }
            assert(current(memory) <= 40);
        }
        #[verifier::exec_allows_no_decreases_clause]
        fn moved_owner() resources peak(memory) <= 24 {
            let outer = Box::new([0u8; 16]);
            let retained = loop {
                resources peak(memory) <= 0 { break outer; }
            };
            drop(retained);
            assert(current(memory) <= 0);
        }
    } => Ok(())
}

// Result evaluation cannot spend an enclosing section's release credits.
test_verify_one_file! {
    #[test] protected_owner_drops_in_exit_results_remain_unsupported verus_code! {
        use vstd::prelude::*;
        fn build() -> Box<[u8; 16]> resources peak(memory) <= 128 {
            let outer = Box::new([0u8; 16]);
            resources peak(memory) <= 32 {
                return { drop(outer); Box::new([0u8; 16]) };
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "moving or dropping an enclosing heap owner")
}

// The same progress and forest model covers bounded breaks and skipped visits.
test_verify_one_file! {
    #[test] counted_exit_forests_reach_callers verus_code! {
        use vstd::prelude::*;
        spec fn budget(n: u16) -> nat { 128 + (n as nat) * 24 }
        #[verifier::exec_allows_no_decreases_clause]
        fn head_stop(n: u16, stop: u16) -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == if stop < n { stop as int } else { n as int },
            resources peak(memory) <= budget(n),
        {
            let mut buffers = Vec::<Box<[u8; 16]>>::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n {
                if i >= stop { break; }
                let buffer = Box::new([0u8; 16]);
                buffers.push(buffer);
                i += 1;
            }
            buffers
        }
        #[verifier::exec_allows_no_decreases_clause]
        fn skip(n: u16) -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == if n > 2 { n - 2 } else { 0int },
            resources peak(memory) <= budget(n),
        {
            let mut buffers = Vec::<Box<[u8; 16]>>::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n {
                i += 1;
                if i <= 2 { continue; }
                let buffer = Box::new([0u8; 16]);
                buffers.push(buffer);
            }
            buffers
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn until_limit(n: u16) -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == n,
            resources peak(memory) <= budget(n),
        {
            let mut buffers = Vec::<Box<[u8; 16]>>::with_capacity(n as usize);
            let mut i = 0u16;
            loop {
                if i >= n { break; }
                let buffer = Box::new([0u8; 16]);
                buffers.push(buffer);
                i += 1;
            }
            buffers
        }
        fn caller() resources peak(memory) <= 512 {
            {
                let mut buffers = head_stop(4, 2);
                let child = buffers.pop().unwrap();
                drop(buffers);
                assert(current(memory) <= 24);
            }
            {
                let mut buffers = until_limit(2);
                let child = buffers.pop().unwrap();
                drop(buffers);
                assert(current(memory) <= 24);
            }
            {
                let mut buffers = skip(4);
                let child = buffers.pop().unwrap();
                drop(buffers);
                assert(current(memory) <= 24);
            }
            {
                let buffers = until_limit(0);
                assert(current(memory) <= 24);
            }
        }
    } => Ok(())
}

// A labelled continue unwinds both loops' temporary allocation scopes.
test_verify_one_file! {
    #[test] labelled_continue_releases_intervening_scopes verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn example() resources peak(memory) <= 100 {
            let mut i = 0u32;
            'outer: while i < 3 {
                let outer = Box::new([0u8; 64]);
                i += 1;
                loop {
                    let inner = Box::new([0u8; 16]);
                    continue 'outer;
                }
            }
            assert(current(memory) <= 4);
        }
    } => Ok(())
}

// An exited path contributes to the function peak but cannot precede a later
// checkpoint on the continuing path or in a subsequent completed iteration.
test_verify_one_file! {
    #[test] checkpoints_exclude_paths_that_already_exited verus_code! {
        use vstd::prelude::*;
        fn returning(stop: bool) resources peak(memory) <= 65 {
            if stop {
                let scratch = [0u8; 64];
                return;
            }
            assert(peak(memory) <= 1);
        }
        #[verifier::exec_allows_no_decreases_clause]
        fn breaking(stop: bool) resources peak(memory) <= 66 {
            let mut i = 0u8;
            while i < 2 {
                assert(peak(memory) <= 2);
                if stop {
                    let scratch = [0u8; 64];
                    break;
                }
                i += 1;
            }
        }
    } => Ok(())
}

// Pattern bindings and match temporaries also unwind before a return.
test_verify_one_file! {
    #[test] returns_from_option_arms_cleanup_bindings verus_code! {
        use vstd::prelude::*;
        fn select(input: Option<u8>) -> u8 resources peak(memory) <= 28 {
            match input {
                Some(value) => {
                    let scratch = Box::new([0u8; 16]);
                    return value;
                }
                None => { return 0; }
            }
        }
        fn caller() resources peak(memory) <= 32 {
            let result = select(Some(1));
            assert(current(memory) <= 1);
        }
    } => Ok(())
}

// Partial visits with an unknown stopping count have no precise forest map.
test_verify_one_file! {
    #[test] partial_iteration_exit_summaries_remain_unsupported verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn build(n: u16, stop: bool) -> Vec<Box<[u8; 16]>>
            resources peak(memory) <= 10000000,
        {
            let mut buffers = Vec::<Box<[u8; 16]>>::with_capacity(n as usize);
            let mut i = 0u16;
            while i < n {
                let buffer = Box::new([0u8; 16]);
                buffers.push(buffer);
                if stop { break; }
                i += 1;
            }
            buffers
        }
    } => Err(err) => assert_vir_error_msg(err, "no precise helper summary can be inferred")
}

// Distinct vector states cannot silently share one returned byte envelope.
test_verify_one_file! {
    #[test] differing_returned_allocation_states_remain_unsupported verus_code! {
        use vstd::prelude::*;
        fn build(short: bool) -> Vec<u8> resources peak(memory) <= 100000 {
            if short { return Vec::with_capacity(1); }
            Vec::with_capacity(2)
        }
    } => Err(err) => assert_vir_error_msg(err, "path-dependent returned allocation identities")
}

// Operand exits need short-circuit evaluation support rather than charging the
// enclosing expression as though it had completed normally.
test_verify_one_file! {
    #[test] operand_level_exits_are_explicitly_rejected verus_code! {
        use vstd::prelude::*;
        fn example() resources peak(memory) <= 100000 {
            let value = 1u32 + { return; 0u32 };
        }
    } => Err(err) => assert_vir_error_msg(err, "control-flow exits inside operands or call arguments")
}

// A head exit after complete visits needs the completed input-region identity,
// not the original forest observed on its representative first visit.
test_verify_one_file! {
    #[test] unconditional_head_exits_preserve_input_regions verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn discard_last(input: Vec<Vec<u32>>, count: u16) -> (remaining: Vec<Vec<u32>>)
            requires input.len() >= count,
            ensures remaining.len() == input.len() - count,
            resources peak(memory) <= 128,
        {
            let mut source = input;
            let mut i = 0u16;
            loop
                invariant
                    i <= count,
                    input.len() >= count,
                    source.len() == input.len() - i,
            {
                if i >= count { break; }
                let child = source.pop().unwrap();
                drop(child);
                i += 1;
            }
            source
        }
        fn caller() resources peak(memory) <= 256 {
            let mut source = Vec::<Vec<u32>>::with_capacity(2);
            let first = Vec::<u32>::with_capacity(4);
            source.push(first);
            let second = Vec::<u32>::with_capacity(8);
            source.push(second);
            let remaining = discard_last(source, 1);
            assert(current(memory) <= 88);
            drop(remaining);
            assert(current(memory) <= 0);
        }
    } => Ok(())
}

// The final head break can follow earlier completed iterations' high water.
test_verify_one_file! {
    #[test] unconditional_exit_checkpoints_include_previous_iterations verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn example() resources peak(memory) <= 68 {
            let mut i = 0u32;
            loop {
                if i >= 2 { break; }
                let scratch = [0u8; 64];
                i += 1;
            }
            assert(peak(memory) <= 4);
        }
    } => Err(err) => assert_vir_error_msg(err, "peak(memory) assertion failed")
}

// A conditional single visit must not export an unconditional append to a
// caller's repeated helper program.
test_verify_one_file! {
    #[test] conditional_single_visits_keep_guarded_borrowed_effects verus_code! {
        use vstd::prelude::*;
        #[verifier::exec_allows_no_decreases_clause]
        fn append_once(buffers: &mut Vec<Box<[u8; 16]>>, enabled: bool)
            requires old(buffers).len() < 4,
            ensures final(buffers).len() == old(buffers).len() + if enabled { 1int } else { 0int },
            resources peak(memory) <= 128,
        {
            while enabled {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
                break;
            }
        }
        // Returning from an initializer must still guard its preceding writes.
        fn append_then_return(buffers: &mut Vec<Box<[u8; 16]>>, enabled: bool)
            requires old(buffers).len() < 4,
            ensures final(buffers).len() == old(buffers).len() + if enabled { 1int } else { 0int },
            resources peak(memory) <= 128,
        {
            if !enabled { return; }
            let unreachable: () = {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
                return;
            };
        }
        #[verifier::exec_allows_no_decreases_clause]
        fn build() -> Vec<Box<[u8; 16]>> resources peak(memory) <= 256 {
            let mut buffers = Vec::with_capacity(4);
            let mut i = 0u8;
            while i < 4 {
                append_once(&mut buffers, false);
                append_then_return(&mut buffers, false);
                i += 1;
            }
            buffers
        }
        fn caller() resources peak(memory) <= 256 {
            let buffers = build();
            assert(current(memory) <= 56);
        }
    } => Ok(())
}
