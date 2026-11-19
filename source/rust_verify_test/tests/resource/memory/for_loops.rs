//! Finite iterator state shares checked heap-loop effects and lexical cleanup.

use crate::common::*;
use crate::verify_one_file;

// Iterator and yielded-value lifetimes end before the following checkpoint.
#[test]
fn scalar_range_state_has_its_own_exact_peak() {
    super::support::exact_peak(
        "range_state",
        r#"
        fn example(count: u16) resources peak(memory) <= BUDGET {
            for index in 0u16..count {
                let scratch = Box::new([0u8; 16]);
            }
            assert(current(memory) <= 2);
        }
    "#,
        34,
    );
}

// An adapter's source stays live while its count argument calls a heap helper.
#[test]
fn iterator_arguments_retain_their_allocation_overlap() {
    super::support::exact_peak(
        "iterator_arguments",
        r#"
        fn limit() -> (count: usize)
            ensures count == 2,
            resources peak(memory) <= 80,
        {
            let scratch = Box::new([0u8; 64]);
            2
        }
        fn example() resources peak(memory) <= BUDGET {
            for index in (0u16..4).take(limit()) { }
        }
    "#,
        96,
    );
}

// Field-initializer order affects the physical order of borrowed heap updates.
#[test]
fn range_constructors_preserve_field_evaluation_order() {
    let code = verus_code! {
        use vstd::prelude::*;
        fn append(buffers: &mut Vec<Vec<u32>>, capacity: u16, bound: u16) -> (result: u16)
            requires old(buffers).len() < 2, capacity <= 4,
            ensures final(buffers).len() == old(buffers).len() + 1, result == bound,
            resources peak(memory) <= 256,
        {
            let child = Vec::<u32>::with_capacity(capacity as usize);
            buffers.push(child);
            bound
        }
        fn build() -> (buffers: Vec<Vec<u32>>)
            ensures buffers.len() == 2,
            resources peak(memory) <= 1024,
        {
            let mut buffers = Vec::with_capacity(2);
            for _ in (core::ops::Range {
                end: append(&mut buffers, 1, 1),
                start: append(&mut buffers, 4, 0),
            }) { }
            buffers
        }
        fn caller() resources peak(memory) <= 1024 {
            let mut buffers = build();
            let last = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= RETAINED_BOUND);
        }
    };
    verify_one_file("range_field_order", code.replace("RETAINED_BOUND", "40"), &[]).unwrap();
    let err = verify_one_file("range_field_order_short", code.replace("RETAINED_BOUND", "39"), &[])
        .unwrap_err();
    assert_vir_error_msg(err, "conditional memory budget exceeded");
}

// Checked factories preserve scalar iterator observations across calls. A local
// method named take must keep its own memory contract rather than become an adapter.
test_verify_one_file! {
    #[test] iterator_factories_preserve_scalar_inputs_and_method_identity verus_code! {
        use vstd::prelude::*;
        struct Factory {}
        impl Factory {
            fn take(self, count: u16) -> (indices: core::ops::Range<u16>)
                ensures indices.start == 0, indices.end == count,
                resources peak(memory) <= 64,
            {
                let scratch = Box::new([0u8; 32]);
                0u16..count
            }
        }
        spec fn budget(count: u16) -> nat { 256 + (count as nat) * 24 }
        fn build(count: u16) -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == count,
            resources peak(memory) <= budget(count),
        {
            let factory = Factory {};
            let mut buffers = Vec::with_capacity(count as usize);
            for _ in factory.take(count) {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
            }
            buffers
        }
        fn caller() resources peak(memory) <= 512 {
            let mut buffers = build(2);
            let child = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// Iterator counts remain symbolic through adapters and containing iterations.
test_verify_one_file! {
    #[test] parametric_adapters_and_nested_visits_keep_exact_counts verus_code! {
        use vstd::prelude::*;
        spec fn budget(count: u16) -> nat { 256 + (count as nat) * 24 }
        fn select(count: u16) -> Vec<Box<[u8; 16]>>
            resources peak(memory) <= budget(count),
        {
            let mut buffers = Vec::with_capacity(count as usize);
            for _ in (0u16..count).skip(1).take(2).rev() {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
            }
            buffers
        }
        fn nested() -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == 6,
            resources peak(memory) <= 512,
        {
            let mut buffers = Vec::with_capacity(6);
            for _ in 0u8..3 {
                for _ in 0u8..2 {
                    let child = Box::new([0u8; 16]);
                    buffers.push(child);
                }
            }
            buffers
        }
        fn caller() resources peak(memory) <= 512 {
            {
                let buffers = select(3);
                assert(current(memory) <= 80);
            }
            {
                let buffers = select(0);
                assert(current(memory) <= 24);
            }
            let mut buffers = nested();
            let child = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// Borrowed collection updates share the same original and newly added regions.
test_verify_one_file! {
    #[test] range_helpers_preserve_borrowed_ownership verus_code! {
        use vstd::prelude::*;
        spec fn budget(count: u16) -> nat { 256 + (count as nat) * 24 }
        fn append(buffers: &mut Vec<Box<[u8; 16]>>, count: u16)
            requires old(buffers).len() + count <= 4,
            ensures final(buffers).len() == old(buffers).len() + count,
            resources peak(memory) <= budget(count),
        {
            // Frame the input length bound in Verus's isolated loop query.
            for _ in 0u16..count
                invariant old(buffers).len() + count <= 4, buffers.len() <= 4,
            {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
            }
        }
        fn caller() resources peak(memory) <= 512 {
            let mut buffers = Vec::with_capacity(4);
            let original = Box::new([0u8; 16]);
            buffers.push(original);
            append(&mut buffers, 2);
            let child = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// A precise range summary keeps every child allocation available to its caller.
test_verify_one_file! {
    #[test] range_builders_export_complete_forests verus_code! {
        use vstd::prelude::*;
        spec fn budget(count: u16) -> nat { 256 + (count as nat) * 24 }
        fn build(count: u16) -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == count,
            resources peak(memory) <= budget(count),
        {
            let mut buffers = Vec::with_capacity(count as usize);
            for index in 0u16..count {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
            }
            buffers
        }
        fn caller() resources peak(memory) <= 512 {
            {
                let mut buffers = build(2);
                let child = buffers.pop().unwrap();
                drop(buffers);
                assert(current(memory) <= 24);
            }
            let empty = build(0);
            assert(current(memory) <= 24);
            drop(empty);
            assert(current(memory) <= 0);
        }
    } => Ok(())
}

// Guards over the yielded integer select the same exact visit intervals as while.
test_verify_one_file! {
    #[test] range_continues_preserve_selected_children verus_code! {
        use vstd::prelude::*;
        fn build() -> (buffers: Vec<Box<[u8; 16]>>)
            ensures buffers.len() == 2,
            resources peak(memory) <= 256,
        {
            let mut buffers = Vec::with_capacity(4);
            for index in 0u8..4 {
                if index < 2 { continue; }
                let child = Box::new([0u8; 16]);
                buffers.push(child);
            }
            buffers
        }
        fn caller() resources peak(memory) <= 256 {
            let mut buffers = build();
            let child = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// Adapter composition retains state bytes and uses the selected scalar values.
#[test]
fn adapted_ranges_keep_yielded_sizes_and_empty_selections() {
    let code = verus_code! {
        use vstd::prelude::*;
        fn build() -> (buffers: Vec<Vec<u32>>)
            ensures buffers.len() == 2,
            resources peak(memory) <= 512,
        {
            let mut buffers = Vec::with_capacity(2);
            for capacity in (1u16..5).rev().skip(1).take(2) {
                let child = Vec::<u32>::with_capacity(capacity as usize);
                buffers.push(child);
            }
            buffers
        }
        #[verifier::exec_allows_no_decreases_clause]
        fn decreasing() -> (buffers: Vec<Vec<u32>>)
            ensures buffers.len() == 2,
            resources peak(memory) <= 512,
        {
            let mut buffers = Vec::with_capacity(2);
            let mut capacity = 3u16;
            while capacity > 1 {
                let child = Vec::<u32>::with_capacity(capacity as usize);
                buffers.push(child);
                capacity -= 1;
            }
            buffers
        }
        fn caller() resources peak(memory) <= 512 {
            let mut buffers = build();
            let last = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= RETAINED_BOUND);
            drop(last);
            assert(current(memory) <= 0);
            let mut buffers = decreasing();
            let last = buffers.pop().unwrap();
            drop(buffers);
            assert(current(memory) <= 32);
        }
        fn empty() -> Vec<Box<[u8; 16]>> resources peak(memory) <= 256 {
            let mut buffers = Vec::with_capacity(2);
            for index in (5u16..1).rev().skip(10).take(2) {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
            }
            buffers
        }
        fn empty_caller() resources peak(memory) <= 256 {
            let buffers = empty();
            assert(current(memory) <= 40);
        }
    };
    verify_one_file("adapted_ranges", code.replace("RETAINED_BOUND", "32"), &["--compile"])
        .unwrap();
    let err = verify_one_file("adapted_ranges_short", code.replace("RETAINED_BOUND", "31"), &[])
        .unwrap_err();
    assert_vir_error_msg(err, "conditional memory budget exceeded");
}

// Breaking a single visit still exports a conditional, complete returned forest.
test_verify_one_file! {
    #[test] single_visit_breaks_keep_empty_and_nonempty_paths verus_code! {
        use vstd::prelude::*;
        fn build(count: u16) -> Vec<Box<[u8; 16]>> resources peak(memory) <= 256 {
            let mut buffers = Vec::with_capacity(1);
            for index in 0u16..count {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
                break;
            }
            buffers
        }
        fn caller() resources peak(memory) <= 256 {
            {
                let buffers = build(0);
                assert(current(memory) <= 32);
            }
            let buffers = build(3);
            assert(current(memory) <= 48);
        }
    } => Ok(())
}

// Nested labelled exits release iterator state and temporary heap allocations.
test_verify_one_file! {
    #[test] labelled_exits_and_returns_unwind_iterator_scopes verus_code! {
        use vstd::prelude::*;
        fn continuing() resources peak(memory) <= 256 {
            'outer: for index in 0u8..3 {
                let outer = Box::new([0u8; 32]);
                for inner in 0u8..2 {
                    let scratch = Box::new([0u8; 16]);
                    continue 'outer;
                }
            }
            assert(current(memory) <= 0);
        }
        fn section_break() resources peak(memory) <= 256 {
            for index in 0u8..3 {
                resources peak(memory) <= 24 {
                    let scratch = Box::new([0u8; 16]);
                    break;
                }
            }
            assert(current(memory) <= 0);
        }
        fn returning() -> Box<[u8; 16]> resources peak(memory) <= 256 {
            for index in 0u8..3 {
                let scratch = Box::new([0u8; 32]);
                let result = Box::new([0u8; 16]);
                return result;
            }
            Box::new([0u8; 16])
        }
        fn caller() resources peak(memory) <= 256 {
            let result = returning();
            assert(current(memory) <= 24);
        }
    } => Ok(())
}

// Reusing a named iterator does not depend on its source spelling or alias.
test_verify_one_file! {
    #[test] named_range_aliases_and_signed_bounds verus_code! {
        use vstd::prelude::*;
        type Indices = core::ops::Range<i16>;
        fn example() resources peak(memory) <= 128 {
            let indices: Indices = -2..2;
            for value in indices {
                let scratch = Box::new([0u8; 16]);
            }
            assert(current(memory) <= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrowed_slice_visits_use_the_existing_pointees verus_code! {
        use vstd::prelude::*;

        fn read(block: &[u8; 16]) -> u8 resources peak(memory) <= 16 {
            block[0]
        }

        fn visit(blocks: &[[u8; 16]]) resources peak(memory) <= 128 {
            for block in blocks {
                let _checksum = read(block);
            }
            assert(current(memory) <= ref_size(blocks));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrowed_vector_visits_keep_owning_elements_available_to_helpers verus_code! {
        use vstd::prelude::*;

        fn read(block: &Box<[u8; 16]>) -> u8 resources peak(memory) <= 16 {
            block[0]
        }

        fn visit(blocks: &Vec<Box<[u8; 16]>>) resources peak(memory) <= 128 {
            for block in blocks {
                let _checksum = read(block);
            }
        }

        fn caller() resources peak(memory) <= 192 {
            let mut blocks = Vec::with_capacity(2);
            blocks.push(Box::new([0u8; 16]));
            visit(&blocks);
            assert(blocks.len() == 1);
        }
    } => Ok(())
}

#[test]
fn borrowed_vector_cleanup_preserves_backing_and_owned_children() {
    let source = r#"
        fn empty() resources peak(memory) <= 150 {
            let blocks = Vec::<Box<[u8; 16]>>::with_capacity(2);
            for block in &blocks {
                let _first = block[0];
            }
            assert(blocks.len() == 0);
            assert(current(memory) <= 40);
        }

        fn early_exit() resources peak(memory) <= 150 {
            let mut blocks = Vec::with_capacity(2);
            blocks.push(Box::new([0u8; 16]));
            for block in &blocks {
                let _first = block[0];
                break;
            }
            assert(blocks.len() == 1);
            assert(current(memory) <= 56);
        }
    "#;
    super::support::verifies("borrowed_vector_cleanup", source);
    super::support::rejects(
        "borrowed_vector_cleanup_short",
        &source.replace("<= 56", "<= 55"),
        "conditional memory budget exceeded: cannot prove the required model bytes fit the declared bound",
    );
}

#[test]
fn consuming_vector_break_keeps_only_the_selected_owner() {
    let source = r#"
        fn early_exit() resources peak(memory) <= 256 {
            let mut kept = Vec::with_capacity(1);
            let mut blocks = Vec::with_capacity(2);
            blocks.push(Box::new([1u8; 16]));
            blocks.push(Box::new([2u8; 16]));
            for block in blocks {
                assert(block[0] == 1);
                assert(peak(memory) <= 144);
                kept.push(block);
                break;
            }
            assert(kept.len() == 1);
            assert(kept[0][0] == 1);
            assert(current(memory) <= 48);
        }
    "#;
    super::support::verifies("consuming_vector_break", source);
    super::support::rejects(
        "consuming_vector_break_short",
        &source.replace("<= 48", "<= 47"),
        "conditional memory budget exceeded",
    );
}

#[test]
fn consuming_vector_retains_spare_backing_through_the_last_visit() {
    let source = r#"
        fn last() resources peak(memory) <= 256 {
            let mut blocks = Vec::with_capacity(4);
            blocks.push(Box::new([7u8; 16]));
            for block in blocks {
                assert(block[0] == 7);
                // Iterator, four reserved slots, yielded handle, and payload.
                assert(current(memory) <= 88);
                break;
            }
            assert(current(memory) <= 0);
        }
    "#;
    super::support::verifies("consuming_vector_last", source);
    super::support::rejects(
        "consuming_vector_last_short",
        &source.replace("<= 88", "<= 87"),
        "conditional memory budget exceeded",
    );
}

test_verify_one_file! {
    #[test] consuming_vector_exhaustion_drops_backing verus_code! {
        use vstd::prelude::*;

        fn drain() resources peak(memory) <= 256 {
            let mut blocks = Vec::with_capacity(2);
            blocks.push(Box::new([1u8; 16]));
            blocks.push(Box::new([2u8; 16]));
            for block in blocks {
                drop(block);
            }
            assert(current(memory) <= 0);
        }

        fn empty_reserved() resources peak(memory) <= 256 {
            let blocks = Vec::<Box<[u8; 16]>>::with_capacity(2);
            for block in blocks {
                assert(false);
                drop(block);
            }
            assert(current(memory) <= 0);
        }

        fn transfer_empty() -> (kept: Vec<Box<[u8; 16]>>)
            ensures kept.len() == 0,
            resources peak(memory) <= 125,
        {
            let mut kept = Vec::with_capacity(2);
            let blocks = Vec::<Box<[u8; 16]>>::with_capacity(2);
            for block in blocks {
                assert(false);
                let scratch = [0u8; 512];
                kept.push(block);
            }
            kept
        }
    } => Ok(())
}

#[test]
fn consuming_vector_collects_and_returns_children_in_order() {
    let source = r#"
        fn collect() -> (kept: Vec<Vec<u8>>)
            ensures kept.len() == 2,
            resources peak(memory) <= 512,
        {
            let mut kept = Vec::with_capacity(2);
            let mut blocks = Vec::with_capacity(2);
            let first = Vec::<u8>::with_capacity(7);
            blocks.push(first);
            let second = Vec::<u8>::with_capacity(3);
            blocks.push(second);
            for block in blocks {
                kept.push(block);
            }
            kept
        }

        fn caller() resources peak(memory) <= 1024 {
            let mut kept = collect();
            assert(current(memory) <= 82);
            let last = kept.pop().unwrap();
            drop(kept);
            // The second child reserves three bytes and the first reserves seven.
            assert(current(memory) <= 27);
        }
    "#;
    super::support::verifies("consuming_vector_collect", source);
    super::support::rejects(
        "consuming_vector_collect_short",
        &source.replace("<= 27", "<= 26"),
        "conditional memory budget exceeded",
    );
}

test_verify_one_file! {
    #[test] consuming_vector_return_releases_the_unvisited_children verus_code! {
        use vstd::prelude::*;

        fn first() -> (kept: Vec<Box<[u8; 16]>>)
            ensures kept.len() == 1 && kept[0][0] == 1,
            resources peak(memory) <= 256,
        {
            let mut kept = Vec::with_capacity(1);
            let mut blocks = Vec::with_capacity(2);
            blocks.push(Box::new([1u8; 16]));
            blocks.push(Box::new([2u8; 16]));
            for block in blocks {
                kept.push(block);
                return kept;
            }
            kept
        }

        fn caller() resources peak(memory) <= 300 {
            let kept = first();
            assert(current(memory) <= 48);
        }
    } => Ok(())
}

// Only a reachable branch needs its temporary storage reserved at the loop head.
#[test]
fn consuming_vector_reserves_conditional_workspace_on_its_path() {
    // Both ordinary visits fit this budget. Taking the workspace branch exceeds it.
    const VISIT_BUDGET_BYTES: u64 = 240;
    const OPTIONAL_WORKSPACE_BYTES: usize = 4 * 1024;

    let inline = r#"
        fn visit(flag: bool)
            requires !flag,
            resources peak(memory) <= VISIT_BUDGET_BYTES,
        {
            let mut blocks = Vec::with_capacity(2);
            blocks.push(5u64);
            for block in blocks {
                if flag {
                    let workspace = [0u8; OPTIONAL_WORKSPACE_BYTES];
                }
            }
        }
    "#;
    let transfer = r#"
        fn collect(flag: bool)
            requires !flag,
            resources peak(memory) <= VISIT_BUDGET_BYTES,
        {
            let mut kept = Vec::with_capacity(2);
            let mut blocks = Vec::with_capacity(2);
            blocks.push(Box::new(5u64));
            for block in blocks {
                if !flag {
                    let marker = 0u8;
                } else {
                    let workspace = [0u8; OPTIONAL_WORKSPACE_BYTES];
                }
                kept.push(block);
            }
        }
    "#;
    for (name, code, message) in [
        ("inline", inline, "memory budget exceeded for the consuming iterator"),
        ("transfer", transfer, "memory budget exceeded for transferring iterator elements"),
    ] {
        // Resource contracts currently require the budget as a literal here.
        let code = code
            .replace("VISIT_BUDGET_BYTES", &VISIT_BUDGET_BYTES.to_string())
            .replace("OPTIONAL_WORKSPACE_BYTES", &OPTIONAL_WORKSPACE_BYTES.to_string());
        super::support::verifies(&format!("iterator_guard_{name}"), &code);
        let reachable = code.replace("requires !flag", "requires flag");
        let err = verify_one_file(
            &format!("iterator_guard_{name}_reachable"),
            format!("use vstd::prelude::*; verus! {{ {reachable} }}"),
            &[],
        )
        .unwrap_err();
        assert_eq!(err.errors.len(), 1);
        assert_help_error_msg(err, message);
    }
}

// A loop-carried slice cannot export its old length as an allocation size.
test_verify_one_file! {
    #[test] reassigned_slice_length_cannot_size_a_returned_allocation verus_code! {
        use vstd::prelude::*;

        fn select_len(a: &[u8], b: &[u8], count: u8) -> (n: usize)
            ensures count > 0 ==> n == b.len(), count == 0 ==> n == a.len(),
            resources peak(memory) <= 200,
        {
            let mut s = a;
            let mut i = 0u8;
            while i < count
                invariant i <= count, i > 0 ==> s == b, i == 0 ==> s == a,
                decreases count - i,
            {
                s = b;
                i += 1;
            }
            s.len()
        }

        fn build(a: &[u8], b: &[u8]) -> (v: Vec<Vec<u8>>)
            requires a.len() == 1, b.len() == 32,
            ensures v.len() == 1,
            resources peak(memory) <= 512,
        {
            let n = select_len(a, b, 1);
            let inner = Vec::<u8>::with_capacity(n);
            let mut out = Vec::with_capacity(1);
            out.push(inner);
            out
        }
        fn caller(a: &[u8], b: &[u8])
            requires a.len() == 1, b.len() == 32,
            resources peak(memory) <= 1024,
        {
            let v = build(a, b);
            // The inner vector reserves 32 bytes, bringing the live total to 112.
            assert(current(memory) <= 81);
        }
    } => Err(err) => assert_vir_error_msg(err, "no precise helper summary can be inferred")
}

// Unmodeled iterable layouts and adapters still need explicit rules.
#[test]
fn unsupported_iterator_classes_and_adapters_reject() {
    for (name, code, diagnostic) in [
        (
            "consuming_rev",
            "let values = Vec::<u64>::new(); for value in values.into_iter().rev() { }",
            "does not support adapters over collection iterators",
        ),
        (
            "array_iter",
            "let values = [0u32; 4]; for value in &values { let copy = *value; }",
            "does not support this slice type",
        ),
        (
            "inclusive",
            "for value in 0u8..=4 { let copy = value; }",
            "does not support struct layouts outside this crate",
        ),
        (
            "zip",
            "for values in (0u8..4).zip(0u8..4) { }",
            "does not support struct layouts outside this crate",
        ),
    ] {
        let source = format!(
            "use vstd::prelude::*; verus! {{ fn example() resources peak(memory) <= 100000 {{ {code} }} }}"
        );
        let err = verify_one_file(name, source, &[]).unwrap_err();
        assert_vir_error_msg(err, diagnostic);
    }
}

// A partial visit cannot silently export a full-count ownership summary.
test_verify_one_file! {
    #[test] partial_for_exits_without_a_precise_count_reject verus_code! {
        use vstd::prelude::*;
        fn build(stop: bool) -> Vec<Box<[u8; 16]>> resources peak(memory) <= 100000 {
            let mut buffers = Vec::with_capacity(4);
            for index in 0u8..4 {
                let child = Box::new([0u8; 16]);
                buffers.push(child);
                if stop { break; }
            }
            buffers
        }
    } => Err(err) => assert_vir_error_msg(err, "no precise helper summary can be inferred")
}
