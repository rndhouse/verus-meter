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
    assert_vir_error_msg(err, "memory budget");
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
    assert_vir_error_msg(err, "memory budget");
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

// Owning containers and borrowed element iterators need explicit lifetime rules.
#[test]
fn unsupported_iterator_classes_and_adapters_reject() {
    for (name, code) in [
        (
            "owning",
            "let values = Vec::<Box<[u8; 16]>>::new(); for value in values { drop(value); }",
        ),
        ("borrowed", "let values = [0u32; 4]; for value in &values { let copy = *value; }"),
        ("inclusive", "for value in 0u8..=4 { let copy = value; }"),
        ("zip", "for values in (0u8..4).zip(0u8..4) { }"),
    ] {
        let source = format!(
            "use vstd::prelude::*; verus! {{ fn example() resources peak(memory) <= 100000 {{ {code} }} }}"
        );
        let err = verify_one_file(name, source, &[]).unwrap_err();
        assert_vir_error_msg(err, "does not support");
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
