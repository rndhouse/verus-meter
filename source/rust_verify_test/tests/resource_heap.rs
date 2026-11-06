#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

fn exact_peak(name: &str, code: &str, peak: u64) {
    let source = |budget: u64| {
        format!(
            "use vstd::prelude::*; verus! {{ {} }}",
            code.replace("BUDGET", &budget.to_string())
        )
    };
    verify_one_file(name, source(peak), &[]).unwrap();
    let err = verify_one_file(&format!("{name}_short"), source(peak - 1), &[]).unwrap_err();
    assert_vir_error_msg(err, &format!("peak {peak} bytes exceeds budget {} bytes", peak - 1));
}

#[test]
fn local_box() {
    exact_peak(
        "local_box",
        r#"fn f() mem_peak <= BUDGET { let data = Box::new([0u8; 16]); assert(current(mem_peak) <= mem_size(data) + mem_size([u8; 16])); }"#,
        24,
    );
}

#[test]
fn scopes_reuse_heap() {
    exact_peak(
        "scopes_reuse_heap",
        r#"fn f() mem_peak <= BUDGET { { let data = Box::new([0u8; 16]); } { let data = Box::new([0u8; 16]); } }"#,
        24,
    );
}

#[test]
fn overlapping_boxes() {
    exact_peak(
        "overlapping_boxes",
        r#"fn f() mem_peak <= BUDGET { let first = Box::new([0u8; 16]); let second = Box::new([0u8; 16]); }"#,
        48,
    );
}

#[test]
fn move_transfers_one_allocation() {
    exact_peak(
        "move_transfers_one_allocation",
        r#"fn f() mem_peak <= BUDGET { let first = Box::new([0u8; 16]); let second = first; }"#,
        32,
    );
}

#[test]
fn drop_releases_heap_but_keeps_slots() {
    exact_peak(
        "drop_releases_heap_but_keeps_slots",
        r#"fn f() mem_peak <= BUDGET { let first = Box::new([0u8; 16]); drop(first); let second = Box::new([0u8; 16]); }"#,
        32,
    );
}

#[test]
fn moved_owner_releases_once() {
    exact_peak(
        "moved_owner_releases_once",
        r#"fn f() mem_peak <= BUDGET { let first = Box::new([0u8; 16]); let second = first; drop(second); let third = Box::new([0u8; 16]); }"#,
        40,
    );
}

#[test]
fn inner_scope_can_consume_outer_owner() {
    exact_peak(
        "inner_scope_can_consume_outer_owner",
        r#"fn f() mem_peak <= BUDGET { let first = Box::new([0u8; 16]); { let moved = first; } let second = Box::new([0u8; 16]); }"#,
        32,
    );
}

#[test]
fn inner_scope_can_drop_outer_owner() {
    exact_peak(
        "inner_scope_can_drop_outer_owner",
        r#"fn f() mem_peak <= BUDGET { let first = Box::new([0u8; 16]); { drop(first); } let second = Box::new([0u8; 16]); }"#,
        32,
    );
}

#[test]
fn standalone_boxes_are_released() {
    exact_peak(
        "standalone_boxes_are_released",
        r#"fn f() mem_peak <= BUDGET { Box::new([0u8; 16]); Box::new([0u8; 16]); }"#,
        24,
    );
}

#[test]
fn source_array_stays_live() {
    exact_peak(
        "source_array_stays_live",
        r#"fn f() mem_peak <= BUDGET { let original = [0u8; 16]; let boxed = Box::new(original); assert(original[0] == 0); }"#,
        40,
    );
}

#[test]
fn boxed_struct() {
    exact_peak(
        "boxed_struct",
        r#"struct Data { value: i64, ready: bool }
fn f() mem_peak <= BUDGET { let mut data = Box::new(Data { value: -1i64, ready: false }); data.value = 2; data.ready = true; assert(data.value == 2 && data.ready); }"#,
        17,
    );
}

#[test]
fn zero_sized_object_tracks_ownership() {
    exact_peak(
        "zero_sized_object_tracks_ownership",
        r#"fn f() mem_peak <= BUDGET { let first = Box::new(()); let second = first; drop(second); }"#,
        16,
    );
}

#[test]
fn borrowed_helper_retains_backing_object() {
    exact_peak(
        "borrowed_helper_retains_backing_object",
        r#"fn fill(data: &mut [u8; 16]) ensures final(data)[0] == 7, mem_peak <= mem_size(data) { data[0] = 7; }
fn f() mem_peak <= BUDGET { let mut data = Box::new([0u8; 16]); fill(&mut *data); assert(data[0] == 7); }"#,
        32,
    );
}

#[test]
fn borrowed_slice_retains_backing_object() {
    exact_peak(
        "borrowed_slice_retains_backing_object",
        r#"fn fill(data: &mut [u8]) requires data.len() >= 1, ensures final(data)[0] == 7, mem_peak <= mem_size(data) { data[0] = 7; }
fn read(data: &[u8]) mem_peak <= mem_size(data) {}
fn f() mem_peak <= BUDGET { let mut data = Box::new([0u8; 16]); fill(&mut *data); read(&*data); assert(data[0] == 7); }"#,
        40,
    );
}

#[test]
fn loop_local_boxes_are_reused() {
    exact_peak(
        "loop_local_boxes_are_reused",
        r#"fn f(mut run: bool) mem_peak <= BUDGET { while run decreases if run { 1int } else { 0int }, { let data = Box::new([0u8; 16]); run = false; } }"#,
        25,
    );
}

#[test]
fn branch_local_boxes_are_reused() {
    exact_peak(
        "branch_local_boxes_are_reused",
        r#"fn f(flag: bool) mem_peak <= BUDGET { if flag { let a = Box::new([0u8; 16]); } else { let b = Box::new([0u8; 8]); } }"#,
        25,
    );
}

#[test]
fn section_local_box_compounds_parent() {
    exact_peak(
        "section_local_box_compounds_parent",
        r#"fn f() mem_peak <= BUDGET { let parent = Box::new([0u8; 16]); mem_peak <= 24 { let child = Box::new([0u8; 16]); } }"#,
        48,
    );
}

#[test]
fn section_can_borrow_parent_object() {
    exact_peak(
        "section_can_borrow_parent_object",
        r#"fn fill(data: &mut [u8; 16]) mem_peak <= 8 { data[0] = 7; }
fn f() mem_peak <= BUDGET { let mut parent = Box::new([0u8; 16]); mem_peak <= 8 { fill(&mut *parent); } }"#,
        32,
    );
}

test_verify_one_file! {
    #[test] conditional_heap_obligations verus_code! {
        use vstd::prelude::*;
        fn f(large: bool) mem_peak <= mem_size(large) + mem_size(Box<[u8; 16]>) + if large { 16 } else { 8 } {
         if large { let data = Box::new([0u8; 16]); } else { let data = Box::new([0u8; 8]); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] conditional_heap_bound_is_enforced verus_code! {
        use vstd::prelude::*;
        fn f(large: bool) mem_peak <= mem_size(large) + 8 + if large { 16 } else { 8 } {
         let data = Box::new([0u8; 16]);
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}

test_verify_one_file! {
    #[test] checkpoint_keeps_previous_heap_peak verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 24 { let data = Box::new([0u8; 16]); drop(data); assert(current(mem_peak) <= 8); }
    } => Err(err) => assert_vir_error_msg(err, "mem_peak assertion failed: peak 24 bytes exceeds bound 8 bytes")
}

test_verify_one_file! {
    #[test] borrow_does_not_release_heap verus_code! {
        use vstd::prelude::*;
        fn read(data: &[u8; 16]) mem_peak <= 8 {}
        fn f() mem_peak <= 40 { let first = Box::new([0u8; 16]); read(&*first); let second = Box::new([0u8; 16]); }
    } => Err(err) => assert_vir_error_msg(err, "peak 48 bytes exceeds budget 40 bytes")
}

test_verify_one_file! {
    #[test] outer_drop_in_branch_rejected verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool) mem_peak <= 200 { let data = Box::new([0u8; 16]); if flag { drop(data); } }
    } => Err(err) => assert_vir_error_msg(err, "moving or dropping an enclosing heap owner")
}

test_verify_one_file! {
    #[test] outer_drop_in_loop_rejected verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool) mem_peak <= 200 { let data = Box::new([0u8; 16]); while flag decreases 1int, { drop(data); } }
    } => Err(err) => assert_vir_error_msg(err, "moving or dropping an enclosing heap owner")
}

test_verify_one_file! {
    #[test] outer_drop_in_section_rejected verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool) mem_peak <= 200 { let data = Box::new([0u8; 16]); mem_peak <= 100 { drop(data); } }
    } => Err(err) => assert_vir_error_msg(err, "moving or dropping an enclosing heap owner")
}

test_verify_one_file! {
    #[test] outer_move_in_branch_rejected verus_code! {
        use vstd::prelude::*;
        fn f(flag: bool) mem_peak <= 100 { let data = Box::new([0u8; 16]); if flag { let moved = data; } }
    } => Err(err) => assert_vir_error_msg(err, "moving or dropping an enclosing heap owner")
}

test_verify_one_file! {
    #[test] owning_parameters_rejected verus_code! {
        use vstd::prelude::*;
        fn f(data: Box<[u8; 16]>) mem_peak <= 100 {}
    } => Err(err) => assert_vir_error_msg(err, "owning box parameters")
}

test_verify_one_file! {
    #[test] nested_boxes_rejected verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 100 { let data = Box::new(Box::new(1u8)); }
    } => Err(err) => assert_vir_error_msg(err, "nested boxes")
}

test_verify_one_file! {
    #[test] owning_struct_fields_rejected verus_code! {
        use vstd::prelude::*;
        struct Owner { data: Box<[u8; 16]> }
        fn f() mem_peak <= mem_size(Owner) {}
    } => Err(err) => assert_vir_error_msg(err, "reference or decorated struct fields")
}

test_verify_one_file! {
    #[test] reassignment_rejected verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 100 { let mut data = Box::new(1u8); data = Box::new(2u8); }
    } => Err(err) => assert_vir_error_msg(err, "reassignment of heap owners")
}

test_verify_one_file! {
    #[test] forget_rejected verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 100 { let data = Box::new(1u8); std::mem::forget(data); }
    } => Err(err) => assert_vir_error_msg(err, "is not supported")
}

test_verify_one_file! {
    #[test] raw_escape_rejected verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 100 { let data = Box::new(1u8); let pointer = Box::into_raw(data); }
    } => Err(err) => assert_vir_error_msg(err, "is not supported")
}

test_verify_one_file! {
    #[test] dropping_contents_cannot_release_box verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 100 { let data = Box::new(1u8); drop(*data); }
    } => Err(err) => assert_vir_error_msg(err, "drop of anything other than a named local heap owner")
}

test_verify_one_file! {
    #[test] dropping_reference_cannot_release_box verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 100 { let data = Box::new(1u8); drop(&*data); }
    } => Err(err) => assert_vir_error_msg(err, "drop of anything other than a named local heap owner")
}

test_verify_one_file! {
    #[test] temporary_box_borrow_rejected verus_code! {
        use vstd::prelude::*;
        fn f() mem_peak <= 100 { let borrowed = &*Box::new(1u8); }
    } => Err(err) => assert_vir_error_msg(err, "this place or borrowed temporary")
}

#[test]
fn aliases_preserve_intrinsic_identity() {
    exact_peak(
        "aliases_preserve_intrinsic_identity",
        r#"use std::boxed::Box as Owned; use std::mem::drop as release; fn f() mem_peak <= BUDGET { let data = Owned::new([0u8; 16]); release(data); let other = Owned::new([0u8; 16]); }"#,
        32,
    );
}

test_verify_one_file! {
    #[test] same_named_function_is_not_drop verus_code! {
        use vstd::prelude::*;
        fn drop(data: &[u8; 16]) mem_peak <= 8 {}
        fn f() mem_peak <= 40 { let first = Box::new([0u8; 16]); drop(&*first); let second = Box::new([0u8; 16]); }
    } => Err(err) => assert_vir_error_msg(err, "peak 48 bytes exceeds budget 40 bytes")
}

#[test]
fn heap_example() {
    verify_one_file(
        "heap_example",
        include_str!("../../../examples/resource/memory/heap.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn overlapping_heap_example_fails_at_second_allocation() {
    let err = verify_one_file(
        "heap_overlap",
        include_str!("../../../examples/resource/memory/expected-failures/heap_overlap.rs").into(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err.clone(), "peak 48 bytes exceeds budget 32 bytes");
    assert!(err.errors[0].spans.iter().any(|span| span.is_primary
        && span.text.iter().any(|line| line.text.contains("let second = Box::new"))));
}

test_verify_one_file! {
    #[test] heap_destructors_are_rejected verus_code! {
        use vstd::prelude::*;
        struct Data { value: u8 }
        impl Drop for Data { fn drop(&mut self) opens_invariants none no_unwind {} }
        fn f() mem_peak <= 100 { let data = Box::new(Data { value: 0 }); }
    } => Err(err) => assert_vir_error_msg(err, "structs with destructors")
}

#[test]
fn shared_borrow_and_copy_contents() {
    exact_peak(
        "shared_borrow_and_copy_contents",
        r#"fn read(data: &[u8; 16]) mem_peak <= 8 {}
fn f() mem_peak <= BUDGET { let data = Box::new([0u8; 16]); read(&*data); let copy = *data; assert(copy[0] == 0); }"#,
        40,
    );
}

#[test]
fn scalar_contents_and_local_borrows() {
    exact_peak(
        "scalar_contents_and_local_borrows",
        r#"fn f() mem_peak <= BUDGET { let mut data = Box::new(1u32); let borrowed = &mut *data; *borrowed = 2; let shared = &*data; let copy = *data; assert(copy == 2 && *shared == 2); }"#,
        32,
    );
}

test_verify_one_file! {
    #[test] heap_budgets_compose_for_actual_arguments verus_code! {
        use vstd::prelude::*;
        fn helper(large: bool)
            mem_peak <= mem_size(large) + mem_size(Box<u8>) + if large { 16 } else { 8 },
        {
            if large { let data = Box::new([0u8; 16]); }
            else { let data = Box::new([0u8; 8]); }
        }
        fn caller(large: bool)
            mem_peak <= mem_size(large) + mem_size(Box<u8>) + mem_size(u8) + mem_peak(helper(large)),
        {
            let retained = Box::new(0u8);
            helper(large);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] heap_cannot_hide_behind_conditional_call verus_code! {
        use vstd::prelude::*;
        fn helper(large: bool)
            mem_peak <= mem_size(large) + mem_size(Box<u8>) + if large { 16 } else { 8 },
        {
            if large { let data = Box::new([0u8; 16]); }
            else { let data = Box::new([0u8; 8]); }
        }
        fn caller(large: bool)
            mem_peak <= mem_size(large) + mem_peak(helper(large)),
        {
            let retained = Box::new(0u8);
            helper(large);
        }
    } => Err(err) => assert_vir_error_msg(err, "conditional memory budget exceeded")
}
