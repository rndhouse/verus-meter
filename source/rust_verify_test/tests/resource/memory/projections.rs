//! Indexed borrows use the same owner shapes and retained effects as parameters.

use super::support::{rejects, verifies};

#[test]
fn indexed_read_borrows_preserve_the_collection_charge() {
    verifies(
        "indexed_read",
        "fn read(b: &Box<u32>) -> u32 resources peak(memory) <= 12 { **b }
        fn f(v: &Vec<Box<u32>>, i: usize) -> u32
            requires i < v.len(), resources peak(memory) <= 40 { read(&v[i]) }",
    );
}

#[test]
fn direct_indexed_growth_retains_new_allocations() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut outer = Vec::<Vec<u32>>::with_capacity(1);
        let child = Vec::<u32>::new(); outer.push(child);
        outer[0].push(1); let scratch = [0u8;64];
    }";
    verifies("indexed_growth", &code.replace("BOUND", "128"));
    rejects("indexed_growth_short", &code.replace("BOUND", "127"), "memory budget exceeded");
}

#[test]
fn indexed_helper_growth_replaces_the_selected_child_charge() {
    let code = "fn grow(v: &mut Vec<u32>)
        requires old(v).len() <= 1, ensures final(v).len() == old(v).len() + 1,
        resources peak(memory) <= 24 { v.push(1); }
        fn f() resources peak(memory) <= BOUND {
            let mut outer = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::new(); outer.push(child);
            grow(&mut outer[0]); grow(&mut outer[0]); let scratch = [0u8;64];
        }";
    verifies("indexed_helpers", &code.replace("BOUND", "136"));
    rejects("indexed_helpers_short", &code.replace("BOUND", "135"), "memory budget exceeded");
}

#[test]
fn fixed_and_runtime_paths_compose_recursively() {
    verifies(
        "nested_indexed_paths",
        "struct Item { data: Box<Vec<u32>>, spare: Box<u32> }
        fn f() resources peak(memory) <= 1000 {
            let mut outer = Vec::<Vec<Item>>::with_capacity(1);
            let mut middle = Vec::<Item>::with_capacity(1);
            let item = Item { data: Box::new(Vec::<u32>::new()), spare: Box::new(7) };
            middle.push(item); outer.push(middle);
            outer[0][0].data.push(1);
            { let n = *outer[0][0].spare; assert(n == 7); }
            drop(outer); let scratch = [0u8;1000];
        }",
    );
}

#[test]
fn nested_projection_updates_are_counted_once() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut outer = Vec::<Vec<Vec<u32>>>::with_capacity(1);
        let mut middle = Vec::<Vec<u32>>::with_capacity(1);
        let child = Vec::<u32>::new(); middle.push(child); outer.push(middle);
        outer[0][0].push(1); let scratch = [0u8;64];
    }";
    verifies("nested_projected_sum", &code.replace("BOUND", "152"));
    rejects("nested_projected_sum_short", &code.replace("BOUND", "151"), "memory budget exceeded");
}

#[test]
fn selection_uses_a_runtime_index() {
    let code = "fn f(i: usize) requires i < 2, resources peak(memory) <= BOUND {
        let mut outer = Vec::<Vec<u32>>::with_capacity(2);
        let a = Vec::<u32>::new(); outer.push(a);
        let b = Vec::<u32>::new(); outer.push(b);
        outer[i].push(1); let scratch = [0u8;64];
    }";
    verifies("runtime_projection", &code.replace("BOUND", "160"));
    rejects("runtime_projection_short", &code.replace("BOUND", "159"), "memory budget exceeded");
}

#[test]
fn branch_local_projection_effects_remain_path_sensitive() {
    let code = "fn f(flag: bool) resources peak(memory) <= BOUND {
        let mut outer = Vec::<Vec<u32>>::with_capacity(1);
        let child = Vec::<u32>::new(); outer.push(child);
        if flag { outer[0].push(1); }
        let scratch = [0u8;64];
    }";
    verifies("branch_projection", &code.replace("BOUND", "129"));
    rejects("branch_projection_short", &code.replace("BOUND", "128"), "memory budget exceeded");
}

#[test]
fn indexed_captures_keep_input_lifetimes_until_collection_drop() {
    verifies(
        "indexed_input_lifetime",
        "struct Item { data: Box<[u8;80]> }
        fn replace(p: &mut Item, data: Box<[u8;80]>) resources peak(memory) <= 16 { p.data = data; }
        fn consume(b: Box<[u8;80]>) resources peak(memory) <= 200 {
            let mut v = Vec::<Item>::with_capacity(1);
            let first = Item { data: Box::new([0u8;80]) }; v.push(first);
            replace(&mut v[0], b); drop(v);
        }
        fn f() resources peak(memory) <= 1000 {
            let b = Box::new([0u8;80]); consume(b); let scratch = [0u8;1000];
        }",
    );
}

#[test]
fn helper_replacement_of_an_element_field_releases_displaced_storage() {
    let code = "struct Item { data: Box<[u8;16]> }
        fn replace(p: &mut Item, data: Box<[u8;16]>) resources peak(memory) <= 16 { p.data = data; }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Item>::with_capacity(1);
            let item = Item { data: Box::new([0u8;16]) }; v.push(item);
            let replacement = Box::new([0u8;16]); replace(&mut v[0], replacement);
            let scratch = [0u8;64];
        }";
    verifies("indexed_replacement", &code.replace("BOUND", "112"));
    rejects("indexed_replacement_short", &code.replace("BOUND", "111"), "memory budget exceeded");
}

#[test]
fn indexed_boxed_slice_children_use_the_same_projection() {
    verifies(
        "indexed_boxed_slice",
        "fn f() resources peak(memory) <= 256 {
        let mut v = Vec::<Vec<u32>>::with_capacity(1);
        let child = Vec::<u32>::new(); v.push(child);
        let mut slice = v.into_boxed_slice(); slice[0].push(1);
        drop(slice); let scratch = [0u8;256];
    }",
    );
}

#[test]
fn indexed_assignments_release_displaced_bytes() {
    verifies(
        "indexed_assignment",
        "fn f() resources peak(memory) <= 200 {
        let mut v = Vec::<Box<u32>>::with_capacity(1);
        let first = Box::new(1u32); v.push(first);
        let replacement = Box::new(2u32); v[0] = replacement;
        assert(*v[0] == 2); drop(v); let scratch = [0u8;200];
    }",
    );
}

#[test]
fn projections_cannot_hide_section_retention() {
    rejects(
        "indexed_section",
        "fn f() resources peak(memory) <= 256 {
        let mut v = Vec::<Vec<u32>>::with_capacity(1);
        let child = Vec::<u32>::new(); v.push(child);
        resources peak(memory) <= 64 { v[0].push(1); }
    }",
        "changing owning children of an enclosing collection inside a memory section",
    );
}

#[test]
fn borrowed_collection_effects_survive_call_boundaries() {
    verifies(
        "indexed_borrowed_effect",
        "fn grow(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 1, old(v)[0].len() == 0,
        resources peak(memory) <= 24 { v[0].push(1); }
        fn relay(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 1, old(v)[0].len() == 0,
        resources peak(memory) <= 32 { grow(v); }
        fn f() resources peak(memory) <= 200 {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::new(); v.push(child);
            relay(&mut v); drop(v); let scratch = [0u8;200];
        }",
    );
}

#[test]
fn discarding_a_removed_child_releases_its_footprint() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(1);
        let first = Box::new([0u8;16]); v.push(first); v.pop();
        let second = Box::new([0u8;16]); v.push(second);
        let scratch = [0u8;64];
    }";
    verifies("discarded_child", &code.replace("BOUND", "112"));
    rejects("discarded_child_short", &code.replace("BOUND", "111"), "memory budget exceeded");
}

#[test]
fn read_only_indexing_in_a_section_does_not_transfer_ownership() {
    verifies(
        "indexed_section_read",
        "fn read(v: &Vec<u32>) -> (r: usize)
        ensures r == v.len(), resources peak(memory) <= 16 { v.len() }
        fn f() resources peak(memory) <= 128 {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::new(); v.push(child);
            resources peak(memory) <= 24 { let n = read(&v[0]); assert(n == 0); }
        }",
    );
}

#[test]
fn removing_through_helpers_invalidates_length_based_invariants() {
    verifies(
        "indexed_removal_effect",
        "fn remove(v: &mut Vec<Box<u32>>)
        ensures final(v).len() == if old(v).len() == 0 { 0 } else { old(v).len() - 1 },
        resources peak(memory) <= 8 { v.pop(); }
        fn relay(v: &mut Vec<Box<u32>>)
        ensures final(v).len() == if old(v).len() == 0 { 0 } else { old(v).len() - 1 },
        resources peak(memory) <= 16 { remove(v); }
        fn f() resources peak(memory) <= 128 {
            let mut v = Vec::<Box<u32>>::with_capacity(1);
            let b = Box::new(1u32); v.push(b); relay(&mut v);
            let mut i = 0usize;
            while i < 1 invariant i <= 1, v.len() == 0, decreases 1-i, { i += 1; }
        }",
    );
}

#[test]
fn indexed_boxes_preserve_implicit_dereference_paths() {
    verifies(
        "indexed_boxed_vector",
        "fn f() resources peak(memory) <= 256 {
        let mut v = Vec::<Box<Box<Vec<u32>>>>::with_capacity(1);
        let b = Box::new(Box::new(Vec::<u32>::new())); v.push(b);
        v[0].push(1); assert(v[0].len() == 1);
        drop(v); let scratch = [0u8;256];
    }",
    );
}

#[test]
fn scalar_mutation_through_indexed_owners_needs_no_new_heap_charge() {
    verifies(
        "indexed_scalar_update",
        "fn f() resources peak(memory) <= 100 {
        let mut v = Vec::<Box<u32>>::with_capacity(1);
        let b = Box::new(1u32); v.push(b); *v[0] = 2;
        assert(*v[0] == 2);
    }",
    );
}

#[test]
fn indexed_owners_example_verifies_and_compiles() {
    crate::verify_one_file(
        "indexed_owners_example",
        include_str!("../../../../../examples/resource/memory/vectors/indexed_owners.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn computed_indices_are_read_as_pure_values() {
    verifies(
        "computed_projection",
        "fn f(i: usize) requires i == 0, resources peak(memory) <= 200 {
        let mut outer = Vec::<Vec<u32>>::with_capacity(2);
        let a = Vec::<u32>::new(); outer.push(a);
        let b = Vec::<u32>::new(); outer.push(b);
        outer[i + 1].push(1); outer[(i + 2) - 1].push(2);
    }",
    );
}

#[test]
fn original_index_bounds_are_still_checked() {
    rejects(
        "projection_bounds",
        "fn f() resources peak(memory) <= 128 {
        let mut v = Vec::<Box<u32>>::with_capacity(1);
        let b = Box::new(1u32); v.push(b); let borrowed = &v[1];
    }",
        "precondition not satisfied",
    );
}
