//! Individual allocation metadata survives checked helper boundaries.
use super::support::{rejects, verifies};

#[test]
fn unsupported_incoming_extractions_reject_even_with_a_larger_budget() {
    for (name, parameter, operation, result) in [
        ("borrowed_pop", "v: &mut Vec<Box<u32>>", "v.pop()", "Option<Box<u32>>"),
        ("owned_pop", "mut v: Vec<Box<u32>>", "v.pop()", "Option<Box<u32>>"),
        // Discarding the result must not bypass the unsupported ownership effect.
        ("discarded_pop", "v: &mut Vec<Box<u32>>", "v.pop();", "()"),
    ] {
        rejects(
            name,
            &format!(
                "fn f({parameter}) -> {result} resources peak(memory) <= 10000 {{ {operation} }}"
            ),
            "popping an incoming owning child",
        );
    }
    rejects(
        "owned_remove",
        "fn f(mut v: Vec<Box<u32>>) -> Box<u32>
            resources peak(memory) <= 10000 { v.remove(0) }",
        "extracting an incoming child from an owned collection",
    );
}

#[test]
fn incoming_indexed_mutation_preserves_selected_and_sibling_allocations() {
    let code = "fn grow(v: &mut Vec<Vec<u32>>, i: usize)
        requires i < old(v).len(), old(v)[i as int].len() == 0,
        ensures final(v).len() == old(v).len(), final(v)[i as int].len() == 1,
            forall|j: int| 0 <= j < old(v).len() && j != i ==> final(v)[j] == old(v)[j],
        resources peak(memory) <= 32 { v[i].push(7); }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::new(); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            grow(&mut v, 0); grow(&mut v, 1);
            v[0].push(8); v[1].push(8);
            let scratch = [0u8;200];
        }";
    verifies("incoming_index", &code.replace("BOUND", "320"));
    rejects("incoming_index_short", &code.replace("BOUND", "319"), "memory budget exceeded");
}

#[test]
fn a_template_cannot_be_applied_to_opaque_arguments() {
    rejects(
        "opaque_relay",
        "fn pass(v: Vec<Box<u32>>) -> Vec<Box<u32>>
            resources peak(memory) <= 100 { v }
        fn relay(v: Vec<Box<u32>>) -> Vec<Box<u32>>
            resources peak(memory) <= 10000 { pass(v) }",
        "a runtime ownership call without precise argument metadata",
    );
}

#[test]
fn returned_collections_preserve_child_reservations() {
    let code = "fn make() -> (v: Vec<Vec<u32>>)
        ensures v.len() == 1, v[0].len() == 0, resources peak(memory) <= 100 {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::with_capacity(4); v.push(child);
            assert(current(memory) <= 64); assert(peak(memory) <= 100); v
        }
        fn relay() -> (v: Vec<Vec<u32>>)
            ensures v.len() == 1, v[0].len() == 0, resources peak(memory) <= 100 { make() }
        fn f() resources peak(memory) <= BOUND {
            let mut v = relay(); v[0].push(7); let scratch = [0u8;80];
        }";
    verifies("returned_forest", &code.replace("BOUND", "144"));
    rejects("returned_forest_short", &code.replace("BOUND", "143"), "memory budget exceeded");
}

#[test]
fn appending_an_owned_parameter_preserves_both_footprints() {
    let code = "fn append(v: &mut Vec<Vec<u32>>, child: Vec<u32>)
        requires old(v).len() <= 1,
        ensures final(v)@ == old(v)@.push(child), resources peak(memory) <= 96 { v.push(child); }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); append(&mut v, b);
            v[0].push(7); v[1].push(9); let scratch = [0u8;256];
        }";
    // Make retained storage dominate the helper's temporary allowance:
    // handle 24 + outer buffer 48 + child buffers 16 and 32 + scratch 256.
    verifies("append_forest", &code.replace("BOUND", "376"));
    rejects("append_forest_short", &code.replace("BOUND", "375"), "memory budget exceeded");
}

#[test]
fn fixed_children_and_boxed_slices_compose_through_results() {
    verifies(
        "fixed_slice_forest",
        "struct Rows { values: Box<[Vec<u32>]>, }
        fn make() -> (r: Rows)
            ensures r.values.len() == 1, r.values[0].len() == 0, resources peak(memory) <= 144 {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let values = v.into_boxed_slice(); Rows { values }
        }
        fn relay() -> (r: Rows)
            ensures r.values.len() == 1, r.values[0].len() == 0, resources peak(memory) <= 144 { make() }
        fn f() resources peak(memory) <= 160 {
            let mut rows = relay(); rows.values[0].push(7);
            let scratch = [0u8;104];
        }",
    );
}
