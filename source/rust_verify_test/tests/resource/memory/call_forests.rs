//! Individual allocation metadata survives checked helper boundaries.
use super::support::{rejects, verifies};

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
fn borrowed_extraction_transfers_the_selected_allocation() {
    let code = "fn take(v: &mut Vec<Box<[u8;32]>>) -> (r: Option<Box<[u8;32]>>)
        requires old(v).len() == 1, ensures r.is_some(), resources peak(memory) <= 17 { v.pop() }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
            let b = Box::new([0u8;32]); v.push(b);
            let child = take(&mut v).unwrap(); drop(v);
            let scratch = [0u8;200]; drop(child);
        }";
    verifies("borrowed_forest_extraction", &code.replace("BOUND", "240"));
    rejects(
        "borrowed_forest_extraction_short",
        &code.replace("BOUND", "239"),
        "memory budget exceeded",
    );
}

#[test]
fn owned_extraction_releases_the_consumed_container() {
    let code = "fn take(mut v: Vec<Box<[u8;32]>>) -> Box<[u8;32]>
        requires v.len() == 1, resources peak(memory) <= 40 { v.pop().unwrap() }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
            let b = Box::new([0u8;32]); v.push(b);
            let child = take(v); let scratch = [0u8;200]; drop(child);
        }";
    verifies("owned_forest_extraction", &code.replace("BOUND", "240"));
    rejects(
        "owned_forest_extraction_short",
        &code.replace("BOUND", "239"),
        "memory budget exceeded",
    );
}

#[test]
fn removal_preserves_heterogeneous_survivors_and_result() {
    let code = "fn take(v: &mut Vec<Vec<u32>>, i: usize) -> Vec<u32>
        requires old(v).len() == 2, i < 2,
        ensures final(v)@ == old(v)@.remove(i as int), resources peak(memory) <= 40 { v.remove(i) }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            let child = take(&mut v, 0); v[0].push(7);
            let scratch = [0u8;16]; drop(child);
        }";
    verifies("removed_forest", &code.replace("BOUND", "160"));
    rejects("removed_forest_short", &code.replace("BOUND", "159"), "memory budget exceeded");
}

#[test]
fn indexed_helper_growth_preserves_fixed_and_repeated_children() {
    verifies(
        "nested_borrowed_forest",
        "fn grow(v: &mut Vec<Box<Vec<u32>>>, i: usize)
        requires i < old(v).len(), old(v)[i as int].len() <= 1,
        ensures final(v).len() == old(v).len(), resources peak(memory) <= 32 { v[i].push(7); }
        fn relay(v: &mut Vec<Box<Vec<u32>>>, i: usize)
            requires i < old(v).len(), old(v)[i as int].len() <= 1, ensures final(v).len() == old(v).len(),
            resources peak(memory) <= 48 { grow(v, i); }
        fn f(i: usize) requires i < 2, resources peak(memory) <= 200 {
            let mut v = Vec::<Box<Vec<u32>>>::with_capacity(2);
            let a = Box::new(Vec::<u32>::with_capacity(4)); v.push(a);
            let b = Box::new(Vec::<u32>::with_capacity(4)); v.push(b);
            relay(&mut v, i); let scratch = [0u8;64];
        }",
    );
}

#[test]
fn appending_an_owned_parameter_preserves_both_footprints() {
    verifies(
        "append_forest",
        "fn append(v: &mut Vec<Vec<u32>>, child: Vec<u32>)
        requires old(v).len() <= 1,
        ensures final(v)@ == old(v)@.push(child), resources peak(memory) <= 96 { v.push(child); }
        fn f() resources peak(memory) <= 256 {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); append(&mut v, b);
            v[0].push(7); v[1].push(9); let scratch = [0u8;64];
        }",
    );
}

#[test]
fn borrowed_growth_keeps_state_identity_across_a_branch() {
    let code = "fn grow(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 1, old(v)[0].len() <= 1,
        ensures final(v).len() == 1, final(v)[0].len() == old(v)[0].len() + 1,
        resources peak(memory) <= 24 { v[0].push(7); }
        fn f(flag: bool) resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::with_capacity(4); v.push(child);
            if flag { grow(&mut v); }
            v[0].push(9); let scratch = [0u8;80];
        }";
    verifies("branch_forest", &code.replace("BOUND", "145"));
    rejects("branch_forest_short", &code.replace("BOUND", "144"), "memory budget exceeded");
}

#[test]
fn helper_extraction_preserves_forests_in_a_caller_loop() {
    verifies(
        "loop_forest_extraction",
        "fn take(v: &mut Vec<Box<[u8;32]>>) -> (r: Option<Box<[u8;32]>>)
        requires old(v).len() > 0,
        ensures r.is_some(), final(v).len() == old(v).len() - 1,
        resources peak(memory) <= 17 { v.pop() }
        fn f() resources peak(memory) <= 176 {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(2);
            let a = Box::new([0u8;32]); v.push(a);
            let b = Box::new([0u8;32]); v.push(b);
            while v.len() > 0 invariant v.len() <= 2, decreases v.len(), {
                let child = take(&mut v).unwrap();
                let scratch = [0u8;64]; drop(child);
            }
            drop(v); let scratch = [0u8;176];
        }",
    );
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

#[test]
fn optional_payloads_keep_occupied_slots_when_transferred() {
    let code = "fn take(v: &mut Vec<Option<Vec<u32>>>) -> (r: Option<Vec<u32>>)
        requires old(v).len() == 1,
        ensures r == old(v)[0], final(v).len() == 0,
        resources peak(memory) <= 34 { v.pop().unwrap() }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Option<Vec<u32>>>::with_capacity(1);
            let mut child = Vec::<u32>::with_capacity(1); child.push(7);
            let option = Some(child); v.push(option);
            let option = take(&mut v); let mut child = option.unwrap(); drop(v);
            child.push(9); let scratch = [0u8;160];
        }";
    verifies("optional_forest_geometry", &code.replace("BOUND", "200"));
    rejects(
        "optional_forest_geometry_short",
        &code.replace("BOUND", "199"),
        "memory budget exceeded",
    );
}
