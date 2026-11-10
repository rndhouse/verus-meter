//! Resource regressions exercise footprint transfer across runtime indices,
//! extraction, fixed children, and repeated operations.

use super::support::{rejects, verifies};

#[test]
fn selected_child_recovers_its_reservation() {
    let code = "fn f(i: usize) requires i < 2, resources peak(memory) <= BOUND {
        let mut outer = Vec::<Vec<u32>>::with_capacity(2);
        let a = Vec::<u32>::with_capacity(4); outer.push(a);
        let b = Vec::<u32>::with_capacity(4); outer.push(b);
        outer[i].push(7); let scratch = [0u8;32];
    }";
    verifies("element_capacity", &code.replace("BOUND", "144"));
    rejects("element_capacity_short", &code.replace("BOUND", "143"), "memory budget exceeded");
}

#[test]
fn popped_owner_outlives_its_container() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
        let b = Box::new([0u8;32]); v.push(b);
        let removed = v.pop().unwrap(); drop(v);
        let scratch = [0u8;64]; drop(removed);
    }";
    verifies("element_lifetime", &code.replace("BOUND", "104"));
    rejects("element_lifetime_short", &code.replace("BOUND", "103"), "memory budget exceeded");
}

#[test]
fn replacing_a_child_releases_the_displaced_footprint() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(1);
        let a = Box::new([0u8;16]); v.push(a);
        let b = Box::new([0u8;16]); v[0] = b;
        let scratch = [0u8;64];
    }";
    verifies("element_replace", &code.replace("BOUND", "112"));
    rejects("element_replace_short", &code.replace("BOUND", "111"), "memory budget exceeded");
}

#[test]
fn extraction_loop_reuses_child_storage() {
    verifies(
        "element_pop_loop",
        "fn f() resources peak(memory) <= 160 {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(2);
        let a = Box::new([0u8;16]); v.push(a);
        let b = Box::new([0u8;16]); v.push(b);
        while v.len() > 0 invariant v.len() <= 2, decreases v.len(), {
            let child = v.pop().unwrap();
            let scratch = [0u8;64]; drop(child);
        }
        drop(v); let scratch = [0u8;160];
    }",
    );
}

#[test]
fn matching_an_extracted_owner_transfers_the_payload() {
    verifies(
        "element_pop_match",
        "fn f() resources peak(memory) <= 160 {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(1);
        let a = Box::new([0u8;16]); v.push(a);
        match v.pop() { Some(child) => { drop(child); }, None => {} }
        let next = Box::new([0u8;16]); v.push(next);
        drop(v); let scratch = [0u8;160];
    }",
    );
}

#[test]
fn opaque_borrowed_extraction_keeps_the_result_charged() {
    // The unreachable removal loop exercises aggregate fallback today. The
    // assertions must also hold if inference later recognizes this helper.
    let code = "fn take(v: &mut Vec<Box<[u8;32]>>) -> (r: Option<Box<[u8;32]>>)
        requires old(v).len() == 1, ensures r.is_some(), resources peak(memory) <= 17 {
            while v.len() > 1 invariant v.len() >= 1, decreases v.len(), { v.remove(0); }
            v.pop()
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
            let b = Box::new([0u8;32]); v.push(b);
            let child = take(&mut v).unwrap(); drop(v);
            let scratch = [0u8;200]; drop(child);
        }";
    verifies("borrowed_extraction", &code.replace("BOUND", "320"));
    // The result still owns a handle (8) and payload (32) beside scratch (200).
    rejects("borrowed_extraction_live", &code.replace("BOUND", "239"), "memory budget exceeded");
}

#[test]
fn opaque_owned_extraction_transfers_input_dependencies() {
    let code = "fn take(mut v: Vec<Box<[u8;32]>>) -> (r: Box<[u8;32]>)
        requires v.len() == 1, resources peak(memory) <= 40 {
            while v.len() > 1 invariant v.len() >= 1, decreases v.len(), { v.remove(0); }
            v.pop().unwrap()
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
            let b = Box::new([0u8;32]); v.push(b);
            let child = take(v); let scratch = [0u8;200]; drop(child);
        }";
    verifies("owned_extraction", &code.replace("BOUND", "320"));
    // Require the real result storage, without fixing the fallback's overcharge.
    rejects("owned_extraction_live", &code.replace("BOUND", "239"), "memory budget exceeded");
}

#[test]
fn removing_reindexes_surviving_element_metadata() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Vec<u32>>::with_capacity(2);
        let a = Vec::<u32>::with_capacity(1); v.push(a);
        let b = Vec::<u32>::with_capacity(2); v.push(b);
        let removed = v.remove(0);
        AFTER_REMOVAL
    }";
    for (name, after, peak) in [
        // Dropping the extracted owner isolates the survivor's charge and
        // reservation: its second push must fit the original two-element buffer.
        (
            "element_remove_survivor",
            "drop(removed); let scratch = [0u8;64];
                v[0].push(1); v[0].push(2);",
            144,
        ),
        ("element_remove_result", "drop(v); let scratch = [0u8;160]; drop(removed);", 188),
    ] {
        let code = code.replace("AFTER_REMOVAL", after);
        verifies(name, &code.replace("BOUND", &format!("{peak}")));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &format!("{short}", short = peak - 1)),
            "memory budget exceeded",
        );
    }
}

#[test]
fn index_metadata_cannot_precede_effectful_arguments() {
    rejects(
        "element_index_effect",
        "fn replace(n: u32, v: &mut Vec<u32>) resources peak(memory) <= 12 { }
        fn f() resources peak(memory) <= 200 {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(4); v.push(b);
            let mut i = 0usize;
            replace({ i = 1; 7 }, &mut v[i]);
        }",
        "bind the arguments first",
    );
}

#[test]
fn indexed_loop_reuses_each_child_reservation() {
    verifies(
        "reserved_element_loop",
        "fn f() resources peak(memory) <= 160 {
        let mut v = Vec::<Vec<u32>>::with_capacity(2);
        let a = Vec::<u32>::with_capacity(4); v.push(a);
        let b = Vec::<u32>::with_capacity(4); v.push(b);
        let mut i = 0usize;
        while i < v.len()
            invariant i <= 2, v.len() == 2,
                forall|j: int| 0 <= j < 2 ==> v[j].len() == if j < i { 1usize } else { 0usize },
            decreases 2-i,
        { v[i].push(7); i += 1; }
        drop(v); let scratch = [0u8;152];
    }",
    );
}

#[test]
fn reservation_paths_cover_fixed_and_repeated_owners() {
    verifies(
        "nested_reserved_loop",
        "fn f() resources peak(memory) <= 200 {
        let mut v = Vec::<Vec<Box<Vec<u32>>>>::with_capacity(1);
        let mut middle = Vec::<Box<Vec<u32>>>::with_capacity(2);
        let a = Box::new(Vec::<u32>::with_capacity(4)); middle.push(a);
        let b = Box::new(Vec::<u32>::with_capacity(4)); middle.push(b);
        v.push(middle);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, v.len() == 1, v[0].len() == 2,
                forall|j: int| 0 <= j < 2 ==> #[trigger] v[0][j].len() == if j < i { 1usize } else { 0usize },
            decreases 2-i,
        { v[0][i].push(7); i += 1; }
        drop(v); let scratch = [0u8;192];
    }",
    );
}

#[test]
fn a_fill_loop_and_a_drain_loop_share_the_same_footprints() {
    verifies(
        "fill_and_drain",
        "fn f() resources peak(memory) <= 160 {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(2);
        let mut i = 0usize;
        while i < 2 invariant i <= 2, v.len() == i, decreases 2-i, {
            let child = Box::new([0u8;16]); v.push(child); i += 1;
        }
        while v.len() > 0 invariant v.len() <= 2, decreases v.len(), {
            let child = v.pop().unwrap(); let scratch = [0u8;64]; drop(child);
        }
        drop(v); let scratch = [0u8;152];
    }",
    );
}

#[test]
fn opaque_dependencies_survive_branches_and_reinsertion() {
    let code = "fn take(v: &mut Vec<Box<[u8;32]>>) -> (r: Option<Box<[u8;32]>>)
        requires old(v).len() == 1, ensures r.is_some(), resources peak(memory) <= 17 {
            while v.len() > 1 invariant v.len() >= 1, decreases v.len(), { v.remove(0); }
            v.pop()
        }
        fn relay(flag: bool, v: &mut Vec<Box<[u8;32]>>) -> Box<[u8;32]>
            requires flag, old(v).len() == 1, resources peak(memory) <= 96 {
            let mut stash = Vec::<Box<[u8;32]>>::with_capacity(1);
            if flag { let child = take(v).unwrap(); stash.push(child); }
            let child = stash.pop().unwrap(); drop(stash); child
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
            let b = Box::new([0u8;32]); v.push(b);
            let child = relay(true, &mut v); drop(v);
            let scratch = [0u8;280]; drop(child);
        }";
    verifies("captured_reinsertion", &code.replace("BOUND", "512"));
    // Even exact inference needs the result's 40 bytes beside scratch (280).
    rejects("captured_reinsertion_live", &code.replace("BOUND", "319"), "memory budget exceeded");
}

#[test]
fn boxed_slice_children_use_the_same_reservation_classes() {
    verifies(
        "slice_reserved_loop",
        "fn f() resources peak(memory) <= 200 {
        let mut v = Vec::<Box<Vec<u32>>>::with_capacity(2);
        let a = Box::new(Vec::<u32>::with_capacity(4)); v.push(a);
        let b = Box::new(Vec::<u32>::with_capacity(4)); v.push(b);
        let mut slice = v.into_boxed_slice();
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, slice.len() == 2,
                forall|j: int| 0 <= j < 2 ==> slice[j].len() == if j < i { 1usize } else { 0usize },
            decreases 2-i,
        { slice[i].push(7); i += 1; }
        drop(slice); let scratch = [0u8;192];
    }",
    );
}

#[test]
fn implicit_box_dereferences_keep_the_allocation_around_a_growing_child() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<Vec<u32>>>::with_capacity(1);
        let child = Box::new(Vec::<u32>::with_capacity(1)); v.push(child);
        v[0].push(1); v[0].push(2);
        let scratch = [0u8;64];
    }";
    verifies("boxed_element_growth", &code.replace("BOUND", "136"));
    rejects("boxed_element_growth_short", &code.replace("BOUND", "135"), "memory budget exceeded");
}

#[test]
fn reservation_classes_follow_owning_struct_fields_in_loops() {
    verifies("field_reserved_loop", "struct Child { data: Vec<u32> }
        fn f() resources peak(memory) <= 200 {
            let mut v = Vec::<Child>::with_capacity(2);
            let a = Child { data: Vec::<u32>::with_capacity(4) }; v.push(a);
            let b = Child { data: Vec::<u32>::with_capacity(4) }; v.push(b);
            let mut i = 0usize;
            while i < 2
                invariant i <= 2, v.len() == 2,
                    forall|j: int| 0 <= j < 2 ==> v[j].data.len() == if j < i { 1usize } else { 0usize },
                decreases 2-i,
            { v[i].data.push(7); i += 1; }
        }");
}

#[test]
fn removal_loops_and_empty_pop_keep_ownership_balanced() {
    verifies(
        "remove_loop",
        "fn f() resources peak(memory) <= 160 {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(2);
        let a = Box::new([0u8;16]); v.push(a);
        let b = Box::new([0u8;16]); v.push(b);
        while v.len() > 0 invariant v.len() <= 2, decreases v.len(), {
            let child = v.remove(0); let scratch = [0u8;64]; drop(child);
        }
        let empty = v.pop(); assert(empty.is_none()); drop(empty);
        drop(v); let scratch = [0u8;160];
    }",
    );
}
