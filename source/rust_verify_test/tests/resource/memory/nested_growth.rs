use super::support::{rejects, verifies};

#[test]
fn nested_growth_counts_enclosing_and_sibling_allocations() {
    let code = "struct P { v: Vec<u32>, sibling: Box<[u8;16]> }
        fn f() resources mem_peak <= BOUND {
            let mut p = Box::new(P { v: Vec::with_capacity(1), sibling: Box::new([0u8;16]) });
            p.v.push(1); p.v.push(2);
        }";
    // Box handle 8, payload 32, sibling 16, original buffer 4, replacement 16.
    verifies("nested_overlap", &code.replace("BOUND", "76"));
    rejects("nested_overlap_short", &code.replace("BOUND", "75"), "memory budget exceeded");
}

#[test]
fn boxed_vectors_grow_at_multiple_depths() {
    verifies(
        "boxed_growth",
        "struct P { v: Box<Box<Vec<u32>>> }
        fn f() resources mem_peak <= 64 {
            let mut p = P { v: Box::new(Box::new(Vec::new())) };
            p.v.push(1); p.v.push(2); p.v.push(3); p.v.push(4);
            assert(p.v.len() == 4);
            let q = p; drop(q); let scratch = [0u8;64];
        }",
    );
}

#[test]
fn leaf_helpers_update_only_the_selected_sibling() {
    let code = "struct P { a: Vec<u32>, b: Vec<u32> }
        fn append(v: &mut Vec<u32>) requires old(v).len() == 0,
            ensures final(v).len() == 1, resources mem_peak <= 24 { v.push(1); }
        fn f() resources mem_peak <= BOUND {
            let mut p = P { a: Vec::new(), b: Vec::with_capacity(10) };
            append(&mut p.a); let scratch = [0u8;32];
        }";
    verifies("nested_leaf_effect", &code.replace("BOUND", "144"));
    rejects("nested_leaf_effect_short", &code.replace("BOUND", "143"), "memory budget exceeded");
}

#[test]
fn composite_borrowed_helpers_preserve_child_effects() {
    let code = "struct P { v: Vec<u32> }
        fn append(p: &mut P) requires old(p).v.len() == 0,
            ensures final(p).v.len() == 1, resources mem_peak <= 24 { p.v.push(1); }
        fn relay(p: &mut P) requires old(p).v.len() == 0,
            ensures final(p).v.len() == 1, resources mem_peak <= 32 { append(p); }
        fn f() resources mem_peak <= BOUND {
            let mut p = P { v: Vec::new() }; relay(&mut p); let scratch = [0u8;32];
        }";
    verifies("nested_composite_effect", &code.replace("BOUND", "88"));
    rejects(
        "nested_composite_effect_short",
        &code.replace("BOUND", "87"),
        "memory budget exceeded",
    );
}

#[test]
fn returned_input_retains_descendant_changes() {
    let code = "struct P { v: Vec<u32> }
        fn append(mut p: P) -> (r: P) requires p.v.len() == 0,
            ensures r.v.len() == 1, resources mem_peak <= 40 { p.v.push(1); p }
        fn wrap(p: P) -> Box<P> requires p.v.len() == 0,
            resources mem_peak <= 80 { Box::new(append(p)) }
        fn f() resources mem_peak <= BOUND {
            let p = P { v: Vec::new() }; let q = wrap(p); let scratch = [0u8;80];
        }";
    verifies("nested_returned_effect", &code.replace("BOUND", "192"));
    rejects(
        "nested_returned_effect_short",
        &code.replace("BOUND", "191"),
        "memory budget exceeded",
    );
}

#[test]
fn nested_reservations_propagate_without_conflating_siblings() {
    let code = "struct P { a: Vec<u32>, b: Vec<u32> }
        fn append(p: &mut P) requires old(p).a.len() == 0,
            ensures final(p).a.len() == 1, resources mem_peak <= 8 { p.a.push(1); }
        fn relay(p: &mut P) requires old(p).a.len() == 0,
            ensures final(p).a.len() == 1, resources mem_peak <= 16 { append(p); }
        fn f() resources mem_peak <= 100 {
            let mut p = P { a: Vec::with_capacity(CAPACITY), b: Vec::with_capacity(4) };
            relay(&mut p);
        }";
    verifies("nested_reservation", &code.replace("CAPACITY", "1"));
    rejects("nested_wrong_sibling", &code.replace("CAPACITY", "0"), "vector capacity exceeded");
}

#[test]
fn nested_growth_has_inductive_loop_state() {
    verifies(
        "nested_loop",
        "struct P { v: Vec<u32> }
        fn f() resources mem_peak <= 120 {
            let mut p = P { v: Vec::new() };
            let mut i = 0usize;
            while i < 6 invariant i <= 6, p.v.len() == i, decreases 6 - i, {
                p.v.push(1); i += 1;
            }
            assert(p.v.len() == 6);
        }",
    );
}

#[test]
fn sections_protect_nested_allocations() {
    let code = "struct P { v: Vec<u32> }
        fn f() resources mem_peak <= 100 {
            let mut p = P { v: Vec::with_capacity(CAPACITY) };
            resources mem_peak <= 0 { p.v.push(1); }
        }";
    verifies("nested_section_reserved", &code.replace("CAPACITY", "1"));
    rejects("nested_section_growth", &code.replace("CAPACITY", "0"), "vector capacity exceeded");
}

#[test]
fn zero_sized_nested_elements_do_not_allocate() {
    verifies(
        "nested_zst",
        "struct P { v: Vec<[u8;0]> }
        fn f() resources mem_peak <= 32 {
            let mut p = Box::new(P { v: Vec::new() }); p.v.push([]); p.v.push([]);
        }",
    );
}

#[test]
fn nested_growth_example_verifies_and_compiles() {
    crate::verify_one_file(
        "nested_growth_example",
        include_str!("../../../../../examples/resource/memory/nested_growth.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn boxed_borrows_compose_relative_reservation_paths() {
    let code = "struct P { a: Vec<u32>, b: Vec<u32> }
        struct Outer { p: Box<P> }
        fn append(p: &mut Box<P>) requires old(p).b.len() == 0,
            ensures final(p).b.len() == 1, resources mem_peak <= 8 { p.b.push(1); }
        fn relay(o: &mut Outer) requires old(o).p.b.len() == 0,
            ensures final(o).p.b.len() == 1, resources mem_peak <= 16 { append(&mut o.p); }
        fn f() resources mem_peak <= 128 {
            let mut o = Outer { p: Box::new(P { a: Vec::with_capacity(4), b: Vec::with_capacity(CAPACITY) }) };
            relay(&mut o); assert(o.p.b.len() == 1);
        }";
    verifies("boxed_borrow_paths", &code.replace("CAPACITY", "1"));
    rejects("boxed_borrow_paths_short", &code.replace("CAPACITY", "0"), "vector capacity exceeded");
}

#[test]
fn unchanged_input_capacity_survives_nested_returns() {
    verifies(
        "nested_forward_capacity",
        "struct P { v: Vec<u32> }
        fn append(mut p: P) -> (r: P) requires p.v.len() == 0,
            ensures r.v.len() == 1, resources mem_peak <= 24 { p.v.push(1); p }
        fn f() resources mem_peak <= 40 {
            let p = P { v: Vec::with_capacity(4) };
            let mut q = append(p); q.v.push(2); q.v.push(3); q.v.push(4);
        }",
    );
}

#[test]
fn sibling_growth_effects_accumulate_across_helpers() {
    let code = "struct P { a: Vec<u32>, b: Vec<u32> }
        fn append(p: &mut P) requires old(p).a.len() == 0, old(p).b.len() == 0,
            ensures final(p).a.len() == 1, final(p).b.len() == 1,
            resources mem_peak <= 40 { p.a.push(1); p.b.push(2); }
        fn f() resources mem_peak <= BOUND {
            let mut p = P { a: Vec::new(), b: Vec::new() }; append(&mut p);
            let scratch = [0u8;40];
        }";
    // Each child retains the helper's conservative 40-byte upper bound.
    verifies("nested_two_effects", &code.replace("BOUND", "168"));
    rejects("nested_two_effects_short", &code.replace("BOUND", "167"), "memory budget exceeded");
}

#[test]
fn returned_input_does_not_shrink_original_allocation() {
    let code = "struct P { v: Vec<u32> }
        fn append(mut p: P) -> (r: P) requires p.v.len() == 0,
            ensures r.v.len() == 1, resources mem_peak <= 40 { p.v.push(1); p }
        fn f() resources mem_peak <= BOUND {
            let p = P { v: Vec::with_capacity(20) }; let q = append(p);
            let scratch = [0u8;40];
        }";
    verifies("nested_keep_original", &code.replace("BOUND", "144"));
    rejects("nested_keep_original_short", &code.replace("BOUND", "143"), "memory budget exceeded");
}

#[test]
fn small_composite_handle_cannot_hide_retained_growth() {
    let code = "struct P { v: Box<Vec<u32>> }
        fn append(mut p: P) -> P requires p.v.len() == 0,
            resources mem_peak <= 24 { p.v.push(1); p }
        fn f() resources mem_peak <= BOUND {
            let p = P { v: Box::new(Vec::new()) }; let q = append(p);
            let scratch = [0u8;32];
        }";
    // The parameter's inline handle is 8, so a 16-byte replacement fits its
    // 24-byte budget and must remain charged when the composite is returned.
    verifies("small_composite_growth", &code.replace("BOUND", "88"));
    rejects("small_composite_growth_short", &code.replace("BOUND", "87"), "memory budget exceeded");
}

#[test]
fn nested_helper_effects_have_inductive_loop_state() {
    verifies(
        "nested_helper_loop",
        "struct P { v: Vec<u32> }
        fn append(p: &mut P) requires old(p).v.len() < 6,
            ensures final(p).v.len() == old(p).v.len() + 1, resources mem_peak <= 56 { p.v.push(1); }
        fn f() resources mem_peak <= 160 {
            let mut p = P { v: Vec::new() }; let mut i = 0usize;
            while i < 6 invariant i <= 6, p.v.len() == i, decreases 6-i, {
                append(&mut p); i += 1;
            }
        }",
    );
}

#[test]
fn helper_cannot_hide_nested_growth_in_section() {
    rejects(
        "nested_helper_section",
        "struct P { v: Vec<u32> }
        fn append(p: &mut P) requires old(p).v.len() == 0,
            resources mem_peak <= 24 { p.v.push(1); }
        fn f() resources mem_peak <= 100 {
            let mut p = P { v: Vec::new() }; resources mem_peak <= 24 { append(&mut p); }
        }",
        "growing an enclosing vector through a helper inside a memory section",
    );
}

#[test]
fn aliases_and_mutating_push_arguments_remain_rejected() {
    rejects(
        "nested_alias",
        "struct P { v: Vec<u32> }
        fn f() resources mem_peak <= 100 { let mut p = P { v: Vec::new() }; let v = &mut p.v; v.push(1); }",
        "aliased owner",
    );
    rejects(
        "nested_push_argument",
        "struct P { a: Vec<u32>, b: Vec<u32> }
        fn append(v: &mut Vec<u32>) -> u32 requires old(v).len() == 0,
            resources mem_peak <= 28 { v.push(1); 0 }
        fn f() resources mem_peak <= 200 {
            let mut p = P { a: Vec::new(), b: Vec::new() }; p.a.push(append(&mut p.b));
        }",
        "bind the argument first",
    );
}
