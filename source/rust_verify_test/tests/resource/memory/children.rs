use super::support::{exact_peak, verifies};

#[test]
fn field_extraction_preserves_siblings_and_releases_the_child() {
    exact_peak(
        "extract_field",
        "struct P { a: Box<[u8;16]>, b: Box<[u8;32]> }
        fn f() resources mem_peak <= BUDGET {
            let p = P { a: Box::new([0u8;16]), b: Box::new([0u8;32]) };
            let a = p.a; drop(a); let scratch = [0u8;32];
        }",
        80,
    );
}

#[test]
fn replacement_overlaps_old_and_new_allocations() {
    exact_peak(
        "replace_field",
        "struct P { a: Box<[u8;16]> }
        fn f() resources mem_peak <= BUDGET {
            let mut p = P { a: Box::new([0u8;16]) }; p.a = Box::new([0u8;16]);
        }",
        40,
    );
}

#[test]
fn boxed_contents_transfer_and_replace() {
    exact_peak(
        "extract_box",
        "fn f() resources mem_peak <= BUDGET {
        let p = Box::new(Box::new([0u8;16])); let a = *p; drop(a); let scratch = [0u8;24];
    }",
        40,
    );
    exact_peak(
        "replace_box",
        "fn f() resources mem_peak <= BUDGET {
        let mut p = Box::new(Box::new([0u8;16])); *p = Box::new([0u8;16]);
    }",
        48,
    );
}

#[test]
fn extracted_field_can_be_reinitialized_and_forwarded() {
    verifies(
        "refill_field",
        "struct P { a: Box<u32>, b: Vec<u32> }
        fn refill(mut p: P) -> P resources mem_peak <= 100 {
            let a = p.a; drop(a); p.a = Box::new(2); p
        }
        fn f() resources mem_peak <= 200 {
            let p = P { a: Box::new(1), b: Vec::with_capacity(4) };
            let q = refill(p); drop(q); let scratch = [0u8;200];
        }",
    );
}

#[test]
fn returned_child_does_not_retain_its_siblings() {
    exact_peak(
        "return_field",
        "struct P { a: Box<[u8;16]>, b: Box<[u8;32]> }
        fn take(p: P) -> Box<[u8;16]> resources mem_peak <= 24 { p.a }
        fn f() resources mem_peak <= BUDGET {
            let p = P { a: Box::new([0u8;16]), b: Box::new([0u8;32]) };
            let a = take(p); let scratch = [0u8;64];
        }",
        88,
    );
}

#[test]
fn borrowed_child_replacements_propagate_through_helpers() {
    exact_peak(
        "borrowed_replace",
        "struct P { a: Box<[u8;16]> }
        fn replace(p: &mut P) resources mem_peak <= 24 { p.a = Box::new([0u8;16]); }
        fn relay(p: &mut P) resources mem_peak <= 32 { replace(p); }
        fn f() resources mem_peak <= BUDGET {
            let mut p = P { a: Box::new([0u8;16]) }; relay(&mut p);
            let scratch = [0u8;64];
        }",
        88,
    );
}

#[test]
fn replaced_child_can_capture_an_input_tree() {
    verifies(
        "borrowed_capture",
        "struct P { a: Box<Vec<u32>> }
        fn replace(p: &mut P, a: Box<Vec<u32>>) ensures final(p).a == a, resources mem_peak <= 16 { p.a = a; }
        fn f() resources mem_peak <= 200 {
            let mut p = P { a: Box::new(Vec::with_capacity(4)) };
            let a = Box::new(Vec::with_capacity(8)); replace(&mut p, a);
            p.a.push(1); drop(p); let scratch = [0u8;200];
        }",
    );
}

#[test]
fn extracted_collection_keeps_child_sums_and_capacity() {
    verifies(
        "extract_collection",
        "struct P { a: Vec<Box<[u8;16]>>, b: Box<u32> }
        fn take(p: P) -> (v: Vec<Box<[u8;16]>>) ensures v == p.a, resources mem_peak <= 56 { p.a }
        fn f() resources mem_peak <= 200 {
            let mut v = Vec::with_capacity(2); let a = Box::new([0u8;16]); v.push(a);
            let p = P { a: v, b: Box::new(1) }; let mut v = take(p);
            let b = Box::new([0u8;16]); v.push(b); drop(v); let scratch = [0u8;200];
        }",
    );
}

#[test]
fn sibling_moves_and_repeated_replacements_compose() {
    verifies(
        "sibling_transfer",
        "struct P { a: Box<u32>, b: Box<u32> }
        fn exchange(p: P) -> (q: P) ensures q.a == p.b, q.b == p.a, resources mem_peak <= 40 {
            let mut q = p; let a = q.a; q.a = q.b; q.b = a; q
        }
        fn f() resources mem_peak <= 100 {
            let p = P { a: Box::new(1), b: Box::new(2) }; let q = exchange(p);
            assert(*q.a == 2 && *q.b == 1); drop(q); let scratch = [0u8;100];
        }",
    );
}

#[test]
fn moving_a_field_directly_into_another_owner_needs_no_new_handle() {
    exact_peak(
        "field_into_owner",
        "struct P { a: Box<[u8;16]> }
        fn f() resources mem_peak <= BUDGET {
            let p = P { a: Box::new([0u8;16]) }; let q = P { a: p.a };
        }",
        32,
    );
}

#[test]
fn replacing_parent_after_child_exports_only_final_ownership() {
    verifies(
        "replace_parent",
        "struct P { a: Box<[u8;16]> }
        struct W { p: Box<P> }
        fn replace(w: &mut W) resources mem_peak <= 80 {
            w.p.a = Box::new([0u8;16]); w.p = Box::new(P { a: Box::new([0u8;16]) });
        }
        fn f() resources mem_peak <= 200 {
            let mut w = W { p: Box::new(P { a: Box::new([0u8;16]) }) };
            replace(&mut w); drop(w); let scratch = [0u8;200];
        }",
    );
}

#[test]
fn nested_child_paths_and_explicit_drop_preserve_siblings() {
    exact_peak(
        "nested_child_drop",
        "struct P { a: Box<[u8;16]>, b: Box<[u8;32]> }
        fn f() resources mem_peak <= BUDGET {
            let p = Box::new(P { a: Box::new([0u8;16]), b: Box::new([0u8;32]) });
            drop(p.a); let scratch = [0u8;32];
        }",
        88,
    );
}

#[test]
fn replacing_a_child_with_an_existing_owner_transfers_once() {
    exact_peak(
        "replace_existing",
        "struct P { a: Box<[u8;16]> }
        fn f() resources mem_peak <= BUDGET {
            let mut p = P { a: Box::new([0u8;16]) }; let b = Box::new([0u8;16]); p.a = b;
            let scratch = [0u8;32];
        }",
        56,
    );
}

#[test]
fn region_boundaries_cannot_hide_child_transfers() {
    use super::support::rejects;
    rejects(
        "branch_child",
        "struct P { a: Box<u32> }
        fn f(flag: bool) resources mem_peak <= 100 {
            let mut p = P { a: Box::new(1) }; if flag { p.a = Box::new(2); }
        }",
        "enclosing heap owner",
    );
    rejects(
        "section_child",
        "struct P { a: Box<u32> }
        fn f() resources mem_peak <= 100 {
            let p = P { a: Box::new(1) }; resources mem_peak <= 20 { drop(p.a); }
        }",
        "enclosing heap owner",
    );
    rejects(
        "borrowed_branch_child",
        "struct P { a: Box<u32> }
        fn f(p: &mut P, flag: bool) resources mem_peak <= 100 {
            if flag { p.a = Box::new(2); }
        }",
        "enclosing heap owner",
    );
}

#[test]
fn child_transfers_example_verifies_and_compiles() {
    crate::verify_one_file(
        "child_transfers_example",
        include_str!("../../../../../examples/resource/memory/child_transfers.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn input_child_lifetimes_are_independent_inside_calls() {
    exact_peak(
        "independent_input_lifetimes",
        "struct P { a: Box<[u8;80]>, b: Box<[u8;16]> }
        fn consume(p: P) resources mem_peak <= 176 { drop(p.a); let scratch = [0u8;160]; }
        fn f() resources mem_peak <= BUDGET {
            let p = P { a: Box::new([0u8;80]), b: Box::new([0u8;16]) }; consume(p);
        }",
        192,
    );
}

#[test]
fn returning_box_contents_releases_the_enclosing_allocation() {
    exact_peak(
        "return_box_contents",
        "fn take(b: Box<Box<[u8;16]>>) -> Box<[u8;16]>
        resources mem_peak <= 16 { *b }
        fn f() resources mem_peak <= BUDGET {
            let b = Box::new(Box::new([0u8;16])); let a = take(b); let scratch = [0u8;64];
        }",
        88,
    );
}

#[test]
fn implicit_box_reads_keep_the_selected_type_in_every_destination() {
    verifies(
        "implicit_child_reads",
        "struct P { a: Box<u32> }
        fn forward(a: Box<u32>) -> (b: Box<u32>) ensures b == a, resources mem_peak <= 8 { a }
        fn f() resources mem_peak <= 256 {
            {
                let b = Box::new(Box::new(1u32)); let a = forward(*b);
                let c = Box::new(Box::new(2u32)); let mut p = P { a: *c };
                let d = Box::new(Box::new(3u32)); p.a = *d;
                let e = Box::new(Box::new(4u32)); let wrapped = Box::new(*e);
                assert(*a == 1 && *p.a == 3 && **wrapped == 4);
            }
            let scratch = [0u8;256];
        }",
    );
}
