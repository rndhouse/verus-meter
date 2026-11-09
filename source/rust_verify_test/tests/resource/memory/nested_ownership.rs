use super::support::{exact_peak, rejects, verifies};

#[test]
fn fixed_children_count_inline_storage_once() {
    exact_peak(
        "nested_boxes",
        "fn f() mem_peak <= BUDGET {
        let b = Box::new(Box::new(7u32));
    }",
        20,
    );
    exact_peak("owning_fields", "struct Pair { flag: bool, a: Box<[u8;16]>, b: Box<u32> }
        fn f() mem_peak <= BUDGET { let p = Pair { flag: true, a: Box::new([0u8;16]), b: Box::new(7) }; }", 37);
}

#[test]
fn boxed_vector_retains_its_handle_and_backing_allocation() {
    let code = "fn f() mem_peak <= BOUND {
        let b = Box::new(Vec::<u32>::with_capacity(4));
        assert(b.len() == 0);
        let scratch = [0u8;32];
    }";
    verifies("boxed_vector", &code.replace("BOUND", "80"));
    rejects("boxed_vector_short", &code.replace("BOUND", "79"), "memory budget exceeded");
}

#[test]
fn nested_drop_releases_every_child() {
    verifies("nested_drop", "struct Inner { data: Vec<u32>, other: Box<[u8;16]> }
        struct Outer { inner: Box<Inner> }
        fn f() mem_peak <= 120 {
            let p = Outer { inner: Box::new(Inner { data: Vec::with_capacity(4), other: Box::new([0u8;16]) }) };
            let q = p; drop(q);
            let scratch = [0u8;120];
        }");
}

#[test]
fn factories_and_forwarding_preserve_recursive_extents() {
    let code = "struct Pair { a: Box<[u8;16]>, b: Vec<u32> }
        fn make(n: usize) -> Pair requires n <= 4, mem_peak <= 56 + 4*n {
            Pair { a: Box::new([0u8;16]), b: Vec::with_capacity(n) }
        }
        fn forward(p: Pair) -> Pair mem_peak <= 32 { p }
        fn f() mem_peak <= BOUND {
            let p = make(2); let q = forward(p); let r = make(2);
        }";
    verifies("nested_factory", &code.replace("BOUND", "120"));
    rejects("nested_factory_short", &code.replace("BOUND", "119"), "memory budget exceeded");
}

#[test]
fn sibling_runtime_allocations_have_distinct_identities() {
    let code = "struct Buffers { a: Vec<u8>, b: Vec<u16> }
        fn make(n: usize) -> Buffers requires n <= 4, mem_peak <= 56 + 3*n {
            Buffers { a: Vec::with_capacity(n), b: Vec::with_capacity(n) }
        }
        fn f(n: usize) requires n <= 4, mem_peak <= BOUND + 3*n {
            let p = make(n); let scratch = [0u8;47];
        }";
    verifies("nested_dynamic", &code.replace("BOUND", "103"));
    rejects("nested_dynamic_short", &code.replace("BOUND", "102"), "memory budget exceeded");
}

#[test]
fn helpers_can_wrap_inputs_under_new_allocations() {
    verifies(
        "nested_wrap",
        "struct Pair { a: Box<[u8;16]>, b: Vec<u32> }
        fn wrap(a: Box<[u8;16]>, b: Vec<u32>) -> Box<Pair> mem_peak <= 72 {
            Box::new(Pair { a, b })
        }
        fn forward(p: Box<Pair>) -> Box<Pair> mem_peak <= 8 { p }
        fn consume(p: Box<Pair>) mem_peak <= 8 { }
        fn f() mem_peak <= 160 {
            let a = Box::new([0u8;16]); let b = Vec::<u32>::with_capacity(4);
            let p = wrap(a,b); let q = forward(p); consume(q);
            let scratch = [0u8;160];
        }",
    );
}

#[test]
fn forwarded_composite_input_remains_live_during_helper_work() {
    let code = "struct Pair { a: Box<[u8;16]>, b: Box<[u8;32]> }
        fn inspect(p: Pair) -> Pair mem_peak <= 48 { let scratch = [0u8;32]; p }
        fn f() mem_peak <= BOUND {
            let p = Pair { a: Box::new([0u8;16]), b: Box::new([0u8;32]) };
            let q = inspect(p);
        }";
    verifies("nested_input_live", &code.replace("BOUND", "96"));
    rejects("nested_input_live_short", &code.replace("BOUND", "95"), "memory budget exceeded");
}

#[test]
fn consuming_composite_input_ends_child_lifetimes_in_callee() {
    verifies(
        "nested_input_drop",
        "struct Pair { a: Box<[u8;16]>, b: Box<[u8;32]> }
        fn consume(p: Pair) mem_peak <= 80 { drop(p); let scratch = [0u8;80]; }
        fn f() mem_peak <= 80 {
            let p = Pair { a: Box::new([0u8;16]), b: Box::new([0u8;32]) };
            consume(p);
        }",
    );
}

#[test]
fn nested_contents_can_be_borrowed_and_updated() {
    verifies(
        "nested_borrow",
        "struct Data { number: Box<u32>, vector: Vec<u32> }
        fn update(x: &mut u32) ensures *final(x) == 9, mem_peak <= 8 { *x = 9; }
        fn f() mem_peak <= 160 {
            let mut v = Vec::<u32>::with_capacity(2); v.push(1);
            let mut p = Data { number: Box::new(7), vector: v };
            update(&mut *p.number);
            assert(*p.number == 9);
            let n = p.vector.len();
            let s = p.vector.as_mut_slice(); s[0] = 2;
            assert(p.vector[0] == 2);
        }",
    );
}

#[test]
fn boxes_and_structs_compose_at_more_than_one_level() {
    verifies(
        "nested_depth",
        "struct A { data: Box<Vec<u8>> }
        struct B { a: Box<A>, flag: bool }
        fn make() -> Box<B> mem_peak <= 100 {
            Box::new(B { a: Box::new(A { data: Box::new(Vec::with_capacity(4)) }), flag: true })
        }
        fn f() mem_peak <= 160 { let b = make(); drop(b); let scratch = [0u8;160]; }",
    );
}

#[test]
fn recursive_layout_is_rejected_without_recursing_forever() {
    rejects(
        "recursive_ownership",
        "struct Node { next: Box<Node> }
        fn f(n: Node) mem_peak <= 100 {}",
        "recursive struct layouts",
    );
}

#[test]
fn sibling_boxed_slice_summaries_keep_independent_dynamic_charges() {
    let code = "struct Pair { a: Box<[u8]>, b: Box<[u8]> }
        fn slice(n: usize) -> Box<[u8]> requires n <= 4, mem_peak <= 48 + n {
            let v = Vec::<u8>::with_capacity(n); v.into_boxed_slice()
        }
        fn make(n: usize) -> Pair requires n <= 4, mem_peak <= 200 + 2*n {
            Pair { a: slice(n), b: slice(n) }
        }
        fn f(n: usize) requires n <= 4, mem_peak <= BOUND + 2*n {
            let p = make(n); let scratch = [0u8;100];
        }";
    verifies("nested_slices", &code.replace("BOUND", "236"));
    rejects("nested_slices_short", &code.replace("BOUND", "235"), "memory budget exceeded");
}

#[test]
fn regrouped_input_provenance_survives_another_call() {
    let code = "struct Pair { a: Box<[u8;16]>, b: Box<[u8;32]> }
        fn inspect(p: Pair) -> Pair mem_peak <= 48 { let scratch = [0u8;32]; p }
        fn group(a: Box<[u8;16]>, b: Box<[u8;32]>) -> Pair mem_peak <= 64 {
            let p = Pair { a, b }; inspect(p)
        }
        fn f() mem_peak <= BOUND {
            let a = Box::new([0u8;16]); let b = Box::new([0u8;32]);
            let p = group(a, b);
        }";
    verifies("nested_regroup", &code.replace("BOUND", "96"));
    rejects("nested_regroup_short", &code.replace("BOUND", "95"), "memory budget exceeded");
}

#[test]
fn owned_children_remain_live_during_later_initializers() {
    let code = "struct Pair { a: Box<[u8;16]>, b: Box<u8> }
        fn later() -> Box<u8> mem_peak <= 72 { let scratch = [0u8;63]; Box::new(1) }
        fn f() mem_peak <= BOUND { let p = Pair { a: Box::new([0u8;16]), b: later() }; }";
    verifies("nested_initializer_order", &code.replace("BOUND", "96"));
    rejects(
        "nested_initializer_order_short",
        &code.replace("BOUND", "95"),
        "memory budget exceeded",
    );
}

#[test]
fn nested_regions_release_local_trees_and_protect_enclosing_trees() {
    verifies(
        "nested_regions",
        "struct P { b: Box<Vec<u32>> }
        fn f(flag: bool) mem_peak <= 200 {
            if flag { let p = P { b: Box::new(Vec::with_capacity(4)) }; }
            mem_peak <= 80 { let p = P { b: Box::new(Vec::with_capacity(4)) }; }
            let scratch = [0u8;199];
        }",
    );
    rejects(
        "nested_protected",
        "struct P { b: Box<u32> }
        fn f(flag: bool) mem_peak <= 100 { let p = P { b: Box::new(1) }; if flag { drop(p); } }",
        "moving or dropping an enclosing heap owner",
    );
}

#[test]
fn borrowed_structs_and_multiple_box_dereferences_preserve_owners() {
    verifies(
        "nested_projection",
        "struct P { b: Box<u32>, v: Vec<u8> }
        fn inspect(p: &P) mem_peak <= 16 { let n = p.v.len(); }
        fn f() mem_peak <= 120 {
            let p = P { b: Box::new(1), v: Vec::with_capacity(4) }; inspect(&p);
            let b = Box::new(Box::new(p)); let n = b.v.len(); let x = *b.b;
            assert(x == 1);
        }",
    );
}

#[test]
fn nested_ownership_example_verifies_and_compiles() {
    crate::verify_one_file(
        "nested_ownership",
        include_str!("../../../../../examples/resource/memory/nested_ownership.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn popping_a_nested_vector_preserves_its_backing_charge() {
    let code = "fn f() mem_peak <= BOUND {
        let mut v = Vec::<u32>::with_capacity(1); v.push(7);
        let mut b = Box::new(v);
        let value = b.pop(); assert(value == Some(7)); assert(b.len() == 0);
        let scratch = [0u8;40];
    }";
    verifies("nested_pop", &code.replace("BOUND", "81"));
    rejects("nested_pop_short", &code.replace("BOUND", "80"), "memory budget exceeded");
}

#[test]
fn replacement_effects_follow_vectors_into_new_parent_owners() {
    verifies(
        "nested_grown_input",
        "fn wrap(mut v: Vec<u8>) -> (b: Box<Vec<u8>>)
            requires v.len() == 0, ensures b.len() == 1, b[0] == 7, mem_peak <= 100 {
            v.push(7); Box::new(v)
        }
        fn f() mem_peak <= 200 {
            let v = Vec::<u8>::new(); let b = wrap(v);
            assert(b[0] == 7); drop(b);
            let scratch = [0u8;200];
        }",
    );
}
