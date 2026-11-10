use super::support::{rejects, verifies};

#[test]
fn insertion_transfers_child_storage_once() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(2);
        let a = Box::new([0u8;16]); v.push(a);
        let b = Box::new([0u8;16]); v.push(b);
        assert(v.len() == 2);
        let scratch = [0u8;20];
    }";
    verifies("element_transfer", &code.replace("BOUND", "92"));
    rejects("element_transfer_short", &code.replace("BOUND", "91"), "memory budget exceeded");
}

#[test]
fn outer_growth_replaces_handles_not_child_allocations() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(1);
        let a = Box::new([0u8;16]); v.push(a);
        let b = Box::new([0u8;16]); v.push(b);
    }";
    // 24-byte vector handle, old 8-byte buffer, replacement 32-byte buffer,
    // and 32 bytes owned by the two elements.
    verifies("element_overlap", &code.replace("BOUND", "96"));
    rejects("element_overlap_short", &code.replace("BOUND", "95"), "memory budget exceeded");
}

#[test]
fn runtime_count_uses_inductive_child_sums() {
    verifies(
        "element_loop",
        "fn f(n: usize) requires n <= 4,
        resources peak(memory) <= 48 + 24*n {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(n);
        let mut i = 0usize;
        while i < n invariant i <= n, v.len() == i, decreases n-i, {
            let child = Box::new([0u8;16]); v.push(child); i += 1;
        }
    }",
    );
}

#[test]
fn runtime_count_accepts_owning_sequence_elements() {
    verifies(
        "nested_sequence_loop",
        "fn f(n: usize) requires n <= 4,
        resources peak(memory) <= 64 + 36*n {
        let mut v = Vec::<Vec<u32>>::with_capacity(n);
        let mut i = 0usize;
        while i < n invariant i <= n, v.len() == i, decreases n-i, {
            let child = Vec::<u32>::with_capacity(3); v.push(child); i += 1;
        }
    }",
    );
}

#[test]
fn arbitrary_fixed_and_runtime_children_compose() {
    verifies(
        "element_composition",
        "struct Element { a: Box<[u8;16]>, b: Vec<u32> }
        struct Container { data: Box<Vec<Element>> }
        fn f() resources peak(memory) <= 256 {
            let mut p = Container { data: Box::new(Vec::with_capacity(2)) };
            let a = Element { a: Box::new([0u8;16]), b: Vec::with_capacity(4) }; p.data.push(a);
            let b = Element { a: Box::new([0u8;16]), b: Vec::with_capacity(1) }; p.data.push(b);
            let moved = p; drop(moved); let scratch = [0u8;256];
        }",
    );
}

#[test]
fn deeper_collections_transfer_their_complete_footprint() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut inner = Vec::<Box<[u8;16]>>::with_capacity(1);
        let item = Box::new([0u8;16]); inner.push(item);
        let mut middle = Vec::<Vec<Box<[u8;16]>>>::with_capacity(1); middle.push(inner);
        let mut outer = Vec::<Box<Vec<Vec<Box<[u8;16]>>>>>::with_capacity(1);
        let boxed = Box::new(middle); outer.push(boxed);
        let scratch = [0u8;32];
    }";
    // Outer handle/buffer 32, boxed middle handle 24, middle buffer 24,
    // inner buffer 8 and leaf allocation 16, then 32 bytes of scratch.
    verifies("deep_elements", &code.replace("BOUND", "136"));
    rejects("deep_elements_short", &code.replace("BOUND", "135"), "memory budget exceeded");
}

#[test]
fn populated_collection_returns_and_forwarding_preserve_children() {
    let code = "fn make() -> Vec<Box<[u8;16]>> resources peak(memory) <= 56 {
        let mut v = Vec::with_capacity(1); let b = Box::new([0u8;16]); v.push(b); v
    }
    fn forward(v: Vec<Box<[u8;16]>>) -> Vec<Box<[u8;16]>> resources peak(memory) <= 24 { v }
    fn f() resources peak(memory) <= BOUND {
        let v = make(); let w = forward(v); let scratch = [0u8;32];
    }";
    // The existing replacement summary bounds the outer buffer by make's
    // budget: handle 24 + buffer bound 56 + children 16 + scratch 32.
    verifies("returned_elements", &code.replace("BOUND", "128"));
    rejects("returned_elements_short", &code.replace("BOUND", "127"), "memory budget exceeded");
}

#[test]
fn input_ownership_can_be_collected_and_returned() {
    let code = "fn collect(b: Box<[u8;16]>) -> Vec<Box<[u8;16]>> resources peak(memory) <= 40 {
        let mut v = Vec::with_capacity(1); v.push(b); v
    }
    fn f() resources peak(memory) <= BOUND {
        let b = Box::new([0u8;16]); let v = collect(b); let scratch = [0u8;32];
    }";
    // Handle 24 + conservative buffer bound 40 + captured child 16 + scratch 32.
    verifies("collected_input", &code.replace("BOUND", "112"));
    rejects("collected_input_short", &code.replace("BOUND", "111"), "memory budget exceeded");
}

#[test]
fn borrowed_collection_captures_transferred_inputs() {
    let code = "fn append(v: &mut Vec<Box<[u8;16]>>, b: Box<[u8;16]>)
        requires old(v).len() < 2, ensures final(v).len() == old(v).len()+1,
        resources peak(memory) <= 16 { v.push(b); }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(2);
        let a = Box::new([0u8;16]); append(&mut v, a);
        let b = Box::new([0u8;16]); append(&mut v, b);
        let scratch = [0u8;32];
    }";
    verifies("borrowed_collected_inputs", &code.replace("BOUND", "104"));
    rejects(
        "borrowed_collected_inputs_short",
        &code.replace("BOUND", "103"),
        "memory budget exceeded",
    );
}

#[test]
fn one_collection_captures_multiple_input_owners() {
    let code = "fn append(v: &mut Vec<Box<[u8;16]>>, a: Box<[u8;16]>, b: Box<[u8;16]>)
        requires old(v).len() == 0, ensures final(v).len() == 2,
        resources peak(memory) <= 24 { v.push(a); v.push(b); }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(2);
        let a = Box::new([0u8;16]); let b = Box::new([0u8;16]); append(&mut v, a, b);
        let scratch = [0u8;32];
    }";
    verifies("multiple_captures", &code.replace("BOUND", "104"));
    rejects("multiple_captures_short", &code.replace("BOUND", "103"), "memory budget exceeded");
}

#[test]
fn borrowed_helper_additions_accumulate() {
    let code = "fn append(v: &mut Vec<Box<[u8;16]>>)
        requires old(v).len() < 2, ensures final(v).len() == old(v).len()+1,
        resources peak(memory) <= 32 { let b = Box::new([0u8;16]); v.push(b); }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(2); append(&mut v); append(&mut v);
        let scratch = [0u8;32];
    }";
    verifies("borrowed_child_additions", &code.replace("BOUND", "104"));
    rejects(
        "borrowed_child_additions_short",
        &code.replace("BOUND", "103"),
        "memory budget exceeded",
    );
}

#[test]
fn owning_input_collection_retains_additions_and_other_inputs() {
    let code = "fn append(mut v: Vec<Box<[u8;16]>>, b: Box<[u8;16]>) -> Vec<Box<[u8;16]>>
        requires v.len() < 2, resources peak(memory) <= 32 { v.push(b); v }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(2); let a = Box::new([0u8;16]); v.push(a);
        let b = Box::new([0u8;16]); let w = append(v,b); let scratch = [0u8;32];
    }";
    verifies("returned_input_elements", &code.replace("BOUND", "104"));
    rejects(
        "returned_input_elements_short",
        &code.replace("BOUND", "103"),
        "memory budget exceeded",
    );
}

#[test]
fn boxed_slice_conversion_keeps_child_allocations() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(2);
        let a = Box::new([0u8;16]); v.push(a);
        let b = v.into_boxed_slice(); let scratch = [0u8;64];
    }";
    verifies("owning_slice", &code.replace("BOUND", "104"));
    rejects("owning_slice_short", &code.replace("BOUND", "103"), "memory budget exceeded");
}

#[test]
fn owning_slice_helpers_transfer_whole_collections() {
    verifies("owning_slice_helpers", "fn make() -> Box<[Box<[u8;16]>]> resources peak(memory) <= 100 {
        let mut v = Vec::with_capacity(2); let a = Box::new([0u8;16]); v.push(a); v.into_boxed_slice()
    }
    fn forward(v: Box<[Box<[u8;16]>]>) -> Box<[Box<[u8;16]>]> resources peak(memory) <= 16 { v }
    fn f() resources peak(memory) <= 200 { let a = make(); let b = forward(a); drop(b); let scratch = [0u8;200]; }");
}

#[test]
fn branch_insertions_keep_the_selected_child_footprint() {
    let code = "fn f(flag: bool) resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(1);
        if flag { let b = Box::new([0u8;16]); v.push(b); }
        let scratch = [0u8;32];
    }";
    verifies("branch_elements", &code.replace("BOUND", "81"));
    rejects("branch_elements_short", &code.replace("BOUND", "80"), "memory budget exceeded");
}

#[test]
fn section_cannot_hide_new_children_of_enclosing_collection() {
    rejects(
        "section_elements",
        "fn f() resources peak(memory) <= 100 {
        let mut v = Vec::<Box<u32>>::with_capacity(1);
        resources peak(memory) <= 16 { let b = Box::new(1u32); v.push(b); }
    }",
        "adding owning children to an enclosing collection inside a memory section",
    );
}

#[test]
fn owning_pop_still_requires_conditional_ownership() {
    rejects(
        "element_pop",
        "fn f(mut v: Vec<Box<u32>>) resources peak(memory) <= 100 { let removed = v.pop(); }",
        "owning or reference-valued Option payloads",
    );
}

#[test]
fn recursive_collection_layouts_are_rejected() {
    rejects(
        "recursive_elements",
        "struct Node { children: Vec<Node> }
        fn f(v: Node) resources peak(memory) <= 100 {}",
        "recursive struct layouts",
    );
}

#[test]
fn runtime_child_bytes_cannot_be_omitted_from_the_budget() {
    rejects(
        "element_loop_short",
        "fn f(n: usize) requires n <= 4,
        resources peak(memory) <= 48 + 8*n {
        let mut v = Vec::<Box<[u8;16]>>::with_capacity(n); let mut i = 0usize;
        while i < n invariant i <= n, v.len() == i, decreases n-i, {
            let b = Box::new([0u8;16]); v.push(b); i += 1;
        }
    }",
        "memory budget exceeded",
    );
}

#[test]
fn captures_survive_nested_borrowed_helper_calls() {
    let code = "struct C { data: Box<Vec<Box<[u8;16]>>> }
        fn append(v: &mut Vec<Box<[u8;16]>>, b: Box<[u8;16]>)
            requires old(v).len() == 0, ensures final(v).len() == 1,
            resources peak(memory) <= 16 { v.push(b); }
        fn relay(p: &mut C, b: Box<[u8;16]>)
            requires old(p).data.len() == 0, ensures final(p).data.len() == 1,
            resources peak(memory) <= 32 { append(&mut *p.data, b); }
        fn f() resources peak(memory) <= BOUND {
            let mut p = C { data: Box::new(Vec::with_capacity(1)) };
            let b = Box::new([0u8;16]); relay(&mut p, b); let scratch = [0u8;64];
        }";
    verifies("nested_captures", &code.replace("BOUND", "120"));
    rejects("nested_captures_short", &code.replace("BOUND", "119"), "memory budget exceeded");
}

#[test]
fn collection_drop_releases_captured_input_allocations() {
    let code = "fn consume(b: Box<[u8;80]>) resources peak(memory) <= 40 {
        let mut v = Vec::with_capacity(1); v.push(b); drop(v);
    }
    fn f() resources peak(memory) <= BOUND {
        let b = Box::new([0u8;80]); consume(b); let scratch = [0u8;120];
    }";
    verifies("captured_drop", &code.replace("BOUND", "120"));
    rejects("captured_drop_short", &code.replace("BOUND", "119"), "memory budget exceeded");
}

#[test]
fn incoming_owning_slice_conversion_retains_opaque_input_provenance() {
    let code = "fn freeze(v: Vec<Box<[u8;16]>>) -> Box<[Box<[u8;16]>]>
        requires v.len() == 1, resources peak(memory) <= 48 { v.into_boxed_slice() }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(4); let b = Box::new([0u8;16]); v.push(b);
        let fixed = freeze(v); let scratch = [0u8;64];
    }";
    // 16-byte boxed-slice handle, conservative 48-byte new backing bound,
    // old incoming buffer 32 and its child 16, then 64-byte scratch.
    verifies("incoming_owning_slice", &code.replace("BOUND", "176"));
    rejects("incoming_owning_slice_short", &code.replace("BOUND", "175"), "memory budget exceeded");
}

#[test]
fn zero_byte_children_do_not_create_payload_charges() {
    verifies(
        "zero_children",
        "fn f() resources peak(memory) <= 40 {
        let mut v = Vec::<Box<[u8;0]>>::with_capacity(1);
        let b = Box::new([]); v.push(b); drop(v); let scratch = [0u8;40];
    }",
    );
}

#[test]
fn growing_children_are_charged_before_insertion() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut outer = Vec::<Vec<u32>>::with_capacity(1);
        let mut child = Vec::<u32>::new(); child.push(1); outer.push(child);
        let scratch = [0u8;32];
    }";
    verifies("grown_element", &code.replace("BOUND", "96"));
    rejects("grown_element_short", &code.replace("BOUND", "95"), "memory budget exceeded");
}

#[test]
fn owning_collections_example_verifies_and_compiles() {
    crate::verify_one_file(
        "owning_collections_example",
        include_str!("../../../../../examples/resource/memory/owning_collections.rs").into(),
        &["--compile"],
    )
    .unwrap();
}
