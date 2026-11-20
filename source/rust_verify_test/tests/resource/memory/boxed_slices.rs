use super::support::{rejects, verifies};

#[test]
fn conversion_releases_the_reservation_and_keeps_one_backing() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<u32>::with_capacity(4);
        v.push(7);
        let b = v.into_boxed_slice();
        assert(b.len() == 1);
        assert(b[0] == 7);
        let scratch = [0u8;32];
    }";
    let handles_and_reservation =
        "value_size(Vec<u32>) + value_size(Box<[u32]>) + value_size([u32; 4])";
    verifies("boxed_slice_one_backing", &code.replace("BOUND", handles_and_reservation));
    // Both handles and the reserved slots give a 56-byte peak.
    rejects(
        "boxed_slice_one_backing_short",
        &code.replace("BOUND", "55"),
        "memory budget exceeded",
    );
}

#[test]
fn forwarding_and_dropping_use_shared_ownership() {
    verifies(
        "boxed_slice_forward",
        "
        fn forward(b: Box<[u32]>) -> (r: Box<[u32]>) ensures r == b, resources peak(memory) <= 16 { b }
        fn consume(b: Box<[u32]>) resources peak(memory) <= 16 { }
        fn f() resources peak(memory) <= 100 {
            let mut v = Vec::<u32>::with_capacity(4); v.push(9);
            let b = v.into_boxed_slice();
            let c = forward(b);
            assert(c[0] == 9);
            consume(c);
            let scratch = [0u8;100];
        }",
    );
}

#[test]
fn runtime_conversion_crosses_helper_boundaries() {
    verifies(
        "boxed_slice_runtime",
        "
        fn freeze(v: Vec<u32>, n: usize) -> (b: Box<[u32]>)
            requires v.len() == n, n <= 8,
            ensures b.len() == n,
            resources peak(memory) <= 48 + 4 * n,
        { v.into_boxed_slice() }
        fn f() resources peak(memory) <= 160 {
            let mut v = Vec::<u32>::with_capacity(4); v.push(1);
            let b = freeze(v, 1);
            assert(b.len() == 1);
            drop(b);
            let scratch = [0u8;160];
        }",
    );
}

#[test]
fn borrowing_does_not_duplicate_backing_storage() {
    // Make the borrow call determine the peak: the slice's 16-byte handle,
    // four-byte payload, 64-byte scratch, and callee's 16-byte allowance coexist.
    let code = "
        fn update(s: &mut [u32]) requires old(s).len() == 1,
            ensures final(s)[0] == 8, resources peak(memory) <= 16 { s[0] = 8; }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<u32>::with_capacity(1); v.push(1);
            let mut b = v.into_boxed_slice();
            let scratch = [0u8;64];
            update(&mut *b);
            assert(b[0] == 8);
            let n = b.len();
        }";
    verifies("boxed_slice_borrow", &code.replace("BOUND", "100"));
    rejects("boxed_slice_borrow_short", &code.replace("BOUND", "99"), "memory budget exceeded");
}

#[test]
fn zero_sized_elements_and_empty_slices() {
    verifies(
        "boxed_slice_zero",
        "fn f() resources peak(memory) <= 40 {
        let mut v = Vec::<()>::new(); v.push(());
        let b = v.into_boxed_slice(); assert(b.len() == 1); drop(b);
        let v = Vec::<u8>::new(); let b = v.into_boxed_slice(); assert(b.len() == 0);
    }",
    );
}

#[test]
fn non_integer_elements_use_inline_layout() {
    verifies(
        "boxed_slice_struct",
        "struct Item { flag: bool, value: u32 }
        fn f() resources peak(memory) <= 100 {
            let mut v = Vec::<Item>::with_capacity(1);
            v.push(Item { flag: true, value: 7 });
            let b = v.into_boxed_slice(); assert(b.len() == 1);
        }",
    );
}

#[test]
fn unbounded_conversion_is_rejected() {
    rejects(
        "boxed_slice_unbounded",
        "fn f(v: Vec<u32>) -> Box<[u32]> resources peak(memory) <= 100 {
        v.into_boxed_slice()
    }",
        "memory budget exceeded",
    );
}

#[test]
fn conversion_charges_the_incoming_backing_through_a_helper() {
    let code = "fn freeze(v: Vec<u32>) -> Box<[u32]>
            requires v.len() == 1,
            resources peak(memory) <= value_size(Vec<u32>) + value_size(Box<[u32]>),
        { v.into_boxed_slice() }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<u32>::with_capacity(20); v.push(1);
            let b = freeze(v);
        }";
    verifies("boxed_slice_input_backing", &code.replace("BOUND", "120"));
    rejects(
        "boxed_slice_input_backing_short",
        &code.replace("BOUND", "119"),
        "memory budget exceeded",
    );
}

#[test]
fn region_local_slices_release_their_storage() {
    verifies(
        "boxed_slice_regions",
        "fn f(flag: bool) resources peak(memory) <= 100 {
        if flag { let v = Vec::<u32>::with_capacity(4); let b = v.into_boxed_slice(); }
        resources peak(memory) <= 80 { let v = Vec::<u32>::with_capacity(4); let b = v.into_boxed_slice(); }
        let scratch = [0u8;99];
    }",
    );
    rejects(
        "boxed_slice_protected",
        "fn f(flag: bool) resources peak(memory) <= 100 {
        let v = Vec::<u32>::new();
        if flag { let b = v.into_boxed_slice(); }
    }",
        "moving or dropping an enclosing heap owner",
    );
}

#[test]
fn boxed_slice_example_verifies_and_compiles() {
    crate::verify_one_file(
        "boxed_slices",
        include_str!("../../../../../examples/resource/memory/heap/boxed_slices.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn retained_slice_bytes_remain_charged() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<u32>::with_capacity(4); v.push(1);
        let b = v.into_boxed_slice();
        let scratch = [0u8;45];
    }";
    verifies("boxed_slice_retained", &code.replace("BOUND", "65"));
    rejects("boxed_slice_retained_short", &code.replace("BOUND", "64"), "memory budget exceeded");
}

#[test]
fn boxed_slice_handle_layout_is_independent_of_payload() {
    verifies(
        "boxed_slice_handle",
        "fn f(b: Box<[u32]>) resources peak(memory) <= value_size(Box<[u32]>) { }",
    );
    rejects(
        "boxed_slice_handle_short",
        "fn f(b: Box<[u32]>) resources peak(memory) <= 15 {}",
        "peak 16 bytes exceeds budget 15 bytes",
    );
}

#[test]
fn loop_local_snapshots_do_not_accumulate() {
    verifies(
        "boxed_slice_loop",
        "fn f(n: usize) requires n <= 4, resources peak(memory) <= 88 {
        let mut i = 0usize;
        while i < n invariant i <= n, n <= 4, decreases n - i {
            let mut v = Vec::<u32>::with_capacity(n); v.push(1);
            let b = v.into_boxed_slice(); assert(b.len() == 1);
            i = i + 1;
        }
        let scratch = [0u8;72];
    }",
    );
}

#[test]
fn moved_owner_keeps_captured_extent_after_receiver_shadowing() {
    verifies(
        "boxed_slice_shadow",
        "fn f() resources peak(memory) <= 80 {
        let mut v = Vec::<u32>::with_capacity(2); v.push(1);
        let b = v.into_boxed_slice();
        let v = Vec::<u32>::new();
        let c = b;
        assert(c.len() == 1);
        drop(c); drop(v);
        let scratch = [0u8;80];
    }",
    );
}
