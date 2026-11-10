use crate::common::*;

test_verify_one_file! {
    #[test] queries_preserve_existing_inline_sizes verus_code! {
        use vstd::prelude::*;
        struct Data { values: [u32; 4], ready: bool }
        spec fn bytes(value: u32) -> nat { owned_size(value) }
        spec fn reference_bytes(value: &[u32]) -> nat { ref_size(value) }
        proof fn sizes(value: Data, reference: &[u32; 100], slice: &[u32]) {
            assert(owned_size(value) == 17);
            assert(owned_size(Data) == 17);
            assert(owned_size([u32; 100]) == 400);
            assert(bytes(7) == 4);
            assert(ref_size(reference) == 8);
            assert(ref_size(&mut [u32; 100]) == 8);
            assert(ref_size(slice) == 16);
            assert(reference_bytes(slice) == 16);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] owning_handles_exclude_separate_allocations verus_code! {
        use vstd::prelude::*;
        struct Owners { vector: Vec<u32>, boxed: Box<[u32; 100]>, ready: bool }
        proof fn sizes(value: Vec<u32>, boxed: Box<[u32; 100]>, slice: Box<[u32]>) {
            assert(owned_size(value) == 24);
            assert(owned_size(Vec<u32>) == 24);
            assert(owned_size(boxed) == 8);
            assert(owned_size(Box<Box<u32>>) == 8);
            assert(owned_size(slice) == 16);
            assert(owned_size(Owners) == 33);
        }
        fn allocate() resources peak(memory) <= owned_size(Box<[u32; 4]>) + owned_size([u32; 4]) {
            let data = Box::new([0u32; 4]);
            assert(peak(memory) <= owned_size(data) + owned_size([u32; 4]));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reference_aliases_use_reference_query verus_code! {
        type Borrow<'a> = &'a [u32; 100];
        proof fn sizes(value: Borrow) {
            assert(ref_size(value) == 8);
            assert(ref_size(Borrow) == 8);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ref_size_rejects_nonreferences verus_code! {
        fn f(value: u32) resources peak(memory) <= ref_size(value) {}
    } => Err(err) => assert_vir_error_msg(err, "ref_size requires a reference")
}

test_verify_one_file! {
    #[test] ref_size_rejects_owning_handles verus_code! {
        use vstd::prelude::*;
        proof fn sizes(value: Box<u32>) { let n = ref_size(value); }
    } => Err(err) => assert_vir_error_msg(err, "ref_size requires a reference")
}

test_verify_one_file! {
    #[test] owned_size_rejects_reference_bindings verus_code! {
        fn f(value: &u32) resources peak(memory) <= owned_size(value) {}
    } => Err(err) => assert_vir_error_msg(err, "owned_size requires a non-reference")
}

test_verify_one_file! {
    #[test] owned_size_rejects_reference_types_in_specifications verus_code! {
        proof fn sizes() { let n = owned_size(&mut [u32; 4]); }
    } => Err(err) => assert_vir_error_msg(err, "owned_size requires a non-reference")
}

test_verify_one_file! {
    #[test] existing_layout_restrictions_remain verus_code! {
        struct Borrowed<'a> { data: &'a [u32; 4] }
        proof fn sizes() { let n = owned_size(Borrowed); }
    } => Err(err) => assert_vir_error_msg(err, "reference or decorated struct fields")
}

test_verify_one_file! {
    #[test] former_size_query_has_no_builtin_alias verus_code! {
        fn f(value: u32) resources peak(memory) <= mem_size(value) {}
    } => Err(err) => assert_rust_error_msg(err, "cannot find function `mem_size`")
}
