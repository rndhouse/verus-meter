use crate::common::*;
use crate::verify_one_file;

test_verify_one_file! {
    #[test] queries_preserve_existing_inline_sizes verus_code! {
        use vstd::prelude::*;
        struct Data { values: [u32; 4], ready: bool }
        spec fn bytes(value: u32) -> nat { value_size(value) }
        spec fn reference_bytes(value: &[u32]) -> nat { ref_size(value) }
        proof fn sizes(value: Data, reference: &[u32; 100], slice: &[u32]) {
            assert(value_size(value) == 17);
            assert(value_size(Data) == 17);
            assert(value_size([u32; 100]) == 400);
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
            assert(value_size(value) == 24);
            assert(value_size(Vec<u32>) == 24);
            assert(value_size(boxed) == 8);
            assert(value_size(Box<Box<u32>>) == 8);
            assert(value_size(slice) == 16);
            assert(value_size(Owners) == 33);
        }
        fn allocate() resources peak(memory) <= value_size(Box<[u32; 4]>) + value_size([u32; 4]) {
            let data = Box::new([0u32; 4]);
            assert(peak(memory) <= value_size(data) + value_size([u32; 4]));
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
    #[test] value_size_rejects_reference_bindings verus_code! {
        fn f(value: &u32) resources peak(memory) <= value_size(value) {}
    } => Err(err) => assert_vir_error_msg(err, "value_size requires a non-reference")
}

test_verify_one_file! {
    #[test] value_size_rejects_reference_types_in_specifications verus_code! {
        proof fn sizes() { let n = value_size(&mut [u32; 4]); }
    } => Err(err) => assert_vir_error_msg(err, "value_size requires a non-reference")
}

test_verify_one_file! {
    #[test] existing_layout_restrictions_remain verus_code! {
        struct Borrowed<'a> { data: &'a [u32; 4] }
        proof fn sizes() { let n = value_size(Borrowed); }
    } => Err(err) => assert_vir_error_msg(err, "reference or decorated struct fields")
}

test_verify_one_file! {
    #[test] return_size_uses_the_instantiated_signature verus_code! {
        use vstd::prelude::*;
        type Sum = u16;
        mod packet {
            use vstd::prelude::*;
            pub fn checksum(byte: u8) -> super::Sum requires byte > 0 { byte as u16 }
        }
        fn identity<T>(value: T) -> T { value }
        fn view(bytes: &[u8]) -> &[u8] { bytes }
        fn no_result() {}
        spec fn bytes() -> nat { return_size(packet::checksum) }
        proof fn layouts() {
            assert(bytes() == value_size(Sum));
            assert(return_size(identity::<Vec<u16>>) == value_size(Vec<u16>));
            assert(return_size(view) == ref_size(&[u8]));
            assert(return_size(no_result) == 0);
        }
        fn section() resources peak(memory) <= return_size(packet::checksum) {
            resources peak(memory) <= return_size(packet::checksum) {
                let x = 1u16;
                assert(current(memory) <= return_size(packet::checksum));
            }
        }
        fn by_count(count: u32)
            requires count > 0,
            resources peak(memory) <= value_size(count) + count * return_size(packet::checksum)
        {
            let result = 1u16;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] return_size_checks_the_budget verus_code! {
        fn byte() -> u8 { 0 }
        fn exceeds() resources peak(memory) <= return_size(byte) {
            let x = 0u16;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 2 bytes exceeds budget 1 byte")
}

test_verify_one_file! {
    #[test] return_size_rejects_nonfunctions verus_code! {
        proof fn sizes(x: u32) { let n = return_size(x); }
    } => Err(err) => assert_vir_error_msg(err, "return_size expects a named function")
}
