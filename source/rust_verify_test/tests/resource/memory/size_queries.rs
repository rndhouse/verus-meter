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

#[test]
fn for_loop_size_matches_live_state_at_body_entry() {
    // Compare the query to the live checker for both thin and fat source references.
    // The enclosing section excludes the original parameter from the checkpoint.
    for (label, source, bytes) in [("slice", "&'a [u16]", 48), ("vector", "&'a Vec<u16>", 40)] {
        // Advancement also evaluates the tagged next result before the body runs.
        let section = "for_loop_size(items) + value_size(u8) + ref_size(&u16)";
        let code = format!(
            "type Source<'a> = {source};
            spec fn state() -> nat {{ for_loop_size(Source) }}
            fn visit(items: Source) resources peak(memory) <= ref_size(items) + {section} {{
                assert(state() == {bytes});
                resources peak(memory) <= {section} {{
                    for item in items {{ assert(current(memory) <= BOUND); }}
                }}
            }}"
        );
        super::support::verifies(
            &format!("for_loop_size_{label}"),
            &code.replace("BOUND", "for_loop_size(items)"),
        );
        super::support::rejects(
            &format!("for_loop_size_{label}_short"),
            &code.replace("BOUND", &(bytes - 1).to_string()),
            if label == "slice" {
                "current(memory) assertion failed"
            } else {
                "conditional memory budget exceeded"
            },
        );
    }
}

test_verify_one_file! {
    #[test] for_loop_size_rejects_consuming_traversal verus_code! {
        use vstd::prelude::*;
        proof fn check(items: Vec<u8>) { let n = for_loop_size(items); }
    } => Err(err) => assert_vir_error_msg(err, "for_loop_size requires a shared slice or vector reference")
}
