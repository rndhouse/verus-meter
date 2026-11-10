use crate::common::*;
use crate::verify_one_file;

fn struct_example() -> String {
    include_str!("../../../../../examples/resource/memory/algorithms/structs.rs").replace(
        "#[path = \"insertion_sort.rs\"]\nmod sorting;",
        &format!(
            "mod sorting {{ {} }}",
            include_str!("../../../../../examples/resource/memory/algorithms/insertion_sort.rs")
        ),
    )
}

#[test]
fn sorting_through_struct_field() {
    verify_one_file("sorting_through_struct_field", struct_example(), &[]).unwrap();
}

#[test]
fn sorting_struct_one_byte_short() {
    let code = struct_example().replace("value_size(SortBuffer)", "32u64");
    let err = verify_one_file("sorting_struct_one_byte_short", code, &[]).unwrap_err();
    assert_vir_error_msg(err, "peak 85 bytes exceeds budget 84 bytes");
}

#[test]
fn changed_struct_field_updates_budget() {
    let code = struct_example()
        .replace("pub ready: bool,", "pub ready: bool, pub extra: u32,")
        .replace("ready: false,", "ready: false, extra: 0u32,");
    verify_one_file("changed_struct_field_updates_budget", code.clone(), &[]).unwrap();
    let frozen = code.replace("value_size(SortBuffer)", "33u64");
    let err = verify_one_file("changed_struct_field_frozen_budget", frozen, &[]).unwrap_err();
    assert_vir_error_msg(err, "peak 89 bytes exceeds budget 85 bytes");
}

test_verify_one_file! {
    #[test] struct_size_excludes_padding verus_code! {
        struct Pair { small: bool, large: usize }
        fn f(p: Pair) resources peak(memory) <= 9 {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_parameter_one_byte_short verus_code! {
        struct Pair { small: bool, large: usize }
        fn f(p: Pair) resources peak(memory) <= 8 {}
    } => Err(err) => assert_vir_error_msg(err, "peak 9 bytes exceeds budget 8 bytes")
}

test_verify_one_file! {
    #[test] constructor_destination_is_charged verus_code! {
        struct Pair { small: bool, large: usize }
        fn f() resources peak(memory) <= 8 {
            let p = Pair { large: 4, small: true };
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 9 bytes exceeds budget 8 bytes")
}

test_verify_one_file! {
    #[test] constructor_exact_budget verus_code! {
        struct Pair { small: bool, large: usize }
        fn f() resources peak(memory) <= 9 {
            let p = Pair { large: 4, small: true };
            assert(p.large == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_struct_layout_and_construction verus_code! {
        struct Inner { x: u32 }
        struct Outer { inner: Inner, flag: bool }
        fn f() resources peak(memory) <= 5 {
            let p = Outer { inner: Inner { x: 42 }, flag: true };
            assert(p.inner.x == 42);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_struct_constructor_one_byte_short verus_code! {
        struct Inner { x: u32 }
        struct Outer { inner: Inner, flag: bool }
        fn f() resources peak(memory) <= 4 {
            let p = Outer { inner: Inner { x: 42 }, flag: true };
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 5 bytes exceeds budget 4 bytes")
}

test_verify_one_file! {
    #[test] copying_whole_struct_keeps_original_slot verus_code! {
        use vstd::prelude::*;
        #[derive(Copy, Clone)]
        struct Pair { a: u32, b: u32 }
        fn f(p: Pair) resources peak(memory) <= 15 { let copy = p; }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds budget 15 bytes")
}

test_verify_one_file! {
    #[test] moving_struct_transfers_its_charge verus_code! {
        struct Pair { a: u32, b: u32 }
        fn f(p: Pair) resources peak(memory) <= 8 { let moved = p; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] field_read_does_not_copy_other_fields verus_code! {
        struct Big { values: [u32; 64], tag: u32 }
        fn f(p: Big) resources peak(memory) <= 264 { let tag = p.tag; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] field_array_copy_is_charged verus_code! {
        struct Big { values: [u32; 64], tag: u32 }
        fn f(p: Big) resources peak(memory) <= 515 { let copy = p.values; }
    } => Err(err) => assert_vir_error_msg(err, "peak 516 bytes exceeds budget 515 bytes")
}

test_verify_one_file! {
    #[test] shared_field_read_charges_reference_and_local verus_code! {
        struct S { n: u32 }
        fn f(p: &S) resources peak(memory) <= 11 { let n = p.n; }
    } => Err(err) => assert_vir_error_msg(err, "peak 12 bytes exceeds budget 11 bytes")
}

test_verify_one_file! {
    #[test] mutable_field_read_and_write verus_code! {
        struct S { n: u32 }
        fn f(p: &mut S)
            requires old(p).n < 10,
            ensures final(p).n == old(p).n + 1,
            resources peak(memory) <= 8,
        { p.n += 1; }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutable_field_borrow_and_write verus_code! {
        struct S { n: u32 }
        fn f(p: &mut S)
            ensures final(p).n == 42,
            resources peak(memory) <= 16,
        {
            let field = &mut p.n;
            *field = 42;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] by_value_call_transfers_struct verus_code! {
        struct S { n: u32 }
        fn leaf(p: S) resources peak(memory) <= 4 {}
        fn f(p: S) resources peak(memory) <= 4 { leaf(p); }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unit_and_tuple_structs verus_code! {
        struct Empty;
        struct Pair(u32, bool);
        fn f() resources peak(memory) <= 5 {
            let empty = Empty;
            let p = Pair(1, true);
            assert(p.0 == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] single_variant_enum_is_not_a_struct verus_code! {
        enum E { Only { n: u32 } }
        fn f(p: E) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "enum or union layouts")
}

test_verify_one_file! {
    #[test] single_field_union_is_not_a_struct verus_code! {
        union U { n: u32 }
        fn f(p: U) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "enum or union layouts")
}

test_verify_one_file! {
    #[test] concrete_instantiation_of_generic_struct_rejected verus_code! {
        struct S<T> { value: T }
        fn f(p: S<u32>) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "generic struct layouts")
}

test_verify_one_file! {
    #[test] struct_reference_fields_rejected verus_code! {
        struct S<'a> { value: &'a u32 }
        fn f(p: S) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "reference or decorated struct fields")
}

test_verify_one_file! {
    #[test] unsupported_field_types_rejected verus_code! {
        struct S { value: char }
        fn f(p: S) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "does not support this type")
}

test_verify_one_file! {
    #[test] opaque_struct_rejected verus_code! {
        #[verifier::external_body]
        struct S { value: u32 }
        fn f(p: S) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "opaque, proxy, ghost, or invariant-bearing structs")
}

test_verify_one_file! {
    #[test] shared_array_field_read_charges_parameters_and_local verus_code! {
        struct S { values: [u32; 4], flag: bool }
        fn f(p: &S, i: usize)
            requires i < 4,
            resources peak(memory) <= 19,
        { let x = p.values[i]; }
    } => Err(err) => assert_vir_error_msg(err, "peak 20 bytes exceeds budget 19 bytes")
}

test_verify_one_file! {
    #[test] nested_field_read_charges_reference_and_local verus_code! {
        struct Inner { x: u32 }
        struct Outer { inner: Inner, other: u32 }
        fn f(p: &Outer) resources peak(memory) <= 11 { let x = p.inner.x; }
    } => Err(err) => assert_vir_error_msg(err, "peak 12 bytes exceeds budget 11 bytes")
}

test_verify_one_file! {
    #[test] array_field_assignment_keeps_parameters verus_code! {
        use vstd::prelude::*;
        struct S { values: [u32; 4] }
        fn f(p: &mut S, i: usize, j: usize)
            requires i < 4, j < 4,
            resources peak(memory) <= 23,
        { p.values[i] = p.values[j]; }
    } => Err(err) => assert_vir_error_msg(err, "peak 24 bytes exceeds budget 23 bytes")
}

test_verify_one_file! {
    #[test] copying_struct_exact_budget verus_code! {
        use vstd::prelude::*;
        #[derive(Copy, Clone)]
        struct Pair { a: u32, b: u32 }
        fn f(p: Pair) resources peak(memory) <= 16 {
            let copy = p;
            assert(copy.a == p.a && copy.b == p.b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_update_remains_rejected verus_code! {
        struct S { x: u32, y: u32 }
        fn f(p: S) resources peak(memory) <= 1000 {
            let updated = S { x: 1, ..p };
        }
    } => Err(err) => assert_vir_error_msg(err, "struct update syntax")
}

test_verify_one_file! {
    #[test] borrowed_temporary_struct_remains_rejected verus_code! {
        struct S { n: u32 }
        fn f() resources peak(memory) <= 1000 { let p = &S { n: 42 }; }
    } => Err(err) => assert_vir_error_msg(err, "borrowed temporary")
}

test_verify_one_file! {
    #[test] struct_with_drop_is_rejected verus_code! {
        struct S { n: u32 }
        impl Drop for S {
            fn drop(&mut self) opens_invariants none no_unwind {}
        }
        fn f(p: S) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "structs with destructors")
}

test_verify_one_file! {
    #[test] nested_drop_is_rejected verus_code! {
        struct Inner { n: u32 }
        impl Drop for Inner { fn drop(&mut self) opens_invariants none no_unwind {} }
        struct Outer { inner: Inner }
        fn f(p: Outer) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "structs with destructors")
}

test_verify_one_file! {
    #[test] ghost_fields_are_explicitly_rejected verus_code! {
        struct S { n: u32, ghost proof_only: int }
        fn f(p: S) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "ghost or tracked struct fields")
}

test_verify_one_file! {
    #[test] mutable_field_borrow_charges_local_reference verus_code! {
        struct S { n: u32 }
        fn f(p: &mut S) resources peak(memory) <= 15 {
            let field = &mut p.n;
        }
    } => Err(err) => assert_vir_error_msg(err, "peak 16 bytes exceeds budget 15 bytes")
}

test_verify_one_file! {
    #[test] type_invariant_struct_is_rejected verus_code! {
        struct S { n: u32 }
        impl S {
            #[verifier::type_invariant]
            spec fn valid(&self) -> bool { self.n < 10 }
        }
        fn f(p: S) resources peak(memory) <= 1000 {}
    } => Err(err) => assert_vir_error_msg(err, "opaque, proxy, ghost, or invariant-bearing structs")
}
