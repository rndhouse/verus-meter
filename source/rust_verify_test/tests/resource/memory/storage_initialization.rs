use crate::common::*;
use crate::verify_one_file;

#[test]
fn lexical_examples_use_their_own_budgets() {
    verify_one_file(
        "lexical_examples_use_their_own_budgets",
        include_str!("../../../../../examples/resource/memory/storage.rs").into(),
        &[],
    )
    .unwrap();
}

// Check both acceptance at the predicted peak and rejection one byte below it.
fn exact_peak(name: &str, code: &str, peak: u64) {
    let source = |budget| {
        format!(
            "use vstd::prelude::*; verus! {{ {} }}",
            code.replace("BUDGET", &format!("{budget}u64")),
        )
    };
    verify_one_file(name, source(peak), &[]).unwrap();
    let err = verify_one_file(&format!("{name}_short"), source(peak - 1), &[]).unwrap_err();
    assert_vir_error_msg(err, &format!("peak {peak} bytes exceeds budget {} bytes", peak - 1));
}

#[test]
fn array_repeat_has_one_destination() {
    exact_peak(
        "array_repeat_has_one_destination",
        "fn f() mem_peak <= BUDGET { let a = [0u32; 4]; }",
        16,
    );
}

#[test]
fn array_literal_has_one_destination() {
    exact_peak(
        "array_literal_has_one_destination",
        "fn f() mem_peak <= BUDGET { let a = [0u32, 1, 2, 3]; }",
        16,
    );
}

#[test]
fn element_computation_uses_destination() {
    exact_peak(
        "element_computation_uses_destination",
        "fn f() mem_peak <= BUDGET { let a = [1u32 + 2u32; 4]; }",
        16,
    );
}

#[test]
fn nested_array_field_shares_struct_storage() {
    exact_peak(
        "nested_array_field_shares_struct_storage",
        r#"
        struct Buffer { values: [u32; 8], ready: bool }
        fn f() mem_peak <= BUDGET {
            let b = Buffer { values: [0u32; 8], ready: false };
        }"#,
        33,
    );
}

#[test]
fn nested_literal_field_shares_struct_storage() {
    exact_peak(
        "nested_literal_field_shares_struct_storage",
        r#"
        struct Inner { values: [u32; 4] }
        struct Outer { inner: Inner, ready: bool }
        fn f() mem_peak <= BUDGET {
            let b = Outer { inner: Inner { values: [0u32, 1, 2, 3] }, ready: false };
        }"#,
        17,
    );
}

#[test]
fn explicit_intermediate_array_remains_charged() {
    exact_peak(
        "explicit_intermediate_array_remains_charged",
        r#"
        struct Buffer { values: [u32; 8], ready: bool }
        fn f() mem_peak <= BUDGET {
            let values = [0u32; 8];
            let b = Buffer { values, ready: false };
        }"#,
        65,
    );
}

#[test]
fn explicit_intermediate_struct_remains_charged() {
    exact_peak(
        "explicit_intermediate_struct_remains_charged",
        r#"
        struct Inner { x: u32 }
        struct Outer { inner: Inner, ready: bool }
        fn f() mem_peak <= BUDGET {
            let inner = Inner { x: 1 };
            let outer = Outer { inner, ready: false };
        }"#,
        9,
    );
}

#[test]
fn array_copy_counts_source_and_destination() {
    exact_peak(
        "array_copy_counts_source_and_destination",
        "fn f(a: [u32; 4]) mem_peak <= BUDGET { let b = a; }",
        32,
    );
}

#[test]
fn borrowed_array_copy_charges_reference_and_destination() {
    exact_peak(
        "borrowed_array_copy_charges_reference_and_destination",
        "fn f(a: &mut [u32; 4]) mem_peak <= BUDGET { let b = *a; }",
        24,
    );
}

#[test]
fn standalone_nested_aggregate_has_one_result() {
    exact_peak(
        "standalone_nested_aggregate_has_one_result",
        r#"
        struct Inner { values: [u32; 4] }
        struct Outer { inner: Inner }
        fn f() mem_peak <= BUDGET {
            Outer { inner: Inner { values: [0u32; 4] } };
        }"#,
        16,
    );
}

#[test]
fn delayed_initialization_uses_reserved_slot() {
    exact_peak(
        "delayed_initialization_uses_reserved_slot",
        "fn f() mem_peak <= BUDGET { let a: [u32; 4]; a = [0u32; 4]; }",
        16,
    );
}

#[test]
fn aggregate_reassignment_reuses_destination() {
    exact_peak(
        "aggregate_reassignment_reuses_destination",
        "fn f() mem_peak <= BUDGET { let mut a = [0u32; 4]; a = [1u32; 4]; }",
        16,
    );
}

#[test]
fn assignment_reads_create_no_source_slots() {
    exact_peak(
        "assignment_reads_create_no_source_slots",
        r#"
        struct Pair { x: u32, y: u32 }
        fn f(p: &mut Pair)
            ensures final(p).x == old(p).y, final(p).y == old(p).x,
            mem_peak <= BUDGET,
        { *p = Pair { x: p.y, y: p.x }; }"#,
        8,
    );
}

#[test]
fn array_copy_assignment_has_no_third_array() {
    exact_peak(
        "array_copy_assignment_has_no_third_array",
        r#"
        fn f() mem_peak <= BUDGET {
            let a = [0u32; 4];
            let mut b = [1u32; 4];
            b = a;
        }"#,
        32,
    );
}

#[test]
fn constructor_argument_initializes_parameter() {
    exact_peak(
        "constructor_argument_initializes_parameter",
        r#"
        struct Buffer { values: [u32; 8], ready: bool }
        fn leaf(b: Buffer) mem_peak <= mem_size(b) {}
        fn f() mem_peak <= BUDGET {
            leaf(Buffer { values: [0u32; 8], ready: false });
        }"#,
        33,
    );
}

#[test]
fn earlier_aggregate_parameter_survives_later_argument() {
    exact_peak(
        "earlier_aggregate_parameter_survives_later_argument",
        r#"
        fn leaf(a: [u32; 4], b: [u32; 4]) mem_peak <= 32 {}
        fn f() mem_peak <= BUDGET {
            leaf([0u32; 4], [1u32 + 2u32; 4]);
        }"#,
        32,
    );
}

#[test]
fn mixed_arguments_use_parameter_storage() {
    exact_peak(
        "mixed_arguments_use_parameter_storage",
        r#"
        fn leaf(a: [u32; 4], b: u32) mem_peak <= 20 {}
        fn f() mem_peak <= BUDGET { leaf([0u32; 4], 1); }
        "#,
        20,
    );
}

#[test]
fn source_array_and_callee_parameter_are_distinct() {
    exact_peak(
        "source_array_and_callee_parameter_are_distinct",
        r#"
        fn leaf(a: [u32; 4]) mem_peak <= 16 {}
        fn f(a: [u32; 4]) mem_peak <= BUDGET { leaf(a); }
        "#,
        32,
    );
}

#[test]
fn scalar_argument_is_retained_during_aggregate_initialization() {
    exact_peak(
        "scalar_argument_is_retained_during_aggregate_initialization",
        r#"
        fn leaf(a: u32, b: [u32; 4]) mem_peak <= 20 {}
        fn f() mem_peak <= BUDGET { leaf(1, [1u32 + 2u32; 4]); }
        "#,
        20,
    );
}

test_verify_one_file! {
    #[test] literals_need_no_source_storage verus_code! {
        #[allow(unused_must_use)]
        fn f() mem_peak <= 0 {
            1u32;
            true;
            1u32 + 2u32;
        }
    } => Ok(())
}

#[test]
fn scalar_literal_initializes_its_local() {
    exact_peak(
        "scalar_literal_initializes_its_local",
        "fn f() mem_peak <= BUDGET { let x = 0u32; }",
        4,
    );
}

#[test]
fn named_fill_value_remains_charged() {
    exact_peak(
        "named_fill_value_remains_charged",
        r#"
        fn f() mem_peak <= BUDGET {
            let fill = 0u32;
            let array = [fill; 4];
        }"#,
        20,
    );
}

#[test]
fn arithmetic_charges_only_declared_values() {
    exact_peak(
        "arithmetic_charges_only_declared_values",
        r#"
        fn f(a: u32, b: u32)
            requires a < 10, b < 10,
            mem_peak <= BUDGET,
        { let sum = a + b; }"#,
        12,
    );
}

#[test]
fn earlier_scalar_parameter_stays_live_during_nested_call() {
    exact_peak(
        "earlier_scalar_parameter_stays_live_during_nested_call",
        r#"
        fn helper() mem_peak <= 32 { let workspace = [0u32; 8]; }
        fn leaf(a: u32, b: ()) mem_peak <= 4 {}
        fn f() mem_peak <= BUDGET { leaf(1, helper()); }
        "#,
        36,
    );
}

#[test]
fn later_parameter_is_not_reserved_before_its_argument() {
    exact_peak(
        "later_parameter_is_not_reserved_before_its_argument",
        r#"
        fn helper() mem_peak <= 32 { let workspace = [0u32; 8]; }
        fn leaf(a: (), b: u32) mem_peak <= 4 {}
        fn f() mem_peak <= BUDGET { leaf(helper(), 1); }
        "#,
        32,
    );
}

test_verify_one_file! {
    #[test] zero_length_repeat_still_checks_operand verus_code! {
        use vstd::prelude::*;
        fn f(x: u32) mem_peak <= 4 {
            let empty = [x + 1; 0]; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] unsupported_discarded_scalar_is_still_rejected verus_code! {
        fn f() mem_peak <= 0 { 'x'; }
    } => Err(err) => assert_vir_error_msg(err, "does not support this executable expression")
}
