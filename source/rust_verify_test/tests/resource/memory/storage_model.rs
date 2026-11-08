use super::support::exact_peak;

// Boundary checks for the remaining model policies, independent of the examples.

#[test]
fn fixed_size_policy_and_unpadded_fields() {
    exact_peak(
        "fixed_size_policy_and_unpadded_fields",
        r#"
        struct Small { n: u32, ready: bool }
        fn f(empty: (), flag: bool, n: u32, index: usize, reference: &u32,
             slice: &[u32], array: [u32; 3], record: Small)
            mem_peak <= BUDGET {}
        "#,
        54,
    );
}

#[test]
fn two_borrows_do_not_duplicate_the_backing_array() {
    exact_peak(
        "two_borrows_do_not_duplicate_the_backing_array",
        r#"
        fn leaf(a: &[u32], b: &[u32]) mem_peak <= 32 {}
        fn f() mem_peak <= BUDGET {
            let data = [0u32; 4];
            leaf(&data, &data);
        }
        "#,
        48,
    );
}

#[test]
fn reference_locals_end_with_their_scopes() {
    exact_peak(
        "reference_locals_end_with_their_scopes",
        r#"
        fn f() mem_peak <= BUDGET {
            let data = [0u32; 4];
            { let first: &[u32] = &data; }
            { let second: &[u32] = &data; }
        }
        "#,
        32,
    );
}

#[test]
fn moves_transfer_one_charge() {
    exact_peak(
        "moves_transfer_one_charge",
        r#"
        struct Data { values: [u32; 4] }
        fn f() mem_peak <= BUDGET {
            let first = Data { values: [0u32; 4] };
            let second = first;
            let third = second;
        }
        "#,
        16,
    );
}

#[test]
fn scopes_allow_reuse_after_moves() {
    exact_peak(
        "scopes_allow_reuse_after_moves",
        r#"
        struct Data { values: [u32; 4] }
        fn f() mem_peak <= BUDGET {
            { let first = Data { values: [0u32; 4] }; let moved = first; }
            { let second = Data { values: [0u32; 4] }; let moved = second; }
        }
        "#,
        16,
    );
}

#[test]
fn iteration_count_does_not_multiply_workspace() {
    exact_peak(
        "iteration_count_does_not_multiply_workspace",
        r#"
        fn f() mem_peak <= BUDGET {
            let mut i = 0usize;
            while i < 100
                invariant i <= 100,
                decreases 100 - i,
            {
                let workspace = [0u32; 4];
                i += 1;
            }
        }
        "#,
        24,
    );
}

#[test]
fn unreachable_storage_does_not_contribute() {
    exact_peak(
        "unreachable_storage_does_not_contribute",
        r#"
        fn f() mem_peak <= BUDGET {
            if false { let workspace = [0u32; 8]; }
        }
        "#,
        0,
    );
}

#[test]
fn standalone_aggregate_results_are_reused() {
    exact_peak(
        "standalone_aggregate_results_are_reused",
        r#"
        fn f() mem_peak <= BUDGET {
            [0u32; 4];
            [0u32; 8];
        }
        "#,
        32,
    );
}

#[test]
fn zero_sized_values_still_have_sized_references() {
    exact_peak(
        "zero_sized_values_still_have_sized_references",
        r#"
        struct Empty;
        fn f() mem_peak <= BUDGET {
            let empty = Empty;
            let reference = &empty;
        }
        "#,
        8,
    );
}

#[test]
fn local_destination_is_reserved_during_initializer_calls() {
    exact_peak(
        "local_destination_is_reserved_during_initializer_calls",
        r#"
        struct Data { values: [u32; 4], finished: () }
        fn helper() mem_peak <= 32 { let workspace = [0u32; 8]; }
        fn f() mem_peak <= BUDGET {
            let data = Data { finished: helper(), values: [0u32; 4] };
        }
        "#,
        48,
    );
}
