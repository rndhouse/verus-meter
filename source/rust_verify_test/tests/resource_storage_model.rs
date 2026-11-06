#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Boundary checks for the remaining model policies, independent of the examples.
fn exact_peak(name: &str, code: &str, peak: u64) {
    let source = |budget| {
        format!(
            "use vstd::prelude::*; verus! {{ {} }}",
            code.replace("BUDGET", &format!("{budget}u64")),
        )
    };
    verify_one_file(name, source(peak), &[]).unwrap();
    if peak > 0 {
        let err = verify_one_file(&format!("{name}_short"), source(peak - 1), &[]).unwrap_err();
        assert_vir_error_msg(err, &format!("peak {peak} bytes exceeds budget {} bytes", peak - 1));
    }
}

#[test]
fn fixed_size_policy_and_unpadded_fields() {
    exact_peak(
        "fixed_size_policy_and_unpadded_fields",
        r#"
        struct Small { n: u32, ready: bool }
        fn f(empty: (), flag: bool, n: u32, index: usize, reference: &u32,
             slice: &[u32], array: [u32; 3], record: Small)
            resources peak_memory_bytes <= BUDGET {}
        "#,
        54,
    );
}

#[test]
fn two_borrows_do_not_duplicate_the_backing_array() {
    exact_peak(
        "two_borrows_do_not_duplicate_the_backing_array",
        r#"
        fn leaf(a: &[u32], b: &[u32]) resources peak_memory_bytes <= 32 {}
        fn f() resources peak_memory_bytes <= BUDGET {
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
        fn f() resources peak_memory_bytes <= BUDGET {
            let data = [0u32; 4];
            { let first: &[u32] = &data; }
            { let second: &[u32] = &data; }
        }
        "#,
        32,
    );
}

#[test]
fn moved_slots_remain_charged_until_scope_exit() {
    exact_peak(
        "moved_slots_remain_charged_until_scope_exit",
        r#"
        struct Data { values: [u32; 4] }
        fn f() resources peak_memory_bytes <= BUDGET {
            let first = Data { values: [0u32; 4] };
            let second = first;
            let third = second;
        }
        "#,
        48,
    );
}

#[test]
fn scopes_allow_reuse_after_moves() {
    exact_peak(
        "scopes_allow_reuse_after_moves",
        r#"
        struct Data { values: [u32; 4] }
        fn f() resources peak_memory_bytes <= BUDGET {
            { let first = Data { values: [0u32; 4] }; let moved = first; }
            { let second = Data { values: [0u32; 4] }; let moved = second; }
        }
        "#,
        32,
    );
}

#[test]
fn iteration_count_does_not_multiply_workspace() {
    exact_peak(
        "iteration_count_does_not_multiply_workspace",
        r#"
        fn f() resources peak_memory_bytes <= BUDGET {
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
fn constant_conditions_do_not_prune_the_structural_bound() {
    exact_peak(
        "constant_conditions_do_not_prune_the_structural_bound",
        r#"
        fn f() resources peak_memory_bytes <= BUDGET {
            if false { let workspace = [0u32; 8]; }
        }
        "#,
        32,
    );
}

#[test]
fn standalone_aggregate_results_are_reused() {
    exact_peak(
        "standalone_aggregate_results_are_reused",
        r#"
        fn f() resources peak_memory_bytes <= BUDGET {
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
        fn f() resources peak_memory_bytes <= BUDGET {
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
        fn helper() resources peak_memory_bytes <= 32 { let workspace = [0u32; 8]; }
        fn f() resources peak_memory_bytes <= BUDGET {
            let data = Data { finished: helper(), values: [0u32; 4] };
        }
        "#,
        48,
    );
}
