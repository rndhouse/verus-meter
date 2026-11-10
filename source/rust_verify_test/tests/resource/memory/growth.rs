use super::support::{rejects, verifies};
use crate::common::*;

#[test]
fn growth_policy_covers_element_sizes() {
    verifies(
        "byte_growth",
        "fn f() resources peak(memory) <= 32 { let mut v = Vec::<u8>::new(); v.push(1); }",
    );
    rejects(
        "byte_growth_short",
        "fn f() resources peak(memory) <= 31 { let mut v = Vec::<u8>::new(); v.push(1); }",
        "memory budget exceeded",
    );
    verifies(
        "large_element_growth",
        "fn f() resources peak(memory) <= 2072 { let mut v = Vec::<[u8; 2048]>::new(); v.push([0u8; 2048]); }",
    );
}

test_verify_one_file! {
    #[test] vector_changes_in_arguments_require_explicit_order verus_code! {
        use vstd::prelude::*;
        fn side(v: &mut Vec<u32>) -> (result: u32)
            requires old(v).len() == 0,
            ensures final(v).len() == 1,
            resources peak(memory) <= 28,
        { v.push(1); 0 }
        fn f() resources peak(memory) <= 128 {
            let mut a = Vec::<u32>::new();
            let mut b = Vec::<u32>::new();
            a.push(side(&mut b));
        }
    } => Err(err) => assert_vir_error_msg(err, "bind the argument first")
}

test_verify_one_file! {
    #[test] section_growth_is_local verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 40 {
            resources peak(memory) <= 40 {
                let mut v = Vec::<u32>::new();
                v.push(1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] section_cannot_hide_growth_of_enclosing_owner verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 64 {
            let mut v = Vec::<u32>::new();
            resources peak(memory) <= 40 { v.push(1); }
        }
    } => Err(err) => assert_vir_error_msg(err, "vector capacity exceeded")
}

#[test]
fn growth_example_compiles() {
    crate::verify_one_file(
        "vector_growth_example",
        include_str!("../../../../../examples/resource/memory/vectors/vector_growth.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

#[test]
fn branch_growth_retains_the_larger_buffer() {
    let body = "{ let mut v = Vec::<u32>::with_capacity(1); v.push(1); if flag { v.push(2); } let scratch = [0u8; 20]; }";
    verifies(
        "branch_growth_fits",
        &format!("fn f(flag: bool) resources peak(memory) <= 61 {body}"),
    );
    rejects(
        "branch_growth_exceeds",
        &format!("fn f(flag: bool) resources peak(memory) <= 60 {body}"),
        "memory budget exceeded",
    );
}

#[test]
fn grown_buffer_releases_on_drop_and_retains_on_pop() {
    verifies(
        "grown_drop",
        "fn f() resources peak(memory) <= 64 { let mut v = Vec::<u32>::new(); v.push(1); drop(v); let scratch = [0u8; 64]; }",
    );
    rejects(
        "grown_pop",
        "fn f() resources peak(memory) <= 64 { let mut v = Vec::<u32>::new(); v.push(1); v.pop(); let scratch = [0u8; 32]; }",
        "memory budget exceeded",
    );
}

test_verify_one_file! {
    #[test] new_spare_capacity_is_reused verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 40 {
            let mut v = Vec::<u32>::new();
            v.push(1); v.push(2); v.push(3); v.push(4);
            assert(v.len() == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] helper_retention_is_charged_after_call verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>)
            requires old(v).len() == 0,
            ensures final(v).len() == 1,
            resources peak(memory) <= 24,
        { v.push(1); }
        fn f() resources peak(memory) <= 55 {
            let mut v = Vec::<u32>::new();
            append(&mut v);
            let scratch = [0u8; 8];
        }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded")
}

test_verify_one_file! {
    #[test] nested_growing_helpers verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>)
            requires old(v).len() < 2,
            ensures final(v).len() == old(v).len() + 1,
            resources peak(memory) <= 24,
        { v.push(1); }
        fn forward(v: &mut Vec<u32>)
            requires old(v).len() < 2,
            ensures final(v).len() == old(v).len() + 1,
            resources peak(memory) <= 32,
        { append(v); }
        fn f() resources peak(memory) <= 96 {
            let mut v = Vec::<u32>::new();
            forward(&mut v); forward(&mut v);
            assert(v.len() == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] growing_owned_input_and_fresh_return verus_code! {
        use vstd::prelude::*;
        fn make() -> (v: Vec<u32>) ensures v.len() == 1, resources peak(memory) <= 40 {
            let mut v = Vec::<u32>::new(); v.push(1); v
        }
        fn append(mut v: Vec<u32>) -> (result: Vec<u32>)
            requires v.len() == 1,
            ensures result.len() == 2,
            resources peak(memory) <= 40,
        { v.push(2); v }
        fn f() resources peak(memory) <= 128 {
            let v = make();
            let mut v = append(v);
            v.push(3);
            assert(v.len() == 3);
            drop(v);
            let scratch = [0u8; 128];
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] growing_helpers_in_a_loop verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>)
            requires old(v).len() < 4,
            ensures final(v).len() == old(v).len() + 1,
            resources peak(memory) <= 40,
        { v.push(1); }
        fn f() resources peak(memory) <= 112 {
            let mut v = Vec::<u32>::new();
            while v.len() < 4
                invariant v.len() <= 4,
                decreases 4 - v.len(),
            { append(&mut v); }
            assert(v.len() == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] empty_vector_can_grow verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 40 {
            let mut v = Vec::<u32>::new();
            v.push(7);
            assert(v.len() == 1 && v[0] == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] growth_counts_both_buffers verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 44 {
            let mut v = Vec::<u32>::with_capacity(1);
            v.push(1); v.push(2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] growth_overlap_exceeds_budget verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 43 {
            let mut v = Vec::<u32>::with_capacity(1);
            v.push(1); v.push(2);
        }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded")
}

test_verify_one_file! {
    #[test] loop_growth verus_code! {
        use vstd::prelude::*;
        fn f(n: usize) requires n <= 8,
            resources peak(memory) <= 32 + 32 + 16 * n,
        {
            let mut v = Vec::<u32>::new();
            while v.len() < n
                invariant v.len() <= n, n <= 8,
                decreases n - v.len(),
            { v.push(1); }
            assert(v.len() == n);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] helper_growth_is_retained verus_code! {
        use vstd::prelude::*;
        fn append(v: &mut Vec<u32>)
            requires old(v).len() == 0,
            ensures final(v).len() == 1,
            resources peak(memory) <= 24,
        { v.push(1); }
        fn f() resources peak(memory) <= 64 {
            let mut v = Vec::<u32>::new();
            append(&mut v);
            v.push(2);
            assert(v.len() == 2);
        }
    } => Ok(())
}
