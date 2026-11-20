use super::support::{rejects, verifies};
use crate::common::*;
use crate::verify_one_file;

#[test]
fn append_only_scalar_loops_retain_the_last_replacement() {
    for (name, constructor, first, length) in
        [("empty", "new()", "", 0), ("nonempty", "with_capacity(1)", "values.push(1);", 1)]
    {
        let code = format!(
            "fn f() resources peak(memory) <= BOUND {{
                let mut values = Vec::<u32>::{constructor}; {first}
                let mut i = 0u8;
                while i < 2
                    invariant i <= 2, values.len() == {length} + i as int,
                    decreases 2-i,
                {{ values.push(2); i += 1; }}
                assert(current(memory) <= 41);
                let scratch = [0u8;128];
            }}"
        );
        // Handle 24 + grown backing 16 + counter 1 + scratch 128.
        verifies(&format!("scalar_loop_backing_{name}"), &code.replace("BOUND", "169"));
        rejects(
            &format!("scalar_loop_backing_{name}_short"),
            &code.replace("BOUND", "168"),
            "memory budget exceeded",
        );
    }
}

#[test]
fn removal_keeps_backing_when_the_new_length_fits_the_initial_capacity() {
    let code = "fn f() resources peak(memory) <= 1024 {
        let mut values = Vec::<u32>::with_capacity(1);
        values.push(1); values.push(2); values.pop(); values.pop();
        let mut i = 0u8;
        while i < 1 invariant i <= 1, values.len() == i as int, decreases 1-i, {
            values.push(3); i += 1;
        }
        CHECK
    }";
    verifies("removed_scalar_loop_backing", &code.replace("CHECK", ""));
    // The emptying pops retained the 16-byte grown buffer. A one-element
    // final length cannot restore its original four-byte allocation.
    rejects(
        "removed_scalar_loop_backing_short",
        &code.replace("CHECK", "assert(current(memory) <= 29);"),
        "memory budget exceeded",
    );
}

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

#[test]
fn enclosing_vector_growth_is_charged_at_replacement_and_retained_by_its_owner() {
    let code = "fn f() resources peak(memory) <= FUNCTION {
        let mut v = Vec::<u32>::new();
        resources peak(memory) <= FIRST { v.push(1); }
        resources peak(memory) <= 0 { v.push(2); v.push(3); v.push(4); }
        resources peak(memory) <= NEXT { v.push(5); }
        assert(current(memory) <= LIVE);
    }";
    // The 24-byte handle stays in the function. At the second growth, its
    // 16-byte buffer overlaps a 32-byte replacement; only the latter survives.
    let case = |parent, first, next, live| {
        code.replace("FUNCTION", parent)
            .replace("FIRST", first)
            .replace("NEXT", next)
            .replace("LIVE", live)
    };
    verifies("section_vector_replacement", &case("72", "16", "32", "56"));
    for (name, code) in [
        ("first", case("72", "15", "32", "56")),
        ("next", case("72", "16", "31", "56")),
        ("overlap", case("71", "16", "32", "56")),
        ("retained", case("72", "16", "32", "55")),
    ] {
        rejects(&format!("section_growth_{name}"), &code, "memory budget exceeded");
    }
}

#[test]
fn nested_section_retains_growth_on_each_path() {
    let code = "fn f(grow: bool) resources peak(memory) <= 57 {
        let mut v = Vec::<u32>::new();
        resources peak(memory) <= 32 {
            if grow { resources peak(memory) <= 16 { v.push(1); } }
            let scratch = [0u8; 16];
            assert(current(memory) <= LIMIT);
        }
        if grow { assert(current(memory) <= 41); }
        else { assert(current(memory) <= 25); }
    }";
    verifies("nested_section_conditional_growth", &code.replace("LIMIT", "32"));
    rejects("nested_section_growth_short", &code.replace("LIMIT", "31"), "memory budget exceeded");
}

#[test]
fn breaking_out_of_a_section_keeps_the_vectors_new_backing() {
    let code = "fn f(grow: bool) resources peak(memory) <= 41 {
        let mut v = Vec::<u32>::new();
        loop decreases 1int, {
            resources peak(memory) <= 16 {
                if grow { v.push(1); break; }
            }
            break;
        }
        if grow { assert(current(memory) <= LIMIT); }
        else { assert(current(memory) <= 25); }
    }";
    verifies("section_growth_break", &code.replace("LIMIT", "41"));
    rejects("section_growth_break_short", &code.replace("LIMIT", "40"), "memory budget exceeded");
}

#[test]
fn splitting_a_streaming_loop_retains_the_staged_blocks() {
    const STREAMING_PEAK: u64 = 184;
    const STAGED_PEAK: u64 = 937;
    let stream = "for byte in packed {
        let block = [*byte; 128];
        output.push(block[0]);
    }";
    let stage = "let mut staged = Vec::new();
        for byte in packed {
            let block = [*byte; 128];
            staged.push(block);
        }
        for block in staged { output.push(block[0]); }";
    let program = |body, peak| {
        format!("fn collect(input: [u8; 2]) -> Vec<u8>
        resources peak(memory) <= value_size(input) + ref_size(&[u8]) + value_size(Vec<u8>) + {peak},
    {{
        let packed: &[u8] = &input;
        let mut output = Vec::new();
        resources peak(memory) <= {peak} {{ {body} }}
        output
    }}")
    };
    verifies("streaming_blocks", &program(stream, STREAMING_PEAK));
    verifies("staged_blocks", &program(stage, STAGED_PEAK));
    let source = format!("use vstd::prelude::*; verus! {{ {} }}", program(stage, STREAMING_PEAK));
    let err = verify_one_file("staged_over_streaming_peak", source, &[]).unwrap_err();
    assert_any_vir_error_msg(err, "memory budget exceeded");
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
