use super::support::{rejects, verifies};
use crate::common::*;
use crate::verify_one_file;

#[test]
fn append_only_scalar_loops_retain_the_final_slots() {
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
        // The handle, final occupied slots, counter and scratch are live together.
        let peak = 24 + (length + 2) * 4 + 1 + 128;
        verifies(&format!("scalar_loop_backing_{name}"), &code.replace("BOUND", &peak.to_string()));
        rejects(
            &format!("scalar_loop_backing_{name}_short"),
            &code.replace("BOUND", &(peak - 1).to_string()),
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
    verifies(
        "removed_scalar_loop_backing",
        &code.replace("CHECK", "assert(current(memory) <= 29);"),
    );
    // The original four-byte reservation survives both pops.
    rejects(
        "removed_scalar_loop_backing_short",
        &code.replace("CHECK", "assert(current(memory) <= 28);"),
        "memory budget exceeded",
    );
}

#[test]
fn growth_policy_covers_element_sizes() {
    verifies(
        "byte_growth",
        "fn f() resources peak(memory) <= 25 { let mut v = Vec::<u8>::new(); v.push(1); }",
    );
    rejects(
        "byte_growth_short",
        "fn f() resources peak(memory) <= 24 { let mut v = Vec::<u8>::new(); v.push(1); }",
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
fn enclosing_vector_charges_each_section_for_its_added_slots() {
    let code = "fn f() resources peak(memory) <= FUNCTION {
        let mut v = Vec::<u32>::new();
        resources peak(memory) <= FIRST { v.push(1); }
        resources peak(memory) <= MIDDLE { v.push(2); v.push(3); v.push(4); }
        resources peak(memory) <= NEXT { v.push(5); }
        assert(current(memory) <= LIVE);
    }";
    // Each section starts from the outer vector's current charge.
    let case = |parent, first, middle, next, live| {
        code.replace("FUNCTION", parent)
            .replace("FIRST", first)
            .replace("MIDDLE", middle)
            .replace("NEXT", next)
            .replace("LIVE", live)
    };
    verifies("section_vector_slots", &case("44", "4", "12", "4", "44"));
    for (name, code) in [
        ("first", case("44", "3", "12", "4", "44")),
        ("middle", case("44", "4", "11", "4", "44")),
        ("next", case("44", "4", "12", "3", "44")),
        ("function", case("43", "4", "12", "4", "44")),
        ("retained", case("44", "4", "12", "4", "43")),
    ] {
        rejects(&format!("section_growth_{name}"), &code, "memory budget exceeded");
    }
}

#[test]
fn an_input_length_funds_one_output_slot_per_iteration() {
    let code = "fn collect(packed: &[u8], n: u16) -> Vec<u32>
        requires packed.len() == n,
        resources peak(memory) <= ref_size(packed) + value_size(n) + value_size(Vec<u32>)
            + value_size(u16) + n * value_size(u32),
    {
        let mut result = Vec::new();
        resources peak(memory) <= value_size(u16) + packed.len() * value_size(u32) {
            let mut i = 0u16;
            while i < n invariant i <= n, result.len() == i, packed.len() == n, decreases n - i, {
                result.push(1u32); i += 1;
            }
            EXTRA
        }
        result
    }";
    verifies("symbolic_output_slots", &code.replace("EXTRA", ""));
    rejects(
        "symbolic_extra_slot",
        &code.replace("EXTRA", "result.push(2u32);"),
        "memory budget exceeded",
    );
}

#[test]
fn nested_section_retains_growth_on_each_path() {
    let code = "fn f(grow: bool) resources peak(memory) <= 45 {
        let mut v = Vec::<u32>::new();
        resources peak(memory) <= 20 {
            if grow { resources peak(memory) <= 4 { v.push(1); } }
            let scratch = [0u8; 16];
            assert(current(memory) <= LIMIT);
        }
        if grow { assert(current(memory) <= 29); }
        else { assert(current(memory) <= 25); }
    }";
    verifies("nested_section_conditional_growth", &code.replace("LIMIT", "20"));
    rejects("nested_section_growth_short", &code.replace("LIMIT", "19"), "memory budget exceeded");
}

#[test]
fn breaking_out_of_a_section_keeps_the_vectors_new_backing() {
    let code = "fn f(grow: bool) resources peak(memory) <= 29 {
        let mut v = Vec::<u32>::new();
        loop decreases 1int, {
            resources peak(memory) <= 4 {
                if grow { v.push(1); break; }
            }
            break;
        }
        if grow { assert(current(memory) <= LIMIT); }
        else { assert(current(memory) <= 25); }
    }";
    verifies("section_growth_break", &code.replace("LIMIT", "29"));
    rejects("section_growth_break_short", &code.replace("LIMIT", "28"), "memory budget exceeded");
}

#[test]
fn splitting_a_streaming_loop_retains_the_staged_blocks() {
    const STREAMING_PEAK: u64 = 130;
    const STAGED_PEAK: u64 = 674;
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
        &format!("fn f(flag: bool) resources peak(memory) <= 53 {body}"),
    );
    rejects(
        "branch_growth_exceeds",
        &format!("fn f(flag: bool) resources peak(memory) <= 52 {body}"),
        "memory budget exceeded",
    );
}

#[test]
fn drop_releases_the_handle_and_pop_releases_an_unreserved_slot() {
    verifies(
        "grown_drop",
        "fn f() resources peak(memory) <= 64 { let mut v = Vec::<u32>::new(); v.push(1); drop(v); let scratch = [0u8; 64]; }",
    );
    verifies(
        "grown_pop",
        "fn f() resources peak(memory) <= 56 { let mut v = Vec::<u32>::new(); v.push(1); v.pop(); let scratch = [0u8; 32]; }",
    );
}

test_verify_one_file! {
    #[test] four_pushes_occupy_four_slots verus_code! {
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
        fn f() resources peak(memory) <= 48 {
            let mut v = Vec::<u32>::new();
            append(&mut v);
            let scratch = [0u8; 21];
        }
    } => Err(err) => assert_vir_error_msg(err, "memory budget exceeded")
}

#[test]
fn successive_helper_pushes_accumulate_and_pops_release_only_unreserved_slots() {
    let program = "fn append(v: &mut Vec<u32>)
        ensures final(v).len() == old(v).len() + 1,
        resources peak(memory) <= ref_size(v) + value_size(u32),
    { v.push(7); }
    fn f() resources peak(memory) <= 64 {
        let mut values = Vec::<u32>::with_capacity(1);
        append(&mut values); append(&mut values); append(&mut values);
        assert(current(memory) <= THREE);
        values.pop(); values.pop(); values.pop();
        assert(current(memory) <= ONE);
    }";
    let case = |three, one| program.replace("THREE", three).replace("ONE", one);
    verifies("helper_slots", &case("36", "28"));
    rejects("helper_third_slot", &case("35", "28"), "memory budget exceeded");
    rejects("helper_reserved_slot", &case("36", "27"), "memory budget exceeded");
}

#[test]
fn removing_an_owned_element_through_a_helper_releases_its_slot() {
    let source = "fn take(v: &mut Vec<Box<u8>>) -> Box<u8>
        requires old(v).len() == 2, ensures final(v).len() == 1,
        resources peak(memory) <= 32,
    { v.remove(0) }
    fn run() resources peak(memory) <= 96 {
        let mut v = Vec::<Box<u8>>::new();
        v.push(Box::new(1u8)); v.push(Box::new(2u8));
        let first = take(&mut v); drop(first);
        assert(current(memory) <= LIVE);
    }";
    // The vector handle, one Box handle and the boxed byte survive the call.
    verifies("helper_removed_slot", &source.replace("LIVE", "33"));
    rejects("helper_surviving_slot", &source.replace("LIVE", "32"), "memory budget exceeded");
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
    #[test] growth_counts_two_occupied_slots verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 32 {
            let mut v = Vec::<u32>::with_capacity(1);
            v.push(1); v.push(2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] second_slot_exceeds_budget verus_code! {
        use vstd::prelude::*;
        fn f() resources peak(memory) <= 31 {
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
