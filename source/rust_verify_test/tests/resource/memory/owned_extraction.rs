//! Incoming allocations retain separate lifetimes after an owned extraction.

use super::support::{rejects, verifies};

#[test]
fn returned_child_outlives_the_owned_input_collection() {
    let code = "fn take(mut v: Vec<Vec<u32>>, i: usize) -> (r: Vec<u32>)
        requires i < v.len(),
        ensures r == v[i as int],
        resources peak(memory) <= 56 { v.remove(i) }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            let mut child = take(v, 0); child.push(7); let scratch = [0u8;256];
        }";
    verifies("owned_result", &code.replace("BOUND", "296"));
    rejects("owned_result_short", &code.replace("BOUND", "295"), "memory budget exceeded");
}

#[test]
fn original_child_remains_charged_after_parent_drop_inside_helper() {
    let code = "fn take(mut v: Vec<Box<[u8;32]>>) -> (r: Box<[u8;32]>)
        requires v.len() == 1,
        resources peak(memory) <= 264 {
            let child = v.remove(0); drop(v); let scratch = [0u8;256]; child
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(1);
            let child = Box::new([0u8;32]); v.push(child);
            let child = take(v);
        }";
    verifies("owned_helper_peak", &code.replace("BOUND", "296"));
    rejects("owned_helper_peak_short", &code.replace("BOUND", "295"), "memory budget exceeded");
}

#[test]
fn dropping_the_child_preserves_only_the_remaining_input_lifetimes() {
    for (name, result, release, tail, helper, bound) in [
        ("remaining", "Vec<Box<[u8;32]>>", "", "v", 280, 328),
        ("neither", "()", "drop(v);", "", 256, 256),
    ] {
        let code = format!(
            "fn take(mut v: Vec<Box<[u8;32]>>) -> {result}
                requires v.len() == 2,
                resources peak(memory) <= {helper} {{
                    let child = v.remove(0); drop(child); {release}
                    let scratch = [0u8;256]; {tail}
                }}
                fn f() resources peak(memory) <= BOUND {{
                    let mut v = Vec::<Box<[u8;32]>>::with_capacity(2);
                    let a = Box::new([0u8;32]); v.push(a);
                    let b = Box::new([1u8;32]); v.push(b);
                    let result = take(v);
                }}"
        );
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn repeated_removal_splits_the_reindexed_remainder() {
    let code = "fn take(mut v: Vec<Vec<u32>>) -> Vec<u32>
        requires v.len() == 2,
        resources peak(memory) <= 280 {
            let first = v.remove(0); drop(first);
            let second = v.remove(0); drop(v); let scratch = [0u8;256]; second
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            let result = take(v);
        }";
    // Different child extents distinguish the shifted survivor from the first
    // child: only its 32-byte buffer overlaps the helper's final workspace.
    verifies("reindexed_regions", &code.replace("BOUND", "312"));
    rejects("reindexed_regions_short", &code.replace("BOUND", "311"), "memory budget exceeded");
}

#[test]
fn extracted_fixed_children_have_independent_input_lifetimes() {
    let code = "struct Child { data: Box<[u8;32]>, tag: Box<[u8;64]>, }
        fn take(mut v: Vec<Child>) -> Box<[u8;32]>
            requires v.len() == 1,
            resources peak(memory) <= 272 {
                let child = v.remove(0); drop(v); drop(child.tag);
                { let scratch = [0u8;256]; }
                child.data
            }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Child>::with_capacity(1);
            let child = Child { data: Box::new([0u8;32]), tag: Box::new([0u8;64]) };
            v.push(child); let result = take(v);
        }";
    verifies("fixed_regions", &code.replace("BOUND", "304"));
    rejects("fixed_regions_short", &code.replace("BOUND", "303"), "memory budget exceeded");
}

#[test]
fn lifetime_regions_follow_nested_runtime_ownership() {
    for (name, parameter, extraction, argument) in [
        (
            "extracted_collection",
            "Vec<Vec<Box<[u8;32]>>>",
            "let mut row = v.remove(0); let child = row.remove(0); drop(row);",
            "rows",
        ),
        (
            "nested_receiver",
            "Box<Vec<Vec<Box<[u8;32]>>>>",
            "let child = v[0].remove(0);",
            "Box::new(rows)",
        ),
    ] {
        let code = format!(
            "fn take(mut v: {parameter}) -> Box<[u8;32]>
                requires v.len() == 1, v[0].len() == 1,
                resources peak(memory) <= 264 {{
                    {extraction} drop(v); let scratch = [0u8;256]; child
                }}
                fn f() resources peak(memory) <= BOUND {{
                    let mut rows = Vec::<Vec<Box<[u8;32]>>>::with_capacity(1);
                    let mut row = Vec::<Box<[u8;32]>>::with_capacity(1);
                    let child = Box::new([0u8;32]); row.push(child); rows.push(row);
                    let v = {argument}; let result = take(v);
                }}"
        );
        verifies(name, &code.replace("BOUND", "296"));
        rejects(&format!("{name}_short"), &code.replace("BOUND", "295"), "memory budget exceeded");
    }
}

#[test]
fn extraction_keeps_new_charges_separate_from_original_input_regions() {
    let code = "fn take(mut v: Vec<Vec<[u8;32]>>) -> (r: Vec<[u8;32]>)
        requires v.len() == 1, v[0].len() == 0,
        ensures r.len() == 1,
        resources peak(memory) <= 408 {
            v[0].push([0u8;32]); let child = v.remove(0); drop(v);
            let scratch = [0u8;256]; child
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<[u8;32]>>::with_capacity(1);
            let child = Vec::<[u8;32]>::new(); v.push(child);
            let result = take(v); AFTER
        }";
    // The call allowance can overlap the original 24-byte outer buffer. The
    // new 128-byte child buffer must not also appear in an input region. After
    // the call, that buffer remains owned by the returned 24-byte vector.
    for (name, after, bound) in
        [("new_charges_during", "", 432), ("new_charges_after", "let scratch = [0u8;512];", 664)]
    {
        let code = code.replace("AFTER", after);
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn unsupported_owned_region_transfers_reject_generous_budgets() {
    for (name, body, message) in [
        (
            "replacement",
            "v[0] = Box::new(7u32); v.remove(0);",
            "owned incoming extraction after indexed replacement",
        ),
        (
            "conditional_replacement",
            "if take { v[0] = Box::new(7u32); } v.remove(0);",
            "owned incoming extraction after indexed replacement",
        ),
        (
            "branch",
            "if take { v.remove(0); }",
            "moving or dropping an enclosing heap owner across a branch, loop, or memory section",
        ),
        (
            "loop",
            "while v.len() > 0 invariant true, decreases v.len(), { v.remove(0); }",
            "moving or dropping an enclosing heap owner across a branch, loop, or memory section",
        ),
    ] {
        rejects(
            name,
            &format!(
                "fn f(mut v: Vec<Box<u32>>, take: bool) resources peak(memory) <= 10000 {{ {body} }}"
            ),
            message,
        );
    }
}
