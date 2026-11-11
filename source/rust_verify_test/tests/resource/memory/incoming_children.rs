//! Incoming children retain caller charges; indexed loans track only new local
//! allocations and export complete ownership changes through checked templates.

use super::support::{rejects, verifies};

#[test]
fn local_charge_zero_does_not_mean_the_incoming_buffer_is_empty() {
    let code = "fn twice(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 1, old(v)[0].len() == 0,
        ensures final(v).len() == 1, final(v)[0].len() == 2,
        resources peak(memory) <= HELPER {
            v[0].push(1); v[0].push(2);
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::with_capacity(1); v.push(child);
            twice(&mut v); let scratch = [0u8;128];
        }";
    verifies("incoming_capacity", &code.replace("HELPER", "40").replace("BOUND", "192"));
    rejects(
        "incoming_capacity_short",
        &code.replace("HELPER", "40").replace("BOUND", "191"),
        "memory budget exceeded",
    );
    // The first append may use one caller-provided slot. It must not establish
    // the four-slot growth floor merely because this frame started at zero bytes.
    rejects(
        "incoming_capacity_not_exact",
        &code.split("fn f()").next().unwrap().replace("HELPER", "24"),
        "memory budget exceeded",
    );
}

#[test]
fn fixed_and_repeated_ownership_paths_share_the_same_loan_rules() {
    for (name, declarations, typ, selected, shape, make, retained) in [
        (
            "boxed_children",
            "",
            "Box<Vec<Box<Vec<u32>>>>",
            "v[0]",
            "v.len() == 1",
            "let mut values = Vec::<Box<Vec<u32>>>::with_capacity(1);
             let child = Box::new(Vec::<u32>::new()); values.push(child);
             let mut v = Box::new(values);",
            80,
        ),
        (
            "boxed_slice_children",
            "",
            "Box<[Box<Vec<u32>>]>",
            "v[0]",
            "v.len() == 1",
            "let mut values = Vec::<Box<Vec<u32>>>::with_capacity(1);
             let child = Box::new(Vec::<u32>::new()); values.push(child);
             let mut v = values.into_boxed_slice();",
            64,
        ),
        (
            "struct_children",
            "struct Child { value: Box<Vec<u32>>, tag: Box<[u8;16]>, }
             struct Parent { values: Vec<Child>, tag: Box<[u8;32]>, }",
            "Parent",
            "v.values[0].value",
            "v.values.len() == 1",
            "let mut values = Vec::<Child>::with_capacity(1);
             let child = Child { value: Box::new(Vec::<u32>::new()), tag: Box::new([0u8;16]) };
             values.push(child);
             let mut v = Parent { values, tag: Box::new([0u8;32]) };",
            136,
        ),
    ] {
        // Each helper delegates to an ordinary leaf helper. The same fixed and
        // runtime path resolution must govern the loan, mutation, and summary.
        let before = selected.replacen("v", "old(v)", 1);
        let after = selected.replacen("v", "final(v)", 1);
        let old_shape = shape.replacen("v", "old(v)", 1);
        let new_shape = shape.replacen("v", "final(v)", 1);
        let code = format!(
            "{declarations}
            fn leaf(v: &mut Vec<u32>)
                requires old(v).len() == 0, ensures final(v).len() == 1,
                resources peak(memory) <= 24 {{ v.push(1); }}
            fn grow(v: &mut {typ})
                requires {old_shape}, {before}.len() == 0,
                ensures {new_shape}, {after}.len() == 1,
                resources peak(memory) <= 128 {{ leaf(&mut {selected}); }}
            fn f() resources peak(memory) <= BOUND {{
                {make}
                grow(&mut v); {selected}.push(2);
                let scratch = [0u8;256];
            }}"
        );
        verifies(name, &code.replace("BOUND", &(retained + 256).to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(retained + 255).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn nested_runtime_children_are_not_charged_twice() {
    let code = "fn grow(v: &mut Vec<Vec<Vec<u32>>>)
        requires old(v).len() == 1, old(v)[0].len() == 1, old(v)[0][0].len() == 0,
        ensures final(v).len() == 1, final(v)[0].len() == 1, final(v)[0][0].len() == 1,
        resources peak(memory) <= 24 { v[0][0].push(1); }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<Vec<u32>>>::with_capacity(1);
            let mut row = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::new(); row.push(child); v.push(row);
            grow(&mut v); let scratch = [0u8;256];
        }";
    verifies("nested_incoming", &code.replace("BOUND", "344"));
    rejects("nested_incoming_short", &code.replace("BOUND", "343"), "memory budget exceeded");
}

#[test]
fn leaf_removal_exports_shape_changes_without_releasing_the_buffer() {
    let code = "fn pop(v: &mut Vec<u32>)
        requires old(v).len() == 1, ensures final(v).len() == 0,
        resources peak(memory) <= 16 { v.pop(); }
        fn shrink(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 1, old(v)[0].len() == 1,
        ensures final(v).len() == 1, final(v)[0].len() == 0,
        resources peak(memory) <= 24 { pop(&mut v[0]); }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let mut child = Vec::<u32>::with_capacity(8); child.push(1); v.push(child);
            shrink(&mut v); v[0].push(2); let scratch = [0u8;128];
        }";
    verifies("incoming_leaf_removal", &code.replace("BOUND", "208"));
    rejects("incoming_leaf_removal_short", &code.replace("BOUND", "207"), "memory budget exceeded");
}

#[test]
fn incoming_indexed_loans_in_loops_remain_unsupported() {
    rejects(
        "incoming_loop",
        "fn f(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 1,
        resources peak(memory) <= 10000 {
            let mut i = 0usize;
            while i < 2 invariant i <= 2, v.len() == 1, decreases 2-i, {
                let n = v[0].len(); i += 1;
            }
        }",
        "indexed incoming children inside loops",
    );
}

#[test]
fn owned_inputs_keep_their_provenance_when_mutated_and_returned() {
    let code = "fn grow(mut v: Vec<Vec<u32>>) -> (r: Vec<Vec<u32>>)
        requires v.len() == 1, v[0].len() == 0,
        ensures r.len() == 1, r[0].len() == 1,
        resources peak(memory) <= 40 { v[0].push(1); v }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::new(); v.push(child);
            let result = grow(v); let scratch = [0u8;128];
        }";
    verifies("owned_incoming_child", &code.replace("BOUND", "192"));
    rejects("owned_incoming_child_short", &code.replace("BOUND", "191"), "memory budget exceeded");
}

#[test]
fn replacing_an_incoming_child_releases_its_old_storage_after_the_call() {
    let code = "fn replace(v: &mut Vec<Box<Vec<u32>>>)
        requires old(v).len() == 1,
        ensures final(v).len() == 1, final(v)[0].len() == 0,
        resources peak(memory) <= 72 {
            let buffer = Vec::<u32>::with_capacity(2); v[0] = Box::new(buffer);
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<Vec<u32>>>::with_capacity(1);
            let child = Box::new(Vec::<u32>::with_capacity(64)); v.push(child);
            replace(&mut v); v[0].push(1); let scratch = [0u8;512];
        }";
    verifies("replace_incoming_child", &code.replace("BOUND", "576"));
    rejects(
        "replace_incoming_child_short",
        &code.replace("BOUND", "575"),
        "memory budget exceeded",
    );
}
