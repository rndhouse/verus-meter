//! Removing a borrowed incoming child partitions ownership at the caller and
//! transfers only frame-local charges while checking the helper's body.

use super::support::{rejects, verifies};

#[test]
fn removed_and_remaining_children_have_independent_lifetimes() {
    for (name, release, bound) in
        [("both", "", 420), ("parent", "drop(v);", 288), ("result", "drop(child);", 388)]
    {
        let code = format!(
            "fn take(v: &mut Vec<Vec<u32>>, i: usize) -> (r: Vec<u32>)
                requires i < old(v).len(),
                ensures r == old(v)[i as int], final(v)@ == old(v)@.remove(i as int),
                resources peak(memory) <= 40 {{ v.remove(i) }}
            fn f() resources peak(memory) <= BOUND {{
                let mut v = Vec::<Vec<u32>>::with_capacity(3);
                let a = Vec::<u32>::with_capacity(1); v.push(a);
                let b = Vec::<u32>::with_capacity(2); v.push(b);
                let c = Vec::<u32>::with_capacity(8); v.push(c);
                let mut child = take(&mut v, 1);
                child.push(1); v[1].push(2);
                {release} let scratch = [0u8;256];
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
fn extraction_composes_across_child_ownership_shapes() {
    for (name, declaration, child_type, make_child, bytes) in [
        ("box", "", "Box<Vec<u32>>", "let child = Box::new(Vec::<u32>::with_capacity(4));", 48),
        (
            "struct",
            "struct Child { data: Box<Vec<u32>>, tag: Box<[u8;16]>, }",
            "Child",
            "let child = Child { data: Box::new(Vec::<u32>::with_capacity(4)), tag: Box::new([0u8;16]) };",
            72,
        ),
        (
            "runtime",
            "",
            "Vec<Box<Vec<u32>>>",
            "let mut child = Vec::<Box<Vec<u32>>>::with_capacity(1);
          let buffer = Box::new(Vec::<u32>::with_capacity(4)); child.push(buffer);",
            72,
        ),
    ] {
        let code = format!(
            "{declaration}
            fn take(v: &mut Vec<{child_type}>, i: usize) -> (r: {child_type})
                requires i < old(v).len(),
                ensures r == old(v)[i as int], final(v)@ == old(v)@.remove(i as int),
                resources peak(memory) <= ref_size(v) + value_size(i) + value_size({child_type}) {{
                    v.remove(i)
                }}
            fn f() resources peak(memory) <= BOUND {{
                let mut v = Vec::<{child_type}>::with_capacity(1);
                {make_child} v.push(child);
                let result = take(&mut v, 0); drop(v);
                let scratch = [0u8;256];
            }}"
        );
        verifies(name, &code.replace("BOUND", &(bytes + 256).to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bytes + 255).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn removal_transfers_new_charges_out_of_the_incoming_parent() {
    let code = "fn take(v: &mut Vec<Vec<u32>>, i: usize) -> (r: Vec<u32>)
        requires i < old(v).len(), old(v)[i as int].len() == 0,
        ensures r.len() == 1, final(v).len() + 1 == old(v).len(),
        resources peak(memory) <= HELPER {
            v[i].push(1); v.remove(i)
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::new(); v.push(child);
            let result = take(&mut v, 0); drop(v); let scratch = [0u8;256];
        }";
    verifies("local_charges", &code.replace("HELPER", "56").replace("BOUND", "296"));
    rejects(
        "local_charges_short",
        &code.replace("HELPER", "56").replace("BOUND", "295"),
        "memory budget exceeded",
    );
    rejects(
        "local_charges_helper_short",
        &code.split("fn f()").next().unwrap().replace("HELPER", "55"),
        "memory budget exceeded",
    );
}

#[test]
fn removal_through_fixed_and_runtime_parents_exports_the_mutation() {
    let code = "fn take(v: &mut Box<Vec<Vec<Box<[u8;32]>>>>, i: usize) -> (r: Box<[u8;32]>)
        requires old(v).len() == 1, i < old(v)[0].len(),
        ensures *r == *old(v)[0][i as int], final(v).len() == 1,
            final(v)[0]@ == old(v)[0]@.remove(i as int),
        resources peak(memory) <= 24 { v[0].remove(i) }
        fn f() resources peak(memory) <= BOUND {
            let mut rows = Vec::<Vec<Box<[u8;32]>>>::with_capacity(1);
            let mut row = Vec::<Box<[u8;32]>>::with_capacity(2);
            let a = Box::new([0u8;32]); row.push(a);
            let b = Box::new([1u8;32]); row.push(b); rows.push(row);
            let mut v = Box::new(rows);
            let child = take(&mut v, 0); RELEASE let scratch = [0u8;256];
        }";
    for (name, release, bound) in [("nested_both", "", 400), ("nested_parent", "drop(v);", 296)] {
        let code = code.replace("RELEASE", release);
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn incoming_extraction_inside_control_flow_is_unsupported() {
    for (name, body) in [
        ("branch", "if take { v.remove(0); }"),
        ("loop", "while v.len() > 0 invariant true, decreases v.len(), { v.remove(0); }"),
    ] {
        rejects(
            name,
            &format!(
                "fn f(v: &mut Vec<Box<u32>>, take: bool)
            resources peak(memory) <= 10000 {{ {body} }}"
            ),
            "moving or dropping an enclosing heap owner across a branch, loop, or memory section",
        );
    }
}
