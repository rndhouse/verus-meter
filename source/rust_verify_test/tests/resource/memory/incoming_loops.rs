//! Incoming ownership composes through loop operations and helper boundaries.

use super::support::{rejects, verifies};

#[test]
fn borrowed_extraction_preserves_independent_output_lifetimes() {
    let code = "fn trim(v: &mut Vec<Vec<u32>>) -> (r: Vec<Vec<u32>>)
        requires old(v).len() == 3,
        ensures final(v).len() == 1, r.len() == 2,
        resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(2); let mut i = 0usize;
        while i < 2
            invariant i <= 2, v.len() == 3-i, result.len() == i,
            decreases 2-i,
        { let child = v.remove(0); result.push(child); i += 1; }
        result
    }
    fn delegate(v: &mut Vec<Vec<u32>>) -> (r: Vec<Vec<u32>>)
        requires old(v).len() == 3,
        ensures final(v).len() == 1, r.len() == 2,
        resources peak(memory) <= 1200 { trim(v) }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(3);
        let a = Vec::<u32>::with_capacity(1); v.push(a);
        let b = Vec::<u32>::with_capacity(2); v.push(b);
        let c = Vec::<u32>::with_capacity(3); v.push(c);
        let selected = OPERATION(&mut v); RELEASE
        let scratch = [0u8;4096];
    }";
    for operation in ["trim", "delegate"] {
        for (name, release, bound) in [
            ("both", "", 4288),
            ("selected", "drop(v);", 4180),
            ("remaining", "drop(selected);", 4204),
        ] {
            let code = code.replace("OPERATION", operation).replace("RELEASE", release);
            verifies(name, &code.replace("BOUND", &bound.to_string()));
            rejects(
                &format!("{name}_short"),
                &code.replace("BOUND", &(bound - 1).to_string()),
                "memory budget exceeded",
            );
        }
    }
}

#[test]
fn indexed_incoming_updates_compose_direct_and_delegated_loops() {
    let code = "fn grow(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 2, old(v)[0].len() == 0,
        ensures final(v).len() == 2, final(v)[0].len() == 2,
        resources peak(memory) <= 256 {
        let mut i = 0usize;
        while i < 2 invariant i <= 2, v.len() == 2, v[0].len() == i, decreases 2-i, {
            v[0].push(7); i += 1;
        }
    }
    fn delegate(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 2, old(v)[0].len() == 0,
        ensures final(v).len() == 2, final(v)[0].len() == 2,
        resources peak(memory) <= 512 { grow(v) }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(2);
        let a = Vec::<u32>::new(); v.push(a);
        let b = Vec::<u32>::with_capacity(8); v.push(b);
        OPERATION(&mut v);
        let child = v.remove(INDEX); drop(v);
        let scratch = [0u8;4096];
    }";
    for operation in ["grow", "delegate"] {
        for (index, bound) in [(0, 4136), (1, 4152)] {
            let code = code.replace("OPERATION", operation).replace("INDEX", &index.to_string());
            verifies(operation, &code.replace("BOUND", &bound.to_string()));
            rejects(
                &format!("{operation}_short"),
                &code.replace("BOUND", &(bound - 1).to_string()),
                "memory budget exceeded",
            );
        }
    }
}

#[test]
fn delegated_owned_replacement_does_not_resurrect_displaced_inputs() {
    let code = "fn replace(mut v: Vec<Vec<u32>>) -> (r: Vec<Vec<u32>>)
        requires v.len() == 1, ensures r.len() == 1,
        resources peak(memory) <= 256 {
        let mut i = 0usize;
        while i < 2 invariant i <= 2, v.len() == 1, decreases 2-i, {
            let replacement = Vec::<u32>::with_capacity(2); v[0] = replacement; i += 1;
        }
        v
    }
    fn delegate(v: Vec<Vec<u32>>) -> (r: Vec<Vec<u32>>)
        requires v.len() == 1, ensures r.len() == 1,
        resources peak(memory) <= 512 { replace(v) }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::with_capacity(1);
        let a = Vec::<u32>::with_capacity(64); v.push(a);
        let mut v = OPERATION(v); let child = v.pop().unwrap(); drop(v);
        let scratch = [0u8;4096];
    }";
    for operation in ["replace", "delegate"] {
        let code = code.replace("OPERATION", operation);
        verifies(operation, &code.replace("BOUND", "4128"));
        rejects(
            &format!("{operation}_short"),
            &code.replace("BOUND", "4127"),
            "memory budget exceeded",
        );
    }
}

#[test]
fn empty_and_partial_borrowed_traversals_keep_real_cardinality() {
    let code = "fn trim(v: &mut Vec<Vec<u32>>, n: usize) -> (r: Vec<Vec<u32>>)
        requires n <= 2, n <= old(v).len(),
        ensures final(v).len() + n == old(v).len(), r.len() == n,
        resources peak(memory) <= 512 {
        let mut result = Vec::with_capacity(2); let mut i = 0usize;
        while i < n
            invariant i <= n, n <= 2, n <= old(v).len(), v.len()+i == old(v).len(), result.len() == i,
            decreases n-i,
        { let child = v.pop().unwrap(); result.push(child); i += 1; }
        result
    }
    fn delegate(v: &mut Vec<Vec<u32>>, n: usize) -> (r: Vec<Vec<u32>>)
        requires n <= 2, n <= old(v).len(),
        ensures final(v).len() + n == old(v).len(), r.len() == n,
        resources peak(memory) <= 600 { trim(v, n) }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Vec<u32>>::new(); INITIALIZE
        let selected = delegate(&mut v, COUNT); drop(v);
        let scratch = [0u8;4096];
    }";
    for (count, initialize, bound) in [
        (0, "", 4168),
        (1, "let a = Vec::<u32>::with_capacity(1); v.push(a);", 4172),
        (
            2,
            "let a = Vec::<u32>::with_capacity(1); v.push(a); let b = Vec::<u32>::with_capacity(2); v.push(b);",
            4180,
        ),
    ] {
        let code = code.replace("INITIALIZE", initialize).replace("COUNT", &count.to_string());
        verifies("partial", &code.replace("BOUND", &bound.to_string()));
        rejects(
            "partial_short",
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn owned_delegation_preserves_intermediate_original_lifetimes() {
    let code = "fn take(mut source: Vec<Vec<u8>>) -> Vec<u8>
        requires source.len() == 1,
        resources peak(memory) <= 256 {
        let mut selected = Vec::with_capacity(1); let mut i = 0usize;
        while i < 1 invariant i <= 1, source.len() == 1-i, selected.len() == i, decreases 1-i, {
            let child = source.remove(0); selected.push(child); i += 1;
        }
        selected.pop().unwrap()
    }
    fn delegate(source: Vec<Vec<u8>>) -> Vec<u8>
        requires source.len() == 1,
        resources peak(memory) <= 1400 {
        let child = take(source);
        let scratch = [0u8;1024];
        child
    }
    fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::with_capacity(1);
        let child = Vec::<u8>::with_capacity(4096); source.push(child);
        let result = delegate(source);
    }";
    verifies("owned_intermediate", &code.replace("BOUND", "8192"));
    rejects("owned_intermediate_short", &code.replace("BOUND", "5000"), "memory budget exceeded");
}

#[test]
fn nested_incoming_loans_delegate_without_copying_the_parent_region() {
    let code = "fn take(v: &mut Vec<Vec<u32>>) -> Vec<u32>
        requires old(v).len() == 3,
        ensures final(v).len() == 0,
        resources peak(memory) <= 1024 {
        let mut i = 0usize;
        while i < 2 invariant i <= 2, v.len() == 3-i, decreases 2-i, {
            let removed = v.remove(0); drop(removed); i += 1;
        }
        v.pop().unwrap()
    }
    fn visit(PARAMETER) -> Vec<u32>
        requires PRECONDITION,
        resources peak(memory) <= 1536 { take(&mut *v[0]) }
    fn f() resources peak(memory) <= BOUND {
        let mut inner = Vec::with_capacity(3);
        let a = Vec::<u32>::with_capacity(1); inner.push(a);
        let b = Vec::<u32>::with_capacity(2); inner.push(b);
        let c = Vec::<u32>::with_capacity(3); inner.push(c);
        let mut v = Vec::with_capacity(1); let child = Box::new(inner); v.push(child);
        let selected = visit(ARGUMENT); RELEASE
        let scratch = [0u8;4096];
    }";
    for (name, parameter, precondition, argument, release) in [
        (
            "borrowed_nested",
            "v: &mut Vec<Box<Vec<Vec<u32>>>>",
            "old(v).len() == 1, old(v)[0].len() == 3",
            "&mut v",
            "drop(v);",
        ),
        (
            "owned_nested",
            "mut v: Vec<Box<Vec<Vec<u32>>>>",
            "v.len() == 1, v[0].len() == 3",
            "v",
            "",
        ),
    ] {
        let code = code
            .replace("PARAMETER", parameter)
            .replace("PRECONDITION", precondition)
            .replace("ARGUMENT", argument)
            .replace("RELEASE", release);
        verifies(name, &code.replace("BOUND", "4132"));
        rejects(&format!("{name}_short"), &code.replace("BOUND", "4131"), "memory budget exceeded");
    }
}

#[test]
fn runtime_helpers_inside_incoming_loops_preserve_shifted_children() {
    let code = "fn trim(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 2,
        ensures final(v).len() == 1,
        resources peak(memory) <= 128 { v.remove(0); }
    fn visit(v: &mut Vec<Vec<Vec<u32>>>)
        requires old(v).len() == 2, forall|j: int| 0 <= j < 2 ==> #[trigger] old(v)[j].len() == 2,
        ensures final(v).len() == 2, forall|j: int| 0 <= j < 2 ==> #[trigger] final(v)[j].len() == 1,
        resources peak(memory) <= 2048 {
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, v.len() == 2,
                forall|j: int| 0 <= j < 2 ==> #[trigger] v[j].len() == if j < i { 1usize } else { 2usize },
            decreases 2-i,
        { trim(&mut v[i]); i += 1; }
    }
    fn f() resources peak(memory) <= BOUND {
        let mut first = Vec::with_capacity(2);
        let a = Vec::<u32>::with_capacity(1); first.push(a);
        let b = Vec::<u32>::with_capacity(2); first.push(b);
        let mut second = Vec::with_capacity(2);
        let c = Vec::<u32>::with_capacity(3); second.push(c);
        let d = Vec::<u32>::with_capacity(4); second.push(d);
        let mut v = Vec::with_capacity(2); v.push(first); v.push(second);
        visit(&mut v);
        let mut inner = v.remove(INDEX); let selected = inner.pop().unwrap(); drop(inner); drop(v);
        let scratch = [0u8;4096];
    }";
    for (index, bound) in [(0, 4128), (1, 4136)] {
        let code = code.replace("INDEX", &index.to_string());
        verifies("incoming_loop_call", &code.replace("BOUND", &bound.to_string()));
        rejects(
            "incoming_loop_call_short",
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn zero_local_bytes_do_not_establish_exact_incoming_capacity() {
    rejects(
        "local_capacity",
        r#"
fn no_growth(v: &mut Vec<u32>)
    requires old(v).len() == 2,
    resources peak(memory) <= 8 { v.push(9); }
struct Holder { data: Vec<Vec<u32>> }
fn twice(v: &mut Holder)
    requires old(v).data.len() == 1, old(v).data[0].len() == 0,
    ensures final(v).data.len() == 1, final(v).data[0].len() == 2,
    resources peak(memory) <= 256 {
    let mut i = 0usize;
    while i < 2 invariant i <= 2, v.data.len() == 1, v.data[0].len() == i, decreases 2-i, {
        v.data[0].push(1); i += 1;
    }
}
fn delegate(v: Vec<Vec<u32>>)
    requires v.len() == 1, v[0].len() == 0,
    resources peak(memory) <= 512 {
    let mut holder = Holder { data: v };
    twice(&mut holder);
    no_growth(&mut holder.data[0]);
}
"#,
        "vector capacity exceeded",
    );
}

#[test]
fn inputs_captured_by_fresh_fixed_fields_retain_their_original_lifetimes() {
    let code = "struct Holder { data: Vec<Vec<u8>> }
    fn append(v: &mut Vec<Vec<u8>>, child: Vec<u8>)
        requires old(v).len() == 0,
        ensures final(v).len() == 1,
        resources peak(memory) <= 256 { v.push(child); }
    fn take(mut holder: Holder, child: Vec<u8>) -> Vec<u8>
        resources peak(memory) <= 512 {
        let fresh = Vec::with_capacity(1); holder.data = fresh;
        append(&mut holder.data, child);
        holder.data.pop().unwrap()
    }
    fn delegate(holder: Holder, child: Vec<u8>) -> Vec<u8>
        resources peak(memory) <= 1400 {
        let selected = take(holder, child);
        let scratch = [0u8;1024]; selected
    }
    fn f() resources peak(memory) <= BOUND {
        let holder = Holder { data: Vec::new() };
        let child = Vec::<u8>::with_capacity(4096);
        let selected = delegate(holder, child);
    }";
    verifies("fresh_field_original", &code.replace("BOUND", "8192"));
    rejects("fresh_field_original_short", &code.replace("BOUND", "5000"), "memory budget exceeded");
}

#[test]
fn captured_inputs_keep_a_local_charge_view_after_helper_calls() {
    rejects(
        "captured_capacity",
        "fn append(v: &mut Vec<Vec<u32>>, child: Vec<u32>)
            requires old(v).len() == 0, child.len() == 0,
            ensures final(v).len() == 1, final(v)[0].len() == 0,
            resources peak(memory) <= 64 { v.push(child); }
        fn no_growth(v: &mut Vec<u32>) requires old(v).len() == 2,
            resources peak(memory) <= 8 { v.push(9); }
        fn delegate(child: Vec<u32>) requires child.len() == 0,
            resources peak(memory) <= 512 {
            let mut v = Vec::with_capacity(1); append(&mut v, child);
            let mut child = v.pop().unwrap();
            child.push(1); child.push(2);
            no_growth(&mut child);
        }",
        "vector capacity exceeded",
    );
}
