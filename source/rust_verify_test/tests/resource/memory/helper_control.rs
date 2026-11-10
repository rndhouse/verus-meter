//! Helper control flow preserves complete child forests across call boundaries.
use super::support::{rejects, verifies};

#[test]
fn matching_optional_children_preserves_reservations() {
    let code = "fn append(v: &mut Vec<Vec<u32>>, source: &mut Vec<Vec<u32>>)
        requires old(v).len() == 0, old(source).len() == 1, old(source)[0].len() == 0,
        ensures final(v).len() == 1, final(v)[0].len() == 0,
        resources peak(memory) <= 80 {
            match source.pop() { Some(payload) => v.push(payload), None => {} }
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(1);
            let mut source = Vec::<Vec<u32>>::with_capacity(1);
            let child = Vec::<u32>::with_capacity(4);
            source.push(child); append(&mut v, &mut source); drop(source);
            v[0].push(7); let scratch = [0u8;200];
        }";
    verifies("matched_child", &code.replace("BOUND", "264"));
    rejects("matched_child_short", &code.replace("BOUND", "263"), "memory budget exceeded");
}

#[test]
fn counted_builders_preserve_uniform_child_reservations() {
    let code = "fn make(n: usize) -> (v: Vec<Vec<u32>>)
        requires n <= 2,
        ensures v.len() == n, forall|i: int| 0 <= i < n ==> v[i].len() == 0,
        resources peak(memory) <= 200 {
            let mut v = Vec::<Vec<u32>>::with_capacity(n);
            let mut i = 0usize;
            while i < n
                invariant i <= n, n <= 2, v.len() == i,
                    forall|j: int| 0 <= j < v.len() ==> v[j].len() == 0,
                decreases n - i,
            {
                let child = Vec::<u32>::with_capacity(4); v.push(child); i += 1;
            }
            v
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = make(2); v[0].push(7); v[1].push(8);
            let scratch = [0u8;200];
        }";
    verifies("counted_children", &code.replace("BOUND", "304"));
    rejects("counted_children_short", &code.replace("BOUND", "303"), "memory budget exceeded");
}

#[test]
fn shrinking_helpers_release_children_and_preserve_survivors() {
    let code = "fn shrink(v: &mut Vec<Vec<u32>>)
        requires old(v).len() == 2, old(v)[0].len() == 0,
        ensures final(v).len() == 1, final(v)[0].len() == 0,
        resources peak(memory) <= 40 {
            while v.len() > 1
                invariant 1 <= v.len() <= 2, v[0].len() == 0,
                decreases v.len(),
            { v.pop(); }
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            shrink(&mut v); v[0].push(7); let scratch = [0u8;200];
        }";
    verifies("shrunken_children", &code.replace("BOUND", "288"));
    rejects("shrunken_children_short", &code.replace("BOUND", "287"), "memory budget exceeded");
}

#[test]
fn repeated_fixed_owners_cover_growth_and_zero_iterations() {
    let code = "fn make(n: usize) -> (v: Vec<Box<[u8;32]>>)
        requires n <= 2, ensures v.len() == n,
        resources peak(memory) <= 200 {
            let mut v = Vec::<Box<[u8;32]>>::new();
            let mut i = 0usize;
            while i < n invariant i <= n, n <= 2, v.len() == i, decreases n-i, {
                let child = Box::new([0u8;32]); v.push(child); i += 1;
            }
            v
        }
        fn f() resources peak(memory) <= BOUND {
            let v = make(COUNT); let scratch = [0u8;200]; drop(v);
        }";
    verifies("repeated_fixed", &code.replace("COUNT", "2").replace("BOUND", "320"));
    rejects(
        "repeated_fixed_short",
        &code.replace("COUNT", "2").replace("BOUND", "319"),
        "memory budget exceeded",
    );
    verifies("repeated_empty", &code.replace("COUNT", "0").replace("BOUND", "224"));
    rejects(
        "repeated_empty_short",
        &code.replace("COUNT", "0").replace("BOUND", "223"),
        "memory budget exceeded",
    );
}

#[test]
fn repeated_nested_owners_compose_with_boxed_slice_results() {
    let code = "fn make(n: usize) -> (v: Box<[Box<Vec<u32>>]>)
        requires n <= 2,
        ensures v.len() == n, forall|i: int| 0 <= i < n ==> v[i].len() == 0,
        resources peak(memory) <= 240 {
            let mut v = Vec::<Box<Vec<u32>>>::with_capacity(n);
            let mut i = 0usize;
            while i < n
                invariant i <= n, n <= 2, v.len() == i,
                    forall|j: int| 0 <= j < v.len() ==> v[j].len() == 0,
                decreases n-i,
            {
                let child = Box::new(Vec::<u32>::with_capacity(4));
                v.push(child); i += 1;
            }
            v.into_boxed_slice()
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = make(2); v[0].push(7); v[1].push(8);
            let scratch = [0u8;256];
        }";
    verifies("repeated_nested_slice", &code.replace("BOUND", "368"));
    rejects("repeated_nested_slice_short", &code.replace("BOUND", "367"), "memory budget exceeded");
}

#[test]
fn conditional_collection_mutations_use_aggregate_fallback() {
    let code = "fn make() -> (v: Vec<Vec<u32>>)
        ensures v.len() == 1, v[0].len() == 0,
        resources peak(memory) <= 200 {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let mut i = 0usize;
            while i < 2
                invariant i <= 2, v.len() == if i == 0 { 0usize } else { 1usize },
                    forall|j: int| 0 <= j < v.len() ==> v[j].len() == 0,
                decreases 2-i,
            {
                if i == 0 {
                    let child = Vec::<u32>::with_capacity(4); v.push(child);
                }
                i += 1;
            }
            v
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = make(); v[0].push(7); let scratch = [0u8;200];
        }";
    verifies("conditional_loop_fallback", &code.replace("BOUND", "800"));
    rejects(
        "conditional_loop_no_false_reservation",
        &code.replace("BOUND", "288"),
        "memory budget exceeded",
    );
}

#[test]
fn repeated_regions_can_be_shrunk_before_returning() {
    let code = "fn make(n: usize) -> (v: Vec<Vec<u32>>)
        requires 1 <= n <= 2,
        ensures v.len() == 1, v[0].len() == 0,
        resources peak(memory) <= 200 {
            let mut v = Vec::<Vec<u32>>::with_capacity(n);
            let mut i = 0usize;
            while i < n
                invariant i <= n, 1 <= n <= 2, v.len() == i,
                    forall|j: int| 0 <= j < v.len() ==> v[j].len() == 0,
                decreases n-i,
            {
                let child = Vec::<u32>::with_capacity(4); v.push(child); i += 1;
            }
            while v.len() > 1
                invariant 1 <= v.len() <= n, 1 <= n <= 2,
                    forall|j: int| 0 <= j < v.len() ==> v[j].len() == 0,
                decreases v.len(),
            { v.pop(); }
            v
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = make(2); v[0].push(7); let scratch = [0u8;256];
        }";
    verifies("repeated_then_shrunk", &code.replace("BOUND", "344"));
    rejects("repeated_then_shrunk_short", &code.replace("BOUND", "343"), "memory budget exceeded");
}

#[test]
fn matching_none_preserves_the_existing_destination() {
    let code = "fn append(v: &mut Vec<Vec<u32>>, source: &mut Vec<Vec<u32>>)
        requires old(v).len() == 1, old(v)[0].len() == 0, old(source).len() == 0,
        ensures final(v).len() == 1, final(v)[0].len() == 0,
        resources peak(memory) <= 80 {
            match source.pop() { Some(payload) => v.push(payload), None => {} }
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let child = Vec::<u32>::with_capacity(4); v.push(child);
            let mut source = Vec::<Vec<u32>>::new();
            append(&mut v, &mut source); drop(source);
            v[0].push(7); let scratch = [0u8;200];
        }";
    verifies("matched_none", &code.replace("BOUND", "288"));
    rejects("matched_none_short", &code.replace("BOUND", "287"), "memory budget exceeded");
}

#[test]
fn loop_regions_follow_fixed_owner_paths_and_preserve_siblings() {
    let code = "struct Rows { values: Vec<Vec<u32>>, tag: Box<[u8;16]>, }
        fn make(n: usize) -> (rows: Rows)
        requires n <= 2,
        ensures rows.values.len() == n,
            forall|i: int| 0 <= i < n ==> rows.values[i].len() == 0,
        resources peak(memory) <= 240 {
            let mut rows = Rows {
                values: Vec::<Vec<u32>>::with_capacity(n), tag: Box::new([0u8;16]),
            };
            let mut i = 0usize;
            while i < n
                invariant i <= n, n <= 2, rows.values.len() == i,
                    forall|j: int| 0 <= j < rows.values.len() ==> rows.values[j].len() == 0,
                decreases n-i,
            {
                let child = Vec::<u32>::with_capacity(4);
                rows.values.push(child); i += 1;
            }
            rows
        }
        fn f() resources peak(memory) <= BOUND {
            let mut rows = make(2); rows.values[0].push(7); rows.values[1].push(8);
            let scratch = [0u8;256];
        }";
    verifies("fixed_path_loop", &code.replace("BOUND", "384"));
    rejects("fixed_path_loop_short", &code.replace("BOUND", "383"), "memory budget exceeded");
}
