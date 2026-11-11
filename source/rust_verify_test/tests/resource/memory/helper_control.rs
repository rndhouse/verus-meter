//! Helper control flow preserves complete child forests across call boundaries.
use super::support::{rejects, verifies};

#[test]
fn loop_carried_helper_appends_preserve_precision() {
    verifies(
        "helper_append_loop",
        "fn append(v: &mut Vec<Vec<u32>>)
        requires old(v).len() <= 1,
        ensures final(v).len() == old(v).len() + 1,
        resources peak(memory) <= 100 {
            let child = Vec::<u32>::with_capacity(4); v.push(child);
        }
        fn f() resources peak(memory) <= 10000 {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let mut i = 0usize;
            while i < 2 invariant i <= 2, v.len() == i, decreases 2-i, {
                append(&mut v); i += 1;
            }
        }",
    );
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
fn unrepresentable_collection_control_flow_is_unsupported() {
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
    rejects(
        "conditional_loop_unsupported",
        &code.replace("BOUND", "10000"),
        "no precise helper summary can be inferred",
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
