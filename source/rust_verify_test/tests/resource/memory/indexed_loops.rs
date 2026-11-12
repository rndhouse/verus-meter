//! Ordered loop updates preserve runtime paths, revisits, and shifted siblings.

use super::support::{rejects, verifies};

#[test]
fn repeated_visits_keep_the_modified_child_and_untouched_sibling() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 2, resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(2);
        let a = Vec::<u32>::with_capacity(4); result.push(a);
        let b = Vec::<u32>::with_capacity(8); result.push(b);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, result.len() == 2, result[0].len() == i,
            decreases 2-i,
        { result[0].push(7); i += 1; }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); SELECTION drop(result);
        let scratch = [0u8;4096];
    }";
    for (name, selection, bound) in [
        ("revisited", "let selected = result.remove(0);", 4136),
        ("untouched", "let selected = result.pop().unwrap();", 4152),
    ] {
        let code = code.replace("SELECTION", selection);
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn distinct_indices_preserve_nested_fixed_and_runtime_paths() {
    let code = "struct Child { data: Vec<u32>, retained: Box<[u8;16]> }
    fn make() -> (r: Vec<Box<Vec<Child>>>)
        ensures r.len() == 1, r[0].len() == 2,
        resources peak(memory) <= 2048 {
        let mut inner = Vec::with_capacity(2);
        let a = Child { data: Vec::<u32>::with_capacity(2), retained: Box::new([0u8;16]) }; inner.push(a);
        let b = Child { data: Vec::<u32>::with_capacity(4), retained: Box::new([0u8;16]) }; inner.push(b);
        let mut result = Vec::with_capacity(1);
        let boxed = Box::new(inner); result.push(boxed);
        let mut i = 0usize;
        while i < result[0].len()
            invariant i <= 2, result.len() == 1, result[0].len() == 2,
                forall|j: int| 0 <= j < 2 ==> #[trigger] result[0][j].data.len() == if j < i { 1usize } else { 0usize },
            decreases 2-i,
        { result[0][i].data.push(7); i += 1; }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let selected = {
            let mut result = make(); let boxed = result.pop().unwrap();
            let mut inner = *boxed; inner.pop().unwrap()
        };
        let scratch = [0u8;4096];
    }";
    verifies("nested_indexed", &code.replace("BOUND", "4160"));
    rejects("nested_indexed_short", &code.replace("BOUND", "4159"), "memory budget exceeded");
}

#[test]
fn indexed_removal_selects_from_the_evolving_collection() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 1, resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(3);
        let a = Vec::<u32>::with_capacity(1); result.push(a);
        let b = Vec::<u32>::with_capacity(2); result.push(b);
        let c = Vec::<u32>::with_capacity(3); result.push(c);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, result.len() == 3-i,
            decreases 2-i,
        { let removed = result.remove(0); drop(removed); i += 1; }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("shifted_removal", &code.replace("BOUND", "4132"));
    rejects("shifted_removal_short", &code.replace("BOUND", "4131"), "memory budget exceeded");
}

#[test]
fn replacements_keep_per_child_extents() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 2, resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(2);
        let a = Vec::<u32>::with_capacity(8); result.push(a);
        let b = Vec::<u32>::with_capacity(16); result.push(b);
        let mut i = 0usize;
        while i < 2 invariant i <= 2, result.len() == 2, decreases 2-i, {
            let replacement = Vec::with_capacity(i + 1); result[0] = replacement; i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); SELECTION drop(result); let scratch = [0u8;4096];
    }";
    for (name, selection, bound) in [
        ("replaced_index", "let selected = result.remove(0);", 4128),
        ("replacement_sibling", "let selected = result.pop().unwrap();", 4184),
    ] {
        let code = code.replace("SELECTION", selection);
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn changed_children_can_be_removed_and_restored_repeatedly() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 2, resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(2);
        let a = Vec::<u32>::with_capacity(8); result.push(a);
        let b = Vec::<u32>::new(); result.push(b);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, result.len() == 2, result[1].len() == i,
            decreases 2-i,
        {
            let mut child = result.pop().unwrap(); child.push(7); result.push(child); i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("changed_restoration", &code.replace("BOUND", "4136"));
    rejects("changed_restoration_short", &code.replace("BOUND", "4135"), "memory budget exceeded");
}

#[test]
fn consuming_removal_uses_a_stable_index_and_shifted_survivors() {
    let code = "fn make(index: usize) -> (r: Vec<Vec<u32>>)
        requires index < 2, ensures r.len() == 1, resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(3);
        let a = Vec::<u32>::with_capacity(1); result.push(a);
        let b = Vec::<u32>::with_capacity(2); result.push(b);
        let c = Vec::<u32>::with_capacity(3); result.push(c);
        while result.len() > 1
            invariant 1 <= result.len() <= 3, index < 2,
            decreases result.len(),
        { let removed = result.remove(index); drop(removed); }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(INDEX); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    for (index, bound) in [(0, 4132), (1, 4124)] {
        let code = code.replace("INDEX", &index.to_string());
        verifies(&format!("consuming_index_{index}"), &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("consuming_index_{index}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn replacement_peak_includes_old_and_new_allocations() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut result = Vec::with_capacity(1);
        let child = Vec::<u8>::with_capacity(4096); result.push(child);
        let mut i = 0usize;
        while i < 2 invariant i <= 2, result.len() == 1, decreases 2-i, {
            let replacement = Vec::<u8>::with_capacity(4096);
            result[0] = replacement; i += 1;
        }
    }";
    verifies("indexed_overlap", &code.replace("BOUND", "16384"));
    rejects("indexed_overlap_short", &code.replace("BOUND", "8191"), "memory budget exceeded");
}

#[test]
fn first_visit_coincidences_do_not_make_a_changing_bound_stable() {
    rejects(
        "changing_indexed_bound",
        "fn make() -> Vec<Vec<u32>>
        resources peak(memory) <= 100000 {
        let mut result = Vec::with_capacity(3);
        let a = Vec::<u32>::new(); result.push(a);
        let b = Vec::<u32>::new(); result.push(b);
        let c = Vec::<u32>::new(); result.push(c);
        let mut i = 0usize;
        while i < result.len()
            invariant i <= 3, result.len() == if i < 2 { 3usize } else { 2usize },
            decreases 3-i,
        { if i == 1 { result.pop(); } i += 1; }
        result
    }",
        "no precise helper summary can be inferred",
    );
}

#[test]
fn indexed_helper_updates_support_a_symbolic_visit_count() {
    let code = "fn grow(child: &mut Vec<u32>)
        requires old(child).len() < 2,
        ensures final(child).len() == old(child).len() + 1,
        resources peak(memory) <= 64 { child.push(7); }
    fn make(n: usize) -> (r: Vec<Vec<u32>>)
        requires n <= 2, ensures r.len() == 2, resources peak(memory) <= 2048 {
        let mut result = Vec::with_capacity(2);
        let a = Vec::<u32>::with_capacity(4); result.push(a);
        let b = Vec::<u32>::with_capacity(8); result.push(b);
        let mut i = 0usize;
        while i < n
            invariant i <= n, n <= 2, result.len() == 2, result[0].len() == i,
            decreases n-i,
        { grow(&mut result[0]); i += 1; }
        result
    }
    fn f(n: usize) requires n <= 2, resources peak(memory) <= BOUND {
        let mut result = make(n); let selected = result.remove(0); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("symbolic_indexed_helper", &code.replace("BOUND", "4144"));
    rejects(
        "symbolic_indexed_helper_short",
        &code.replace("BOUND", "4143"),
        "memory budget exceeded",
    );
}

#[test]
fn removing_owned_inputs_keeps_only_the_surviving_original_regions() {
    let code = "fn trim(mut source: Vec<Vec<u32>>) -> Vec<u32>
        requires source.len() == 3,
        resources peak(memory) <= 256 {
        let mut i = 0usize;
        while i < 2 invariant i <= 2, source.len() == 3-i, decreases 2-i, {
            let removed = source.remove(0); drop(removed); i += 1;
        }
        source.pop().unwrap()
    }
    fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::with_capacity(3);
        let a = Vec::<u32>::with_capacity(1); source.push(a);
        let b = Vec::<u32>::with_capacity(2); source.push(b);
        let c = Vec::<u32>::with_capacity(3); source.push(c);
        let selected = trim(source);
        let scratch = [0u8;4096];
    }";
    verifies("indexed_owned_regions", &code.replace("BOUND", "4132"));
    rejects(
        "indexed_owned_regions_short",
        &code.replace("BOUND", "4131"),
        "memory budget exceeded",
    );
}

#[test]
fn zero_visits_do_not_reserve_unreachable_replacement_storage() {
    verifies(
        "zero_indexed_visits",
        "fn f() resources peak(memory) <= 4200 {
        let mut result = Vec::with_capacity(1);
        let child = Vec::<u8>::with_capacity(4096); result.push(child);
        let mut i = 0usize;
        while i < 0 invariant i == 0, result.len() == 1, decreases 1-i, {
            let replacement = Vec::<u8>::with_capacity(4096);
            result[0] = replacement; i += 1;
        }
    }",
    );
}

#[test]
fn indexed_helpers_compose_completed_recurrences() {
    let code = "fn update(child: &mut Vec<u32>)
        requires old(child).len() == 0,
        ensures final(child).len() == 3,
        resources peak(memory) <= 128 {
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, child.len() == if i == 0 { 0int } else { i + 1 },
            decreases 2-i,
        { child.pop(); child.push(7); child.push(8); i += 1; }
    }
    fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 1, resources peak(memory) <= 2048 {
        let mut result = Vec::with_capacity(1);
        let child = Vec::<u32>::new(); result.push(child);
        let mut i = 0usize;
        while i < 1
            invariant i <= 1, result.len() == 1, result[0].len() == 3*i,
            decreases 1-i,
        { update(&mut result[0]); i += 1; }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("indexed_recurrent_helper", &code.replace("BOUND", "4136"));
    rejects(
        "indexed_recurrent_helper_short",
        &code.replace("BOUND", "4135"),
        "memory budget exceeded",
    );
}

#[test]
fn reordered_children_keep_their_individual_allocations() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 2, resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(2);
        let first = Vec::<u32>::with_capacity(4); result.push(first);
        let second = Vec::<u32>::with_capacity(8); result.push(second);
        let mut i = 0usize;
        while i < COUNT invariant i <= COUNT, result.len() == 2, decreases COUNT-i, {
            let a = result.pop().unwrap(); let b = result.pop().unwrap();
            result.push(a); result.push(b); i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let last = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    for (count, bound) in [(1, 4136), (2, 4152)] {
        let code = code.replace("COUNT", &count.to_string());
        verifies("reordered", &code.replace("BOUND", &bound.to_string()));
        rejects(
            "reordered_short",
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}
