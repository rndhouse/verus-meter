//! Guarded ownership programs preserve exact selection counts and child order.

use super::support::{rejects, verifies};

#[test]
fn threshold_selection_keeps_exact_fresh_footprints() {
    let code = "fn make(cutoff: usize) -> Vec<Box<[u8;32]>>
        requires cutoff <= 3,
        resources peak(memory) <= 256 {
        let mut v = Vec::<Box<[u8;32]>>::with_capacity(3);
        let mut i = 0usize;
        while i < 3
            invariant i <= 3, cutoff <= 3,
                v.len() == if i < cutoff { i } else { cutoff },
            decreases 3 - i,
        {
            if i < cutoff { let child = Box::new([0u8;32]); v.push(child); }
            i += 1;
        }
        v
    }
    fn f() resources peak(memory) <= BOUND {
        let v = make(COUNT); let scratch = [0u8;512];
    }";
    for (name, count, bound) in [("none", 0, 560), ("mixed", 2, 624), ("all", 3, 656)] {
        let code = code.replace("COUNT", &count.to_string());
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn invariant_selection_partitions_incoming_lifetimes() {
    let code = "fn remove(mut v: Vec<Box<[u8;32]>>, choose: bool) -> Vec<Box<[u8;32]>>
        requires v.len() == 2,
        resources peak(memory) <= 128 {
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, v.len() == if choose { 2 - i } else { 2 },
            decreases 2 - i,
        {
            if choose { v.pop(); }
            i += 1;
        }
        v
    }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Box<[u8;32]>>::with_capacity(2);
        let a = Box::new([0u8;32]); v.push(a);
        let b = Box::new([1u8;32]); v.push(b);
        let v = remove(v, CHOOSE); let scratch = [0u8;512];
    }";
    for (name, choose, bound) in [("keep", false, 616), ("drop", true, 552)] {
        let code = code.replace("CHOOSE", &choose.to_string());
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn routing_keeps_source_order_and_disjoint_destination_lifetimes() {
    // Export the selected collection through another helper. The caller checks
    // the last child's exact footprint after releasing every sibling and buffer.
    let code = "struct State { source: Vec<Vec<u32>>, left: Vec<Vec<u32>>, right: Vec<Vec<u32>> }
        fn route(mut state: State, cutoff: usize) -> (r: State)
            requires state.source.len() == 3, state.left.len() == 0,
                state.right.len() == 0, cutoff <= 3,
            ensures r.left.len() == cutoff, r.right.len() == 3 - cutoff,
            resources peak(memory) <= 512 {
            let mut i = 0usize;
            while i < 3
                invariant i <= 3, cutoff <= 3, state.source.len() == 3 - i,
                    state.left.len() == if i < cutoff { i } else { cutoff },
                    state.right.len() == if i < cutoff { 0int } else { i - cutoff },
                decreases 3 - i,
            {
                let child = state.source.pop().unwrap();
                if i < cutoff { state.left.push(child); } else { state.right.push(child); }
                i += 1;
            }
            state
        }
        fn selected() -> (r: Vec<Vec<u32>>) ensures r.len() == 2,
            resources peak(memory) <= 1024 {
            let mut source = Vec::<Vec<u32>>::with_capacity(3);
            let a = Vec::<u32>::with_capacity(4); source.push(a);
            let b = Vec::<u32>::with_capacity(8); source.push(b);
            let c = Vec::<u32>::with_capacity(16); source.push(c);
            let left = Vec::<Vec<u32>>::with_capacity(3);
            let right = Vec::<Vec<u32>>::with_capacity(3);
            let state = State { source, left, right };
            let mut state = route(state, 2);
            drop(state.source); drop(state.right);
            state.left
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = selected(); let child = v.pop().unwrap(); drop(v);
            let scratch = [0u8;2048];
        }";
    verifies("route", &code.replace("BOUND", "2104"));
    rejects("route_short", &code.replace("BOUND", "2103"), "memory budget exceeded");
}

#[test]
fn guarded_helpers_compose_through_nested_loops_and_keep_branch_peaks() {
    let code = "fn append(v: &mut Vec<Box<[u8;32]>>, choose: bool)
        requires old(v).len() <= 3,
        ensures final(v).len() == old(v).len() + if choose { 1int } else { 0int },
        resources peak(memory) <= 256 {
        if choose {
            let child = Box::new([0u8;32]); v.push(child);
        } else {
            let scratch = [0u8;192];
        }
    }
    fn make(choose: bool) -> Vec<Box<[u8;32]>>
        resources peak(memory) <= 640 {
        let mut v = Vec::<Box<[u8;32]>>::with_capacity(4);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, v.len() == if choose { 2*i } else { 0int },
            decreases 2 - i,
        {
            let mut j = 0usize;
            while j < 2 invariant j <= 2, i < 2,
                v.len() == if choose { 2*i + j } else { 0int }, decreases 2-j,
            { append(&mut v, choose); j += 1; }
            i += 1;
        }
        v
    }
    fn f() resources peak(memory) <= BOUND {
        let v = make(CHOOSE); let scratch = [0u8;1024];
    }";
    for (name, choose, bound) in [("skip", false, 1080), ("append", true, 1208)] {
        let code = code.replace("CHOOSE", &choose.to_string());
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
    // Reducing the retained transformation cannot erase the skipped path's
    // temporary allocation, including when no child survives at the caller.
    rejects(
        "branch_peak",
        "fn f() resources peak(memory) <= 128 {
        let mut v = Vec::<Box<[u8;8]>>::with_capacity(1);
        let mut i = 0usize;
        while i < 1 invariant i <= 1, v.len() <= i, decreases 1-i, {
            if i == 0 { let scratch = [0u8;256]; }
            else { let child = Box::new([0u8;8]); v.push(child); }
            i += 1;
        }
    }",
        "memory budget exceeded",
    );
}

#[test]
fn payload_and_nonlinear_counter_predicates_reject_without_aggregate_fallback() {
    for (name, condition) in [("payload", "child.len() > 0"), ("nonlinear_counter", "i * i < 2")] {
        rejects(
            name,
            &format!(
                "fn f(mut source: Vec<Vec<u32>>) -> Vec<Vec<u32>>
            requires source.len() == 2,
            resources peak(memory) <= 100000 {{
            let mut destination = Vec::<Vec<u32>>::with_capacity(2);
            let mut i = 0usize;
            while i < 2
                invariant i <= 2, source.len() == 2-i, destination.len() <= i,
                decreases 2-i,
            {{
                let child = source.pop().unwrap();
                if {condition} {{ destination.push(child); }} else {{ drop(child); }}
                i += 1;
            }}
            destination
        }}"
            ),
            "no precise helper summary can be inferred",
        );
    }
    rejects(
        "conditional_progress",
        "fn consume(mut source: Vec<Box<u32>>, choose: bool) -> Vec<Box<u32>>
        resources peak(memory) <= 100000 {
        while source.len() > 0 invariant true, decreases source.len(), {
            if choose { source.pop(); }
        }
        source
    }",
        "no precise helper summary can be inferred",
    );
}

#[test]
fn alternative_fresh_blocks_keep_selected_child_descriptors() {
    let code = "fn make(cutoff: usize) -> (v: Vec<Vec<u32>>)
        requires cutoff <= 2,
        ensures v.len() == 2,
        resources peak(memory) <= 256 {
        let mut v = Vec::<Vec<u32>>::with_capacity(2);
        let mut i = 0usize;
        while i < 2 invariant i <= 2, cutoff <= 2, v.len() == i, decreases 2-i, {
            if i < cutoff { let child = Vec::<u32>::with_capacity(4); v.push(child); }
            else { let child = Vec::<u32>::with_capacity(8); v.push(child); }
            i += 1;
        }
        v
    }
    fn f() resources peak(memory) <= BOUND {
        let mut v = make(CUTOFF);
        let child = v.pop().unwrap(); drop(v);
        let scratch = [0u8;512];
    }";
    for (name, cutoff, bound) in [("large", 0, 568), ("mixed", 1, 568), ("small", 2, 552)] {
        let code = code.replace("CUTOFF", &cutoff.to_string());
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn local_routing_proves_one_conservation_group_for_all_destinations() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::<Box<[u8;64]>>::with_capacity(2);
        let a = Box::new([0u8;64]); source.push(a);
        let b = Box::new([1u8;64]); source.push(b);
        let mut left = Vec::<Box<[u8;64]>>::with_capacity(2);
        let mut right = Vec::<Box<[u8;64]>>::with_capacity(2);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, source.len() + left.len() + right.len() == 2,
                source.len() == 2-i, left.len() <= i, right.len() <= i,
            decreases 2-i,
        {
            let child = source.pop().unwrap();
            if i < 1 { left.push(child); } else { right.push(child); }
            i += 1;
        }
        drop(source); let scratch = [0u8;512];
    }";
    verifies("local_routing", &code.replace("BOUND", "728"));
    rejects("local_routing_short", &code.replace("BOUND", "727"), "memory budget exceeded");
}

#[test]
fn a_counter_window_selects_removals_and_releases_original_children() {
    let code = "fn trim(mut v: Vec<Vec<u32>>, first: usize, end: usize) -> Vec<Vec<u32>>
        resources peak(memory) <= 128 {
        let mut i = 0usize;
        while i < 3 invariant i <= 3, decreases 3-i, {
            if first <= i && i < end { v.pop(); }
            i += 1;
        }
        v
    }
    fn f() resources peak(memory) <= BOUND {
        let mut v = Vec::<Vec<u32>>::with_capacity(3);
        let a = Vec::<u32>::with_capacity(4); v.push(a);
        let b = Vec::<u32>::with_capacity(8); v.push(b);
        let c = Vec::<u32>::with_capacity(16); v.push(c);
        let v = trim(v, FIRST, END); let scratch = [0u8;1024];
    }";
    for (name, first, end, bound) in [
        ("empty_window", 2, 1, 1232),
        ("outside", 5, 9, 1232),
        ("one", 1, 2, 1168),
        ("all", 0, 3, 1120),
    ] {
        let code = code.replace("FIRST", &first.to_string()).replace("END", &end.to_string());
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}
