//! Iteration effects compose across ownership roles and helper boundaries.

use super::support::{rejects, verifies};

#[test]
fn local_transfers_prove_combined_footprint_conservation() {
    let code = "fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::<Vec<u32>>::with_capacity(2);
        let a = Vec::<u32>::with_capacity(4); source.push(a);
        let b = Vec::<u32>::with_capacity(8); source.push(b);
        let mut destination = Vec::<Vec<u32>>::with_capacity(2);
        while source.len() > 0
            invariant source.len() + destination.len() == 2,
            decreases source.len(),
        {
            let child = source.pop().unwrap(); destination.push(child);
        }
        drop(source); let scratch = [0u8;512];
    }";
    verifies("local_transfer", &code.replace("BOUND", "632"));
    rejects("local_transfer_short", &code.replace("BOUND", "631"), "memory budget exceeded");
}

#[test]
fn consumption_releases_incoming_children_and_retains_backing() {
    let code = "fn consume(mut v: Vec<Box<[u8;32]>>, keep: usize) -> Vec<Box<[u8;32]>>
        resources peak(memory) <= 72 {
            while v.len() > keep invariant true, decreases v.len(), {
                let child = v.pop().unwrap(); drop(child);
            }
            v
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;32]>>::with_capacity(2);
            SETUP
            let v = consume(v, KEEP); let scratch = [0u8;256];
        }";
    for (name, setup, keep, bound) in [
        ("empty", "", 0, 296),
        ("one", "let a = Box::new([0u8;32]); v.push(a);", 0, 296),
        (
            "many",
            "let a = Box::new([0u8;32]); v.push(a); let b = Box::new([1u8;32]); v.push(b);",
            0,
            296,
        ),
        (
            "partial",
            "let a = Box::new([0u8;32]); v.push(a); let b = Box::new([1u8;32]); v.push(b);",
            1,
            328,
        ),
    ] {
        let code = code.replace("SETUP", setup).replace("KEEP", &keep.to_string());
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn transfers_preserve_different_child_extents_and_order() {
    let code = "fn transfer(mut source: Vec<Vec<u32>>) -> (r: Vec<Vec<u32>>)
        requires source.len() == 2,
        ensures r.len() == 2,
        resources peak(memory) <= 256 {
            let mut destination = Vec::<Vec<u32>>::with_capacity(2);
            while source.len() > 0
                invariant source.len() + destination.len() == 2,
                decreases source.len(),
            {
                let child = source.pop().unwrap(); destination.push(child);
            }
            destination
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(2);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            let mut v = transfer(v); let child = v.pop().unwrap(); drop(v);
            let scratch = [0u8;512];
        }";
    verifies("transfer", &code.replace("BOUND", "552"));
    rejects("transfer_short", &code.replace("BOUND", "551"), "memory budget exceeded");
}

#[test]
fn consumption_and_construction_compose_in_one_iteration() {
    let code = "fn make() -> Box<[u8;32]> resources peak(memory) <= 72 { Box::new([0u8;32]) }
        fn rebuild(mut source: Vec<Box<[u8;64]>>) -> Vec<Box<[u8;32]>>
            requires source.len() == 2,
            resources peak(memory) <= 256 {
                let mut destination = Vec::<Box<[u8;32]>>::with_capacity(2);
                while source.len() > 0
                    invariant source.len() + destination.len() == 2,
                    decreases source.len(),
                {
                    let old = source.pop().unwrap(); drop(old);
                    let child = make(); destination.push(child);
                }
                destination
            }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Box<[u8;64]>>::with_capacity(2);
            let a = Box::new([0u8;64]); v.push(a);
            let b = Box::new([1u8;64]); v.push(b);
            let v = rebuild(v); let scratch = [0u8;512];
        }";
    verifies("rebuild", &code.replace("BOUND", "616"));
    rejects("rebuild_short", &code.replace("BOUND", "615"), "memory budget exceeded");
}

#[test]
fn counted_iterations_can_build_multiple_independent_collections() {
    let code = "struct Outputs { a: Vec<Box<[u8;32]>>, b: Vec<Box<[u8;16]>>, }
        fn build(n: usize) -> Outputs requires n <= 2, resources peak(memory) <= 256 {
            let mut a = Vec::<Box<[u8;32]>>::with_capacity(2);
            let mut b = Vec::<Box<[u8;16]>>::with_capacity(2);
            let mut i = 0usize;
            while i < n invariant i <= n, n <= 2, a.len() == i, b.len() == i,
                decreases n - i,
            {
                let x = Box::new([0u8;32]); a.push(x);
                let y = Box::new([0u8;16]); b.push(y);
                i += 1;
            }
            Outputs { a, b }
        }
        fn f() resources peak(memory) <= BOUND {
            let outputs = build(2); let scratch = [0u8;512];
        }";
    verifies("build", &code.replace("BOUND", "688"));
    rejects("build_short", &code.replace("BOUND", "687"), "memory budget exceeded");
}

#[test]
fn disjoint_fixed_roles_transfer_nested_children_with_a_symbolic_count() {
    let code = "struct Child { data: Vec<u32>, tag: Box<[u8;8]> }
        struct State { source: Vec<Child>, destination: Vec<Child> }
        fn transfer(mut state: State, n: usize) -> (r: State)
            requires n <= state.source.len(),
                state.destination.len() + n <= 2,
            ensures r.destination.len() == state.destination.len() + n,
            resources peak(memory) <= 512 {
            let ghost initial = state.destination.len();
            let mut i = 0usize;
            while i < n
                invariant i <= n, state.destination.len() == initial + i,
                    state.source.len() >= n - i,
                    state.destination.len() + n - i <= 2,
                decreases n - i,
            {
                let child = state.source.pop().unwrap();
                state.destination.push(child); i += 1;
            }
            state
        }
        fn f() resources peak(memory) <= BOUND {
            let mut source = Vec::<Child>::with_capacity(2);
            let a = Child { data: Vec::<u32>::with_capacity(4), tag: Box::new([0u8;8]) };
            source.push(a);
            let b = Child { data: Vec::<u32>::with_capacity(8), tag: Box::new([1u8;8]) };
            source.push(b);
            let destination = Vec::<Child>::with_capacity(2);
            let state = State { source, destination };
            let state = transfer(state, COUNT);
            drop(state.source); let scratch = [0u8;1024];
        }";
    for (name, count, bound) in [("zero", 0, 1136), ("one", 1, 1176), ("two", 2, 1200)] {
        let code = code.replace("COUNT", &count.to_string());
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
    // Selecting a child after a fixed-field transfer must retain its nested
    // reservations and release both collection buffers independently.
    let extracted = code
        .replace("COUNT", "2")
        .replace("let state = transfer(state, 2);", "let mut state = transfer(state, 2);")
        .replace("drop(state.source); let scratch", "drop(state.source); let child = state.destination.pop().unwrap(); drop(state.destination); let scratch");
    verifies("fixed_role_extraction", &extracted.replace("BOUND", "1128"));
    rejects(
        "fixed_role_extraction_short",
        &extracted.replace("BOUND", "1127"),
        "memory budget exceeded",
    );
}

#[test]
fn unsupported_iteration_dependencies_reject_generous_budgets() {
    for (name, body, message) in [
        (
            "conditional",
            "if choose { source.pop(); }",
            "moving or dropping an enclosing heap owner across a branch, loop, or memory section",
        ),
        ("indexed_remove", "source.remove(0);", "no precise helper summary can be inferred"),
        (
            "dependent_construction",
            "source.pop(); let child = Vec::<u32>::with_capacity(i); destination.push(child);",
            "memory budget predicates currently require immutable Boolean or native integer input parameters",
        ),
        (
            "transformed_payload",
            "let mut child = source.pop().unwrap(); child.pop(); destination.push(child);",
            "no precise helper summary can be inferred",
        ),
    ] {
        rejects(
            name,
            &format!(
                "fn f(mut source: Vec<Vec<u32>>, choose: bool) -> Vec<Vec<u32>>
                    requires source.len() == 2, resources peak(memory) <= 100000 {{
                    let mut destination = Vec::<Vec<u32>>::with_capacity(2);
                    let mut i = 0usize;
                    while i < 2
                        invariant i <= 2, source.len() >= 2 - i, destination.len() <= i,
                        decreases 2 - i,
                    {{ {body} i += 1; }}
                    destination
                }}"
            ),
            message,
        );
    }
    // Nested extraction creates intermediate input regions. A representative
    // child token must not escape through those regions, even if the child is
    // ultimately dropped and never contributes to the returned forest.
    rejects(
        "intermediate_region_dependency",
        "fn f(mut source: Vec<Vec<Box<u32>>>) -> Vec<Vec<Box<u32>>>
            resources peak(memory) <= 100000 {
            while source.len() > 0 invariant true, decreases source.len(), {
                let mut child = source.pop().unwrap(); child.pop(); drop(child);
            }
            source
        }",
        "no precise helper summary can be inferred",
    );
}

#[test]
fn ordered_round_trips_preserve_complete_children_and_input_lifetimes() {
    let code = "struct State { values: Vec<Vec<u32>>, sibling: Box<[u8;16]> }
        fn round_trip(mut state: State, n: usize) -> (r: State)
            requires state.values.len() == 2, n <= 2,
            ensures r.values.len() == 2,
            resources peak(memory) <= 512 {
            let mut i = 0usize;
            while i < n
                invariant state.values.len() == 2, i <= n, n <= 2,
                decreases n-i,
            {
                OPERATIONS
                i += 1;
            }
            state
        }
        fn f() resources peak(memory) <= BOUND {
            let mut values = Vec::<Vec<u32>>::with_capacity(2);
            let first = Vec::<u32>::with_capacity(4); values.push(first);
            let second = Vec::<u32>::with_capacity(8); values.push(second);
            let state = State { values, sibling: Box::new([0u8;16]) };
            let mut state = round_trip(state, COUNT);
            let last = state.values.pop().unwrap(); drop(state);
            let scratch = [0u8;1024];
        }";
    let operations = "let first = state.values.pop().unwrap();
                let second = state.values.pop().unwrap();
                let temporary = Box::new([0u8;128]); drop(temporary);
                state.values.push(second); state.values.push(first);";
    let nested = format!(
        "let mut j = 0usize;
        while j < 2 invariant j <= 2, state.values.len() == 2, decreases 2-j,
        {{ {operations} j += 1; }}"
    );
    for (name, operations) in [("direct", operations), ("nested", nested.as_str())] {
        let code = code.replace("OPERATIONS", operations);
        for count in [0, 2] {
            let code = code.replace("COUNT", &count.to_string());
            verifies(name, &code.replace("BOUND", "1080"));
            rejects(
                &format!("{name}_short"),
                &code.replace("BOUND", "1079"),
                "memory budget exceeded",
            );
        }
    }
    rejects(
        "round_trip_intermediate_peak",
        &code
            .split("fn f()")
            .next()
            .unwrap()
            .replace("OPERATIONS", operations)
            .replace("<= 512", "<= 128"),
        "memory budget exceeded",
    );
    rejects(
        "changed_child_order",
        &code
            .replace(
                "OPERATIONS",
                &operations.replace(
                    "state.values.push(second); state.values.push(first);",
                    "state.values.push(first); state.values.push(second);",
                ),
            )
            .replace("COUNT", "2")
            .replace("BOUND", "100000"),
        "no precise helper summary can be inferred",
    );
}

#[test]
fn ordered_append_blocks_compose_direct_helpers_and_nested_loops() {
    let pair = "let a = Vec::<u32>::with_capacity(4); v.push(a);
                let b = Vec::<u32>::with_capacity(8); v.push(b);";
    let declarations = format!(
        "fn append_pair(v: &mut Vec<Vec<u32>>)
            requires old(v).len() <= 6,
            ensures final(v).len() == old(v).len() + 2,
            resources peak(memory) <= 1024 {{ {pair} }}"
    );
    let nested = format!(
        "let mut j = 0usize;
        while j < 2
            invariant j <= 2, v.len() == 4*i + 2*j, i < n, n <= 2,
            decreases 2-j,
        {{ {pair} j += 1; }}"
    );
    for (name, body) in [
        ("direct_block", format!("{pair} {pair}")),
        ("helper_block", "append_pair(&mut v); append_pair(&mut v);".into()),
        ("nested_block", nested),
    ] {
        let code = format!(
            "{declarations}
            fn build(n: usize) -> (r: Vec<Vec<u32>>)
                requires n <= 2, ensures r.len() == 4*n,
                resources peak(memory) <= 2048 {{
                let mut v = Vec::<Vec<u32>>::with_capacity(8);
                let mut i = 0usize;
                while i < n
                    invariant i <= n, n <= 2, v.len() == 4*i,
                    decreases n-i,
                {{ {body} i += 1; }}
                v
            }}
            fn f() resources peak(memory) <= BOUND {{
                let mut v = build(2); let last = v.pop().unwrap(); drop(v);
                let scratch = [0u8;4096];
            }}"
        );
        verifies(name, &code.replace("BOUND", "4152"));
        rejects(&format!("{name}_short"), &code.replace("BOUND", "4151"), "memory budget exceeded");
        verifies(
            &format!("{name}_zero"),
            &code
                .replace(
                    "let mut v = build(2); let last = v.pop().unwrap(); drop(v);",
                    "let v = build(0); drop(v);",
                )
                .replace("BOUND", "4096"),
        );
    }
}

#[test]
fn removal_blocks_compose_and_preserve_the_unconsumed_prefix() {
    let code = "fn trim_pair(v: &mut Vec<Vec<u32>>)
        requires old(v).len() >= 2,
        ensures final(v).len() == old(v).len() - 2,
        resources peak(memory) <= 64 { v.pop(); v.pop(); }
        fn build(n: usize) -> (r: Vec<Vec<u32>>)
            requires n <= 2, ensures r.len() == 4-2*n,
            resources peak(memory) <= 2048 {
            let mut v = Vec::<Vec<u32>>::with_capacity(4);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            let c = Vec::<u32>::with_capacity(12); v.push(c);
            let d = Vec::<u32>::with_capacity(16); v.push(d);
            let mut i = 0usize;
            while i < n
                invariant i <= n, n <= 2, v.len() == 4-2*i,
                decreases n-i,
            { BODY i += 1; }
            v
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = build(1); let last = v.pop().unwrap(); drop(v);
            let scratch = [0u8;4096];
        }";
    for (name, body) in [
        ("direct_removal_block", "v.pop(); v.pop();"),
        ("helper_removal_block", "trim_pair(&mut v);"),
        (
            "nested_removal_block",
            "let mut j = 0usize;
            while j < 2
                invariant j <= 2, i < n, n <= 2, v.len() == 4-2*i-j,
                decreases 2-j,
            { v.pop(); j += 1; }",
        ),
    ] {
        let code = code.replace("BODY", body);
        verifies(name, &code.replace("BOUND", "4152"));
        rejects(&format!("{name}_short"), &code.replace("BOUND", "4151"), "memory budget exceeded");
        verifies(
            &format!("{name}_empty"),
            &code
                .replace(
                    "let mut v = build(1); let last = v.pop().unwrap(); drop(v);",
                    "let v = build(2); drop(v);",
                )
                .replace("BOUND", "4096"),
        );
    }
}

#[test]
fn removal_blocks_partition_original_input_lifetimes() {
    let code = "fn trim(mut v: Vec<Vec<u32>>, n: usize) -> (r: Vec<Vec<u32>>)
        requires v.len() == 4, n <= 2,
        ensures r.len() == 4-2*n,
        resources peak(memory) <= 128 {
            let mut i = 0usize;
            while i < n
                invariant i <= n, n <= 2, v.len() + 2*i == 4,
                decreases n-i,
            { v.pop(); v.pop(); i += 1; }
            v
        }
        fn f() resources peak(memory) <= BOUND {
            let mut v = Vec::<Vec<u32>>::with_capacity(4);
            let a = Vec::<u32>::with_capacity(4); v.push(a);
            let b = Vec::<u32>::with_capacity(8); v.push(b);
            let c = Vec::<u32>::with_capacity(12); v.push(c);
            let d = Vec::<u32>::with_capacity(16); v.push(d);
            let v = trim(v, COUNT); let scratch = [0u8;4096];
        }";
    for (count, bound) in [(0, 4376), (1, 4264), (2, 4216)] {
        let code = code.replace("COUNT", &count.to_string());
        verifies("input_removal_block", &code.replace("BOUND", &bound.to_string()));
        rejects(
            "input_removal_block_short",
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn transfer_ranges_compose_and_keep_child_order_across_helpers_and_loops() {
    let operation = "let child = source.pop().unwrap(); destination.push(child);";
    let nested = format!(
        "let mut j = 0usize;
        while j < 2
            invariant j <= 2, i < n, n <= 2,
                source.len() + destination.len() == 4,
                destination.len() == 2*i+j,
            decreases 2-j,
        {{ {operation} j += 1; }}"
    );
    for (name, body) in [
        ("direct_range", format!("{operation} {operation}")),
        ("nested_range", nested),
        (
            "helper_range",
            "let a = source.pop().unwrap(); insert(&mut destination, a);
            let b = source.pop().unwrap(); insert(&mut destination, b);"
                .into(),
        ),
        (
            "forwarded_range",
            "let a = source.pop().unwrap(); let a = forward(a); destination.push(a);
            let b = source.pop().unwrap(); let b = forward(b); destination.push(b);"
                .into(),
        ),
    ] {
        let code = format!(
            "fn insert(v: &mut Vec<Vec<u32>>, child: Vec<u32>)
            requires old(v).len() < 4,
            ensures final(v).len() == old(v).len()+1,
            resources peak(memory) <= 256 {{ v.push(child); }}
            fn forward(v: Vec<u32>) -> Vec<u32> resources peak(memory) <= 24 {{ v }}
            fn build(n: usize) -> (r: Vec<Vec<u32>>)
                requires n <= 2, ensures r.len() == 2*n,
                resources peak(memory) <= 2048 {{
                let mut source = Vec::<Vec<u32>>::with_capacity(4);
                let a = Vec::<u32>::with_capacity(4); source.push(a);
                let b = Vec::<u32>::with_capacity(8); source.push(b);
                let c = Vec::<u32>::with_capacity(12); source.push(c);
                let d = Vec::<u32>::with_capacity(16); source.push(d);
                let mut destination = Vec::<Vec<u32>>::with_capacity(4);
                let mut i = 0usize;
                while i < n
                    invariant i <= n, n <= 2,
                        source.len() + destination.len() == 4,
                        destination.len() == 2*i,
                    decreases n-i,
                {{ {body} i += 1; }}
                destination
            }}
            fn f() resources peak(memory) <= BOUND {{
                let mut v = build(2); let last = v.pop().unwrap(); drop(v);
                let scratch = [0u8;4096];
            }}"
        );
        verifies(name, &code.replace("BOUND", "4136"));
        rejects(&format!("{name}_short"), &code.replace("BOUND", "4135"), "memory budget exceeded");
    }
}

#[test]
fn unsupported_block_dependencies_do_not_become_repeated_fresh_children() {
    for (name, body) in [
        (
            "partial_range_routing",
            "source.pop(); let child = source.pop().unwrap(); destination.push(child);",
        ),
        (
            "reordered_range",
            "let first = source.pop().unwrap(); let second = source.pop().unwrap(); destination.push(second); destination.push(first);",
        ),
        (
            "changing_nested_count",
            "let mut j = 0usize;
            while j < source.len() invariant j <= source.len(), decreases source.len()-j,
            { let child = Vec::<u32>::new(); destination.push(child); j += 1; }
            source.pop();",
        ),
    ] {
        rejects(
            name,
            &format!(
                "fn f(mut source: Vec<Vec<u32>>) -> Vec<Vec<u32>>
            requires source.len() == 4, resources peak(memory) <= 100000 {{
            let mut destination = Vec::<Vec<u32>>::with_capacity(8);
            let mut i = 0usize;
            while i < 2 invariant i <= 2, decreases 2-i,
            {{ {body} i += 1; }}
            destination
        }}"
            ),
            "no precise helper summary can be inferred",
        );
    }
    rejects(
        "changed_helper_parameter",
        "fn grow(mut v: Vec<u32>) -> Vec<u32>
        requires v.len() == 0, resources peak(memory) <= 256 { v.push(1); v }
        fn f(mut source: Vec<Vec<u32>>) -> Vec<Vec<u32>>
            requires source.len() == 2,
                forall|i: int| 0 <= i < source.len() ==> source[i].len() == 0,
            resources peak(memory) <= 100000 {
            let mut destination = Vec::<Vec<u32>>::with_capacity(2);
            let mut i = 0usize;
            while i < 2 invariant i <= 2, source.len() == 2-i,
                forall|j: int| 0 <= j < source.len() ==> source[j].len() == 0,
                decreases 2-i,
            {
                let child = source.pop().unwrap(); let child = grow(child);
                destination.push(child); i += 1;
            }
            destination
        }",
        "no precise helper summary can be inferred",
    );
}

#[test]
fn later_iterations_do_not_reuse_first_visit_zero_charge_shortcuts() {
    rejects(
        "later_extracted_charge",
        "fn f() resources peak(memory) <= 300 {
        let mut values = Vec::<Vec<u8>>::with_capacity(1);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, values.len() == if i == 0 { 0usize } else { 1usize },
            decreases 2-i,
        {
            let old = values.pop();
            let new = Vec::<u8>::with_capacity(128); values.push(new);
            drop(old); i += 1;
        }
    }",
        "memory budget exceeded",
    );
}
