//! Checked visit counts connect scalar progress, lengths, and caller ownership.

use super::support::{rejects, verifies};

#[test]
fn immutable_derived_capacities_remain_related_to_symbolic_counts() {
    let code = "#[verifier::exec_allows_no_decreases_clause]
    fn make(n: usize) -> Vec<Box<[u8;8]>>
        requires n <= 10,
        resources peak(memory) <= 128 + 32 * n {
        let base = n + 1; let capacity = 2 * base;
        let mut result = Vec::with_capacity(capacity); let mut i = 0usize;
        while i < n {
            let first = Box::new([0u8;8]); result.push(first);
            let second = Box::new([0u8;8]); result.push(second);
            i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let result = make(COUNT); let scratch = [0u8;512];
    }";
    for (count, bound) in [(0, 552), (3, 648)] {
        let code = code.replace("COUNT", &count.to_string());
        verifies("derived_capacity", &code.replace("BOUND", &bound.to_string()));
        rejects(
            "derived_capacity_short",
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn scalar_calls_do_not_acquire_unstated_postconditions_at_loop_entry() {
    let code = "fn source() -> u8 resources peak(memory) <= 1 { 7 }
    #[verifier::exec_allows_no_decreases_clause]
    fn make() -> Vec<Box<[u8;8]>> resources peak(memory) <= 256 {
        let unrelated = source();
        let mut result = Vec::with_capacity(2); let mut i = 0usize;
        while i < 2 {
            let child = Box::new([0u8;8]); result.push(child); i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let result = make(); let scratch = [0u8;512];
    }";
    verifies("opaque_scalar", &code.replace("BOUND", "568"));
    rejects("opaque_scalar_short", &code.replace("BOUND", "567"), "memory budget exceeded");
}

#[test]
fn strides_and_countdowns_preserve_partial_final_ranges() {
    let code = "#[verifier::exec_allows_no_decreases_clause]
    fn build() -> Vec<Box<[u8;16]>> resources peak(memory) <= 256 {
        let mut result = Vec::with_capacity(3);
        INITIAL
        while CONDITION { let child = Box::new([0u8;16]); result.push(child); UPDATE }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let result = build(); let scratch = [0u8;512];
    }";
    for (name, initial, condition, update, bound) in [
        ("stride", "let mut i = 0usize;", "i < 5", "i += 2;", 608),
        ("inclusive", "let mut i = 0usize;", "i <= 4", "i += 2;", 608),
        ("countdown", "let mut i = 5i32;", "i > 0", "i -= 2;", 608),
        ("inclusive_countdown", "let mut i = 4i32;", "i >= 0", "i -= 2;", 608),
        ("reversed_countdown", "let mut i = 5i32;", "0 < i", "i = i - 2;", 608),
        ("reversed_stride", "let mut i = 0usize;", "5 > i", "i = 2 + i;", 608),
        ("empty", "let mut i = 5usize;", "i < 2", "i += 2;", 560),
    ] {
        let code = code
            .replace("INITIAL", initial)
            .replace("CONDITION", condition)
            .replace("UPDATE", update);
        verifies(name, &code.replace("BOUND", &bound.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn changing_bounds_and_additional_scalar_translations_close_at_exit() {
    let code = "struct Output { children: Vec<Box<[u8;16]>>, tail: Vec<u8> }
    #[verifier::exec_allows_no_decreases_clause]
    fn build() -> Output resources peak(memory) <= 256 {
        let mut result = Vec::with_capacity(2);
        let mut i = 0usize; let mut end = 6usize; let mut bytes = 0usize;
        while i < end {
            let child = Box::new([0u8;16]); result.push(child);
            i += 2; end -= 1; bytes += 3;
        }
        let tail = Vec::<u8>::with_capacity(bytes);
        Output { children: result, tail }
    }
    fn f() resources peak(memory) <= BOUND {
        let result = build(); let scratch = [0u8;512];
    }";
    verifies("carried_exit", &code.replace("BOUND", "614"));
    rejects("carried_exit_short", &code.replace("BOUND", "613"), "memory budget exceeded");
}

#[test]
fn native_counter_overflow_remains_an_executable_error() {
    rejects(
        "stride_overflow",
        "#[verifier::exec_allows_no_decreases_clause] fn f() resources peak(memory) <= 256 {
        let mut result = Vec::with_capacity(1);
        let mut i = 254u8;
        while i < 255 { result.push(Box::new([0u8;16])); i += 2; }
    }",
        "possible arithmetic underflow/overflow",
    );
}

#[test]
fn consuming_blocks_count_a_partial_last_visit() {
    let code = "fn trim(mut source: Vec<Vec<u32>>) -> Vec<Vec<u32>>
        resources peak(memory) <= 256 {
        while source.len() > 0 decreases source.len(), { source.pop(); source.pop(); }
        source
    }
    fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::with_capacity(3);
        let a = Vec::<u32>::with_capacity(1); source.push(a);
        let b = Vec::<u32>::with_capacity(2); source.push(b);
        let c = Vec::<u32>::with_capacity(3); source.push(c);
        let source = trim(source); let scratch = [0u8;512];
    }";
    verifies("consume_block", &code.replace("BOUND", "608"));
    rejects("consume_block_short", &code.replace("BOUND", "607"), "memory budget exceeded");
}

#[test]
fn reversed_consumption_counts_beyond_the_finite_window() {
    let code = "fn trim(mut source: Vec<Vec<u32>>) -> Vec<Vec<u32>>
        resources peak(memory) <= 256 {
        while 0 < source.len() decreases source.len(), { source.pop(); source.pop(); }
        source
    }
    fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::with_capacity(17); let mut i = 0usize;
        while i < 17 invariant i <= 17, decreases 17-i, {
            let child = Vec::<u32>::with_capacity(1); source.push(child); i += 1;
        }
        let source = trim(source); let scratch = [0u8;512];
    }";
    verifies("reversed_consume", &code.replace("BOUND", "952"));
    rejects("reversed_consume_short", &code.replace("BOUND", "951"), "memory budget exceeded");
}

#[test]
fn affine_guards_select_ranges_of_strided_visits() {
    let code = "#[verifier::exec_allows_no_decreases_clause]
    fn make() -> Vec<Box<[u8;16]>> resources peak(memory) <= 256 {
        let mut result = Vec::with_capacity(2);
        let mut i = 1usize;
        while i < 8 {
            if i + 1 < 6 { result.push(Box::new([0u8;16])); }
            i += 2;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let result = make(); let scratch = [0u8;512];
    }";
    verifies("stride_guard", &code.replace("BOUND", "584"));
    rejects("stride_guard_short", &code.replace("BOUND", "583"), "memory budget exceeded");
}

#[test]
fn stationary_indexed_overwrites_use_induction_beyond_the_finite_window() {
    let code =
        "fn make() -> (r: Vec<Vec<u32>>) ensures r.len() == 2, resources peak(memory) <= 4096 {
        let mut result = Vec::with_capacity(2);
        let a = Vec::<u32>::new(); result.push(a);
        let b = Vec::<u32>::with_capacity(8); result.push(b);
        let mut i = 0usize;
        while i < 16 invariant i <= 16, decreases 16-i, {
            let replacement = Vec::<u32>::with_capacity(i+1);
            result[0] = replacement; i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.remove(INDEX); drop(result);
        let scratch = [0u8;4096];
    }";
    for (index, bound) in [(0, 4184), (1, 4152)] {
        let code = code.replace("INDEX", &index.to_string());
        verifies("large_overwrite", &code.replace("BOUND", &bound.to_string()));
        rejects(
            "large_overwrite_short",
            &code.replace("BOUND", &(bound - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn affine_descriptor_updates_preserve_large_count_geometry_and_allocations() {
    let code = "fn append(v: &mut Vec<u32>, limit: usize)
        requires old(v).len() < limit,
        ensures final(v).len() == old(v).len()+1,
        resources peak(memory) <= 16 { v.push(1); }
    fn make() -> (r: Vec<u32>)
        ensures r.len() == 16,
        resources peak(memory) <= 4096 {
        let mut result = Vec::<u32>::with_capacity(32);
        let mut i = 0usize;
        while i < 16 invariant i <= 16, result.len() == i, decreases 16-i, {
            append(&mut result, 32); i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let selected = make();
        let length = selected.len(); let tail = Vec::<u8>::with_capacity(length);
        let scratch = [0u8;4096];
    }";
    verifies("large_affine", &code.replace("BOUND", "4296"));
    rejects("large_affine_short", &code.replace("BOUND", "4295"), "memory budget exceeded");
}

#[test]
fn data_dependent_and_nontranslation_progress_remain_unsupported() {
    for (name, update) in [
        ("geometric_progress", "i *= 2;"),
        ("payload_progress", "i += child.len();"),
        ("conditional_progress", "if i < 2 { i += 1; } else { i += 2; }"),
    ] {
        rejects(
            name,
            &format!(
                "fn f(mut source: Vec<Vec<u32>>) -> Vec<Vec<u32>>
            requires source.len() == 4,
            resources peak(memory) <= 100000 {{
            let mut result = Vec::with_capacity(4); let mut i = 1usize;
            while i < 4 invariant i <= 100, source.len() <= 4, decreases 100-i, {{
                let child = source.pop().unwrap(); {update} result.push(child);
            }}
            result
        }}"
            ),
            "no precise helper summary can be inferred",
        );
    }
    // Saturation changes relative progress: the shorter collection becomes
    // empty before the other one. A single gap stride would overcount visits.
    rejects(
        "dual_saturation",
        "#[verifier::exec_allows_no_decreases_clause]
        fn f(mut a: Vec<Vec<u32>>, mut b: Vec<Vec<u32>>) -> Vec<Vec<u32>>
            requires a.len() == 1, b.len() == 5,
            resources peak(memory) <= 100000 {
            while a.len() < b.len() { a.pop(); b.pop(); b.pop(); }
            b
        }",
        "no precise helper summary can be inferred",
    );
    rejects(
        "known_dual_saturation",
        "#[verifier::exec_allows_no_decreases_clause]
        fn f() -> Vec<Vec<u32>> resources peak(memory) <= 100000 {
            let mut a = Vec::with_capacity(1); let first = Vec::<u32>::new(); a.push(first);
            let mut b = Vec::with_capacity(5); let mut i = 0usize;
            while i < 5 { let child = Vec::<u32>::new(); b.push(child); i += 1; }
            while a.len() < b.len() { a.pop(); b.pop(); b.pop(); }
            b
        }",
        "no precise helper summary can be inferred",
    );
    rejects(
        "computed_saturating_progress",
        "#[verifier::exec_allows_no_decreases_clause]
        fn f() -> Vec<Vec<u32>> resources peak(memory) <= 100000 {
            let mut source = Vec::with_capacity(1);
            let first = Vec::<u32>::new(); source.push(first);
            let mut result = Vec::with_capacity(3); let mut end = 5usize;
            while source.len() + 1 < end {
                source.pop();
                let child = Vec::<u32>::with_capacity(1); result.push(child);
                end -= 2;
            }
            result
        }",
        "no precise helper summary can be inferred",
    );
}

#[test]
fn nested_counts_use_the_current_outer_scalar_state() {
    let code = "fn make() -> Vec<Box<[u8;8]>> resources peak(memory) <= 512 {
        let mut result = Vec::with_capacity(9); let mut i = 0usize;
        while i < 3 invariant i <= 3, result.len() <= 3*i, decreases 3-i, {
            let mut j = 0usize;
            while j < i invariant j <= i, i < 3, result.len() <= 3*i+j, decreases i-j, {
                let child = Box::new([0u8;8]); result.push(child); j += 1;
            }
            i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let result = make(); let scratch = [0u8;512];
    }";
    verifies("nested_count", &code.replace("BOUND", "632"));
    rejects("nested_count_short", &code.replace("BOUND", "631"), "memory budget exceeded");
}

#[test]
fn symbolic_bounds_control_allocation_extents_without_replacing_descriptors() {
    let code = "fn bytes(n: usize) -> (r: Vec<u8>)
        requires n <= 7, ensures r.len() == n, resources peak(memory) <= 128 {
        let mut result = Vec::with_capacity(n); let mut i = 0usize;
        while i < n invariant i <= n, decreases n-i, { result.push(0); i += 1; }
        result
    }
    fn replace(mut source: Vec<Vec<u8>>, limit: usize) -> Vec<Vec<u8>>
        requires source.len() == 2, limit <= 32,
            forall|j: int| 0 <= j < 2 ==> #[trigger] source[j].len() <= limit,
        resources peak(memory) <= 256 + 4 * limit {
        let mut i = 0usize;
        while i < 2 invariant i <= 2, source.len() == 2,
            forall|j: int| 0 <= j < 2 ==> #[trigger] source[j].len() <= limit,
            decreases 2-i,
        {
            let length = source[i].len();
            let replacement = Vec::<u8>::with_capacity(length); source[i] = replacement;
            i += 1;
        }
        source
    }
    fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::with_capacity(2);
        let first = bytes(5); source.push(first);
        let second = bytes(7); source.push(second);
        let result = replace(source, 7); let scratch = [0u8;4096];
    }";
    verifies("symbolic_extents", &code.replace("BOUND", "4180"));
    rejects("symbolic_extents_short", &code.replace("BOUND", "4179"), "memory budget exceeded");
}
