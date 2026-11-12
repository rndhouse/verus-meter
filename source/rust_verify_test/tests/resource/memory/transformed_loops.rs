//! Traversals retain a different, complete ownership forest for each child.

use super::support::{rejects, verifies};

#[test]
fn nested_release_returns_each_remaining_child() {
    let code = "fn make() -> (r: Vec<Vec<Box<[u8;32]>>>)
        ensures r.len() == 2,
        resources peak(memory) <= 1024 {
        let mut source = Vec::with_capacity(2);
        let mut a = Vec::with_capacity(1); let x = Box::new([0u8;32]); a.push(x); source.push(a);
        let mut b = Vec::with_capacity(3); let y = Box::new([0u8;32]); b.push(y); source.push(b);
        let mut destination = Vec::with_capacity(2);
        while source.len() > 0
            invariant source.len() + destination.len() == 2,
            decreases source.len(),
        {
            let mut child = source.pop().unwrap();
            let removed = child.pop(); drop(removed);
            destination.push(child);
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make();
        let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;2048];
    }";
    verifies("trim_nested", &code.replace("BOUND", "2080"));
    rejects("trim_nested_short", &code.replace("BOUND", "2079"), "memory budget exceeded");
}

#[test]
fn generation_uses_the_iteration_capacity() {
    let code = "fn build(n: usize) -> (r: Vec<Vec<u32>>)
        requires n <= 16,
        ensures r.len() == n,
        resources peak(memory) <= 2048 {
        let mut result = Vec::with_capacity(16);
        let mut i = 0usize;
        while i < n
            invariant i <= n, n <= 16, result.len() == i,
            decreases n-i,
        {
            let child = Vec::with_capacity(i + 1); result.push(child); i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = build(16);
        let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("iteration_capacity", &code.replace("BOUND", "4184"));
    rejects("iteration_capacity_short", &code.replace("BOUND", "4183"), "memory budget exceeded");
    let zero = code
        .replace("let mut result = build(16);", "let result = build(0);")
        .replace("let selected = result.pop().unwrap(); drop(result);", "drop(result);");
    verifies("empty_generation", &zero.replace("BOUND", "4096"));
    let helper = "fn allocate(capacity: usize) -> Vec<u32>
        requires capacity <= 16, resources peak(memory) <= 32 + 4*capacity {
        Vec::with_capacity(capacity)
    }";
    let through_call =
        format!("{helper} {}", code.replace("Vec::with_capacity(i + 1)", "allocate(i)"));
    verifies("iteration_capacity_call", &through_call.replace("BOUND", "4180"));
    rejects(
        "iteration_capacity_call_short",
        &through_call.replace("BOUND", "4179"),
        "memory budget exceeded",
    );
}

#[test]
fn replacement_preserves_the_other_original_fields() {
    let code = "struct Child { buffer: Vec<u32>, retained: Box<[u8;16]> }
    fn make() -> (r: Vec<Child>)
        ensures r.len() == 2,
        resources peak(memory) <= 1024 {
        let mut source = Vec::with_capacity(2);
        let a = Child { buffer: Vec::with_capacity(1), retained: Box::new([0u8;16]) }; source.push(a);
        let b = Child { buffer: Vec::with_capacity(3), retained: Box::new([0u8;16]) }; source.push(b);
        let mut destination = Vec::with_capacity(2);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, source.len() + destination.len() == 2, destination.len() == i,
            decreases 2-i,
        {
            let mut child = source.pop().unwrap();
            let replacement = Vec::with_capacity(i); child.buffer = replacement;
            destination.push(child); i += 1;
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("replace_field", &code.replace("BOUND", "4148"));
    rejects("replace_field_short", &code.replace("BOUND", "4147"), "memory budget exceeded");
}

#[test]
fn growing_each_child_preserves_its_original_capacity() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 2,
        resources peak(memory) <= 1024 {
        let mut source = Vec::with_capacity(2);
        let a = Vec::<u32>::with_capacity(0); source.push(a);
        let b = Vec::<u32>::with_capacity(8); source.push(b);
        let mut destination = Vec::with_capacity(2);
        while source.len() > 0
            invariant source.len() + destination.len() == 2,
                forall|k: int| 0 <= k < source.len() ==> #[trigger] source[k].len() == 0,
            decreases source.len(),
        {
            let mut child = source.pop().unwrap(); child.push(1); destination.push(child);
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    for (name, selection, bound) in [
        ("grown_child", "", 4136),
        ("spare_capacity", "let first = result.pop(); drop(first);", 4152),
    ] {
        let code = code.replace(
            "let selected = result.pop().unwrap(); drop(result);",
            &format!("{selection} let selected = result.pop().unwrap(); drop(result);"),
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
fn intermediate_input_regions_close_before_export() {
    let code = "fn clear(mut source: Vec<Vec<Box<u32>>>) -> (r: Vec<Vec<Box<u32>>>)
        ensures r.len() == 0,
        resources peak(memory) <= 256 {
        while source.len() > 0 invariant true, decreases source.len(), {
            let mut child = source.pop().unwrap(); child.pop(); drop(child);
        }
        source
    }
    fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::with_capacity(2);
        let mut a = Vec::with_capacity(1); let x = Box::new(1u32); a.push(x); source.push(a);
        let mut b = Vec::with_capacity(3); let y = Box::new(2u32); b.push(y); source.push(b);
        let result = clear(source); let scratch = [0u8;4096];
    }";
    verifies("intermediate_regions", &code.replace("BOUND", "4168"));
    rejects("intermediate_regions_short", &code.replace("BOUND", "4167"), "memory budget exceeded");
    verifies(
        "incoming_transform",
        "fn trim(mut source: Vec<Vec<u32>>) -> Vec<Vec<u32>>
            requires source.len() == 2, resources peak(memory) <= 512 {
            let mut destination = Vec::with_capacity(2);
            while source.len() > 0
                invariant source.len() + destination.len() == 2,
                decreases source.len(),
            {
                let mut child = source.pop().unwrap(); child.pop(); destination.push(child);
            }
            destination
        }",
    );
}

#[test]
fn leaf_only_interfaces_keep_the_selected_descriptor() {
    let code = "fn selected() -> Vec<u32> resources peak(memory) <= 2048 {
        let mut buffers = Vec::with_capacity(3);
        let mut i = 0usize;
        while i < 3
            invariant i <= 3, buffers.len() == i,
            decreases 3-i,
        {
            let child = Vec::with_capacity(i); buffers.push(child); i += 1;
        }
        buffers.pop().unwrap()
    }
    fn forward() -> Vec<u32> resources peak(memory) <= 2048 { selected() }
    fn f() resources peak(memory) <= BOUND {
        let selected = forward(); let scratch = [0u8;4096];
    }";
    verifies("leaf_descriptor", &code.replace("BOUND", "4128"));
    rejects("leaf_descriptor_short", &code.replace("BOUND", "4127"), "memory budget exceeded");
}

#[test]
fn helper_growth_uses_its_checked_allocation_allowance() {
    let code = "fn grow(mut child: Vec<u32>) -> Vec<u32>
        requires child.len() == 0,
        resources peak(memory) <= 64 { child.push(1); child }
    fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 2,
        resources peak(memory) <= 1024 {
        let mut source = Vec::with_capacity(2);
        let a = Vec::<u32>::with_capacity(0); source.push(a);
        let b = Vec::<u32>::with_capacity(8); source.push(b);
        let mut destination = Vec::with_capacity(2);
        while source.len() > 0
            invariant source.len() + destination.len() == 2,
                forall|k: int| 0 <= k < source.len() ==> #[trigger] source[k].len() == 0,
            decreases source.len(),
        {
            let child = source.pop().unwrap(); let child = grow(child); destination.push(child);
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("helper_growth", &code.replace("BOUND", "4136"));
    rejects("helper_growth_short", &code.replace("BOUND", "4135"), "memory budget exceeded");
}

#[test]
fn temporary_allocation_peaks_survive_transformation_composition() {
    let code = "fn trim(mut source: Vec<Vec<Box<u32>>>) -> Vec<Vec<Box<u32>>>
        requires source.len() == 1,
        resources peak(memory) <= BOUND {
        let mut destination = Vec::with_capacity(1);
        while source.len() > 0
            invariant source.len() + destination.len() == 1,
            decreases source.len(),
        {
            let mut child = source.pop().unwrap();
            let temporary = Box::new([0u8;4096]); drop(temporary);
            child.pop(); destination.push(child);
        }
        destination
    }";
    verifies("transformation_peak", &code.replace("BOUND", "8192"));
    rejects("transformation_peak_short", &code.replace("BOUND", "4095"), "memory budget exceeded");
}

#[test]
fn unsupported_payload_observations_have_no_fallback() {
    rejects(
        "payload_capacity",
        "fn f(mut sizes: Vec<usize>) -> Vec<Vec<u32>>
        resources peak(memory) <= 100000 {
        let mut result = Vec::with_capacity(2);
        while sizes.len() > 0
            invariant sizes.len() + result.len() == 2,
            decreases sizes.len(),
        {
            let capacity = sizes.pop().unwrap();
            let child = Vec::with_capacity(capacity); result.push(child);
        }
        result
    }",
        "no precise helper summary can be inferred",
    );
}

#[test]
fn extracting_fixed_children_releases_each_incoming_wrapper() {
    let code = "fn unbox(mut source: Vec<Box<Vec<u32>>>) -> (r: Vec<Vec<u32>>)
        requires source.len() == 2,
        ensures r.len() == 2,
        resources peak(memory) <= 512 {
        let mut destination = Vec::with_capacity(2);
        while source.len() > 0
            invariant source.len() + destination.len() == 2,
            decreases source.len(),
        {
            let boxed = source.pop().unwrap(); let child = *boxed; destination.push(child);
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut source = Vec::with_capacity(2);
        let a = Box::new(Vec::<u32>::with_capacity(1)); source.push(a);
        let b = Box::new(Vec::<u32>::with_capacity(3)); source.push(b);
        let mut result = unbox(source); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("unbox_children", &code.replace("BOUND", "4124"));
    rejects("unbox_children_short", &code.replace("BOUND", "4123"), "memory budget exceeded");
}

#[test]
fn generated_blocks_preserve_source_offsets_and_output_order() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == OUTPUTS,
        resources peak(memory) <= 1024 {
        let mut source = Vec::with_capacity(4);
        let a = Vec::<u32>::with_capacity(1); source.push(a);
        let b = Vec::<u32>::with_capacity(2); source.push(b);
        let c = Vec::<u32>::with_capacity(3); source.push(c);
        let d = Vec::<u32>::with_capacity(4); source.push(d);
        let mut destination = Vec::with_capacity(4);
        let mut i = 0usize;
        while i < 2
            invariant i <= 2, source.len() == 4 - 2*i, destination.len() == WIDTH*i,
            decreases 2-i,
        {
            OPERATIONS
            i += 1;
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    for (name, body, width, peak) in [
        (
            "partial_block",
            "source.pop(); let child = source.pop().unwrap(); destination.push(child);",
            1,
            4124,
        ),
        (
            "reordered_block",
            "let first = source.pop().unwrap(); let second = source.pop().unwrap(); destination.push(second); destination.push(first);",
            2,
            4128,
        ),
    ] {
        let code = code
            .replace("OPERATIONS", body)
            .replace("WIDTH", &width.to_string())
            .replace("OUTPUTS", &(2 * width).to_string());
        verifies(name, &code.replace("BOUND", &peak.to_string()));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &(peak - 1).to_string()),
            "memory budget exceeded",
        );
    }
}

#[test]
fn converting_children_retains_only_the_length_sized_allocations() {
    let code = "fn make() -> (r: Vec<Box<[u32]>>)
        ensures r.len() == 2,
        resources peak(memory) <= 512 {
        let mut source = Vec::with_capacity(2);
        let mut a = Vec::<u32>::with_capacity(1); a.push(1); source.push(a);
        let mut b = Vec::<u32>::with_capacity(3); b.push(2); source.push(b);
        let mut destination = Vec::with_capacity(2);
        while source.len() > 0
            invariant source.len() + destination.len() == 2,
                forall|k: int| 0 <= k < source.len() ==> #[trigger] source[k].len() == 1,
            decreases source.len(),
        {
            let child = source.pop().unwrap();
            let boxed = child.into_boxed_slice(); destination.push(boxed);
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("convert_children", &code.replace("BOUND", "4116"));
    rejects("convert_children_short", &code.replace("BOUND", "4115"), "memory budget exceeded");
}

#[test]
fn nonzero_counter_ranges_keep_each_threshold_phase() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 3,
        resources peak(memory) <= 1024 {
        let mut result = Vec::with_capacity(3);
        let mut i = 2usize;
        while i < 5
            invariant 2 <= i <= 5, result.len() == i - 2,
            decreases 5-i,
        {
            if i < 4 {
                let child = Vec::with_capacity(i); result.push(child);
            } else {
                let child = Vec::with_capacity(i + 1); result.push(child);
            }
            i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("offset_phases", &code.replace("BOUND", "4140"));
    rejects("offset_phases_short", &code.replace("BOUND", "4139"), "memory budget exceeded");
}

#[test]
fn allocation_sizes_can_observe_each_selected_child() {
    let code = "fn make() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 2,
        resources peak(memory) <= 512 {
        let mut source = Vec::with_capacity(2);
        let mut a = Vec::<u32>::with_capacity(2); a.push(1); source.push(a);
        let mut b = Vec::<u32>::with_capacity(4); b.push(1); b.push(2); source.push(b);
        let mut destination = Vec::with_capacity(2);
        while source.len() > 0
            invariant source.len() + destination.len() == 2,
                forall|k: int| 0 <= k < source.len() ==> #[trigger] source[k].len() <= 2,
            decreases source.len(),
        {
            let old = source.pop().unwrap();
            let capacity = old.len(); let child = Vec::with_capacity(capacity + 1);
            drop(old); destination.push(child);
        }
        destination
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = make(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("child_observation", &code.replace("BOUND", "4128"));
    let helper = "fn allocate(capacity: usize) -> Vec<u32>
        requires capacity <= 3, resources peak(memory) <= 32 + 4*capacity {
        Vec::with_capacity(capacity)
    }";
    let through_call = format!(
        "{helper} {}",
        code.replace(
            "let capacity = old.len(); let child = Vec::with_capacity(capacity + 1);",
            "let capacity = old.len() + 1; let child = allocate(capacity);"
        )
    );
    verifies("child_observation_call", &through_call.replace("BOUND", "4128"));
    rejects(
        "child_observation_call_short",
        &through_call.replace("BOUND", "4127"),
        "memory budget exceeded",
    );
    rejects("child_observation_short", &code.replace("BOUND", "4127"), "memory budget exceeded");
}

#[test]
fn optional_outputs_distinguish_later_empty_extractions() {
    let code = "fn make() -> (r: Vec<Option<Vec<u32>>>)
        ensures r.len() == 3, r[0].is_some(), r[1].is_none(), r[2].is_none(),
        resources peak(memory) <= 1024 {
        let mut source = Vec::with_capacity(1);
        let child = Vec::<u32>::with_capacity(4); source.push(child);
        let mut destination = Vec::<Option<Vec<u32>>>::with_capacity(3);
        let mut i = 0usize;
        while i < 3
            invariant i <= 3, destination.len() == i,
                source.len() == if i == 0 { 1usize } else { 0usize },
                i > 0 ==> destination[0].is_some(),
                forall|k: int| 1 <= k < destination.len() ==> #[trigger] destination[k].is_none(),
            decreases 3-i,
        {
            let child = source.pop(); destination.push(child); i += 1;
        }
        destination
    }
    fn empty_last() -> (r: bool)
        ensures r,
        resources peak(memory) <= 1536 {
        let mut result = make();
        let empty = result.pop().unwrap(); let absent = empty.is_none(); assert(absent); drop(empty);
        let another = result.pop().unwrap(); assert(another.is_none()); drop(another);
        let selected = result.pop().unwrap().unwrap(); drop(result);
        drop(selected); absent
    }
    fn build() -> (r: Vec<Vec<u32>>)
        ensures r.len() == 1,
        resources peak(memory) <= 2048 {
        let empty = empty_last();
        let mut result = Vec::with_capacity(1);
        let mut i = 0usize;
        while i < 1 invariant i <= 1, result.len() == i, empty, decreases 1-i, {
            if empty {
                let child = Vec::<u32>::with_capacity(4); result.push(child);
            } else {
                let child = Vec::<u32>::new(); result.push(child);
            }
            i += 1;
        }
        result
    }
    fn f() resources peak(memory) <= BOUND {
        let mut result = build(); let selected = result.pop().unwrap(); drop(result);
        let scratch = [0u8;4096];
    }";
    verifies("optional_visits", &code.replace("BOUND", "4136"));
    rejects("optional_visits_short", &code.replace("BOUND", "4135"), "memory budget exceeded");
}
