//! Generated loop facts must be proved at entry and on every reachable back edge.

use super::support::{rejects, verifies};
use crate::verify_one_file;

#[track_caller]
fn bound_pair(name: &str, code: &str, peak: u64) {
    verifies(name, &code.replace("BOUND", &format!("{peak}")));
    let short = peak - 1;
    let source = code.replace("BOUND", &format!("{short}"));
    let source = format!("use vstd::prelude::*; verus! {{ {source} }}");
    let error = verify_one_file(&format!("{name}_short"), source, &[]).unwrap_err();
    assert!(!error.errors.is_empty());
    for diagnostic in error.errors {
        assert!(diagnostic.code.is_none());
        assert!(
            diagnostic.message.contains("memory budget exceeded")
                || diagnostic.message.contains("loop invariant not satisfied"),
            "{diagnostic:?}",
            diagnostic = diagnostic
        );
        if diagnostic.message.contains("loop invariant not satisfied") {
            assert!(
                diagnostic.spans.iter().any(|span| span
                    .label
                    .as_deref()
                    .is_some_and(|label| label.starts_with("memory "))),
                "{}",
                diagnostic.rendered
            );
        }
    }
}

#[test]
fn late_allocations_follow_normal_and_continue_back_edges() {
    for (name, edge) in [
        ("fallthrough", ""),
        ("continue", "continue;"),
        ("conditional_continue", "if i < 17 { continue; }"),
    ] {
        // At visit 17: root 72 + Vec handle 24 + backing 136 + counter 1
        // + 17 retained 16-byte payloads + scratch 128 = 633 bytes.
        let code = format!(
            "fn f() resources peak(memory) <= BOUND {{
                let root = Box::new([0u8;64]);
                let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
                let mut i = 0u8;
                while i < 17
                    invariant i <= 17, values.len() == i as int,
                    decreases 17-i,
                {{
                    let child = Box::new([0u8;16]); values.push(child);
                    i += 1;
                    if i == 17 {{ let scratch = [0u8;128]; }}
                    {edge}
                }}
            }}"
        );
        bound_pair(&format!("loop_proof_{name}"), &code, 633);
    }
}

#[test]
fn partial_exits_keep_retained_allocations() {
    for (name, edge) in [("break", "break;"), ("return", "return;")] {
        let code = format!(
            "fn f() resources peak(memory) <= BOUND {{
                let root = Box::new([0u8;64]);
                let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
                let mut i = 0u8;
                while i < 17
                    invariant_except_break i <= 17, values.len() == i as int,
                    invariant values.len() <= 17,
                    decreases 17-i,
                {{
                    let child = Box::new([0u8;16]); values.push(child);
                    if i == 16 {{ let scratch = [0u8;128]; {edge} }}
                    i += 1;
                }}
            }}"
        );
        // The partial final visit retains the same 17 payloads as a full visit.
        bound_pair(&format!("loop_proof_partial_{name}"), &code, 633);
    }
}

#[test]
fn partial_breaks_export_checked_storage_for_later_allocations() {
    for count in [1, 7, 17] {
        let current = 233 + 16 * count;
        let peak = current + 128;
        let code = format!(
            "fn f() resources peak(memory) <= BOUND {{
                let root = Box::new([0u8;64]);
                let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
                let mut i = 0u8;
                while i < 17
                    invariant_except_break i < {count}, values.len() == i as int,
                    invariant values.len() <= {count},
                    decreases 17-i,
                {{
                    let child = Box::new([0u8;16]); values.push(child);
                    if i == {count} - 1 {{ break; }}
                    i += 1;
                }}
                assert(current(memory) <= {current});
                let scratch = [0u8;128];
            }}"
        );
        // Root 72 + handle/backing 160 + counter 1 + surviving payloads.
        bound_pair(&format!("partial_exit_storage_{count}"), &code, peak);
    }
    // Either exit retains its actual forest. The Boolean adds one byte to
    // the worst case, where all 17 appends complete: 633 + 1 = 634.
    bound_pair(
        "partial_or_normal_exit_storage",
        "fn f(early: bool) resources peak(memory) <= BOUND {
            let root = Box::new([0u8;64]);
            let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
            let mut i = 0u8;
            while i < 17
                invariant_except_break i <= 17, values.len() == i as int,
                invariant values.len() <= 17,
                decreases 17-i,
            {
                let child = Box::new([0u8;16]); values.push(child);
                if early && i == 6 { break; }
                i += 1;
            }
            assert(current(memory) <= 506);
            let scratch = [0u8;128];
        }",
        634,
    );
}

#[test]
fn generated_facts_do_not_hide_reachable_assertion_failures() {
    for (name, before, after, suffix) in [
        ("entry", "assert(false);", "", ""),
        ("late", "if i == 16 { assert(false); }", "", ""),
        ("continue", "", "if i == 16 { assert(false); continue; }", ""),
        ("break", "", "if i == 16 { break; }", "assert(false);"),
        ("return", "", "if i == 16 { assert(false); return; }", ""),
        ("complete", "", "", "assert(false);"),
    ] {
        let code = format!(
            "fn f() resources peak(memory) <= 1024 {{
                let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
                let mut i = 0u8;
                while i < 17
                    invariant_except_break i <= 17, values.len() == i as int,
                    invariant values.len() <= 17,
                    decreases 17-i,
                {{
                    {before}
                    let child = Box::new([0u8;16]); values.push(child);
                    {after}
                    i += 1;
                }}
                {suffix}
            }}"
        );
        rejects(&format!("loop_proof_reachable_{name}"), &code, "assertion failed");
    }
}

#[test]
fn nested_loop_entries_use_the_current_outer_visit() {
    // Both u8 counters coexist at the inner peak: 633 + 1 = 634.
    bound_pair(
        "loop_proof_nested",
        "fn f() resources peak(memory) <= BOUND {
            let root = Box::new([0u8;64]);
            let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
            let mut i = 0u8;
            while i < 17
                invariant i <= 17, values.len() == i as int,
                decreases 17-i,
            {
                let mut j = 0u8;
                while j < 1
                    invariant i < 17, j <= 1, values.len() == i as int + j as int,
                    decreases 1-j,
                {
                    let child = Box::new([0u8;16]); values.push(child);
                    j += 1;
                    if i == 16 { let scratch = [0u8;128]; }
                }
                i += 1;
            }
        }",
        634,
    );
}

#[test]
fn head_breaks_close_visit_counts_and_returned_ownership() {
    bound_pair(
        "loop_proof_head_break",
        "fn f() resources peak(memory) <= BOUND {
            let root = Box::new([0u8;64]);
            let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
            let mut i = 0u8;
            loop
                invariant i <= 17, values.len() == i as int,
                decreases 17-i,
            {
                if i >= 17 { break; }
                let child = Box::new([0u8;16]); values.push(child);
                i += 1;
                if i == 17 { let scratch = [0u8;128]; }
            }
        }",
        633,
    );

    // The returned forest retains 24 + 17*8 + 17*16 = 432 bytes. Caller root
    // 72 and scratch 2048 overlap it. The declared helper allowance also fits.
    bound_pair(
        "loop_proof_head_break_caller",
        "fn build() -> (result: Vec<Box<[u8;16]>>)
            ensures result.len() == 17,
            resources peak(memory) <= 1024,
        {
            let mut values = Vec::<Box<[u8;16]>>::with_capacity(17);
            let mut i = 0u8;
            loop
                invariant i <= 17, values.len() == i as int,
                decreases 17-i,
            {
                if i >= 17 { break; }
                let child = Box::new([0u8;16]); values.push(child); i += 1;
            }
            values
        }
        fn f() resources peak(memory) <= BOUND {
            let root = Box::new([0u8;64]);
            let values = build();
            let scratch = [0u8;2048];
        }",
        2552,
    );
}

#[test]
fn single_visits_preserve_real_entry_and_exit_facts() {
    for (name, condition, peak) in [("taken", "true", 249), ("skipped", "false", 233)] {
        // Input 1 + root 72 + Vec handle/backing 32 + scratch 128; the taken visit
        // additionally retains one 16-byte child before the later scratch.
        let code = format!(
            "fn f(enabled: bool)
                requires enabled == {condition},
                resources peak(memory) <= BOUND,
            {{
                let root = Box::new([0u8;64]);
                let mut values = Vec::<Box<[u8;16]>>::with_capacity(1);
                while enabled decreases 1nat, {{
                    let child = Box::new([0u8;16]); values.push(child);
                    break;
                }}
                let scratch = [0u8;128];
            }}"
        );
        bound_pair(&format!("loop_proof_single_{name}"), &code, peak);
    }
}

#[test]
fn user_facts_require_entry_back_edges_and_actual_exit_state() {
    for (name, initial, body, suffix, message) in [
        ("entry", "1", "i += 1;", "", "invariant not satisfied before loop"),
        ("back_edge", "0", "i += 1;", "", "invariant not satisfied at end of loop body"),
        ("continue", "0", "i += 1; continue;", "", "loop invariant not satisfied"),
        ("break", "0", "i += 1; break;", "assert(i == 0);", "assertion failed"),
    ] {
        let code = format!(
            "fn f() resources peak(memory) <= 128 {{
                let mut values = Vec::<Box<[u8;16]>>::with_capacity(2);
                let mut i = {initial}u8;
                while i < 2
                    invariant i == 0, values.len() <= 2,
                    decreases 2-i,
                {{
                    let child = Box::new([0u8;16]); values.push(child);
                    {body}
                }}
                {suffix}
            }}"
        );
        // Frozen user facts still require entry/back-edge proofs. A single
        // visit uses actual exit state instead of assuming the header invariant.
        let source = format!("use vstd::prelude::*; verus! {{ {code} }}");
        let error = verify_one_file(&format!("loop_proof_user_{name}"), source, &[]).unwrap_err();
        assert!(!error.errors.is_empty());
        for diagnostic in error.errors {
            assert!(diagnostic.code.is_none());
            assert!(
                diagnostic.message.contains(message),
                "{diagnostic:?}",
                diagnostic = diagnostic
            );
        }
    }
}
