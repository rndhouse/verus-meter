//! Generated budget assertions retain their execution sites after annotation erasure.

use super::support::{rejects, verifies};
use crate::verify_one_file;

/// Keep the source contract symbolic while fixing its value by a precondition.
/// A short bound must fail at the charged operation, not at an unrelated proof.
#[track_caller]
fn bound_pair(name: &str, code: &str, peak: u64, site: &str) {
    verifies(name, &code.replace("LIMIT", &format!("{peak}")));
    let short = peak - 1;
    let code = code.replace("LIMIT", &format!("{short}"));
    let source = format!("use vstd::prelude::*; verus! {{ {code} }}");
    let err = verify_one_file(&format!("{name}_short"), source, &[]).unwrap_err();
    assert!(!err.errors.is_empty());
    for error in &err.errors {
        assert!(error.code.is_none());
        assert!(error.message.contains("memory budget exceeded"), "{error:?}", error = error);
    }
    assert!(err.errors.iter().any(|error| {
        error
            .spans
            .iter()
            .any(|span| span.is_primary && span.text.iter().any(|line| line.text.contains(site)))
    }));
}

#[test]
fn symbolic_assertions_cover_entry_declarations_and_expression_results() {
    for (name, result, body, peak, site) in [
        ("entry", "()", "", 8, "fn f("),
        ("initializer", "()", "let scratch = [0u8;64];", 72, "let scratch"),
        ("uninitialized", "()", "let scratch: [u8;64]; scratch = [0u8;64];", 72, "let scratch:"),
        ("standalone", "()", "[0u8;64];", 72, "[0u8;64]"),
        ("returned", "[u8;64]", "[0u8;64]", 72, "[0u8;64]"),
    ] {
        // The immutable u64 input contributes 8 bytes; the aggregate adds 64.
        let code = format!(
            "fn f(limit: u64) -> {result}
                requires limit == LIMIT,
                resources peak(memory) <= limit,
            {{ {body} }}"
        );
        bound_pair(&format!("obligation_{name}"), &code, peak, site);
    }
}

#[test]
fn symbolic_assertions_cover_calls_and_later_arguments() {
    bound_pair(
        "obligation_unit_call",
        "fn helper() resources peak(memory) <= 64 { let scratch = [0u8;64]; }
        fn f(limit: u64)
            requires limit == LIMIT,
            resources peak(memory) <= limit,
        { let unit = helper(); }",
        72,
        "helper();",
    );

    // The first 16-byte argument remains live while the later argument uses 64
    // bytes. The caller's input adds 8: the check must remain inside that block.
    bound_pair(
        "obligation_later_argument",
        "fn sink(first: [u8;16], later: ()) resources peak(memory) <= 16 {}
        fn f(limit: u64)
            requires limit == LIMIT,
            resources peak(memory) <= limit,
        {
            sink([0u8;16], {
                let scratch = [0u8;64];
            });
        }",
        88,
        "let scratch",
    );
}

#[test]
fn unreachable_branches_and_return_suffixes_do_not_hoist_assertions() {
    for (name, body) in [
        ("branch", "if active { let scratch = [0u8;64]; }"),
        ("return", "if !active { return; } let scratch = [0u8;64];"),
    ] {
        let code = format!(
            "fn f(limit: u64, active: bool)
                requires limit == LIMIT, active == ACTIVE,
                resources peak(memory) <= limit,
            {{ {body} }}"
        );
        // Both inputs occupy 9 bytes. Only the active path adds the 64 bytes.
        bound_pair(
            &format!("obligation_{name}_active"),
            &code.replace("ACTIVE", "true"),
            73,
            "let scratch",
        );
        bound_pair(
            &format!("obligation_{name}_skipped"),
            &code.replace("ACTIVE", "false"),
            9,
            "fn f(",
        );
    }
}

#[test]
fn loop_assertions_follow_the_body_and_back_edges() {
    let code = "fn f(limit: u64, count: u8)
        requires limit == LIMIT, count == COUNT,
        resources peak(memory) <= limit,
    {
        let mut i = 0u8;
        while i < count
            invariant i <= count, count == COUNT, limit == LIMIT,
            decreases count - i,
        {
            let scratch = [0u8;64];
            i += 1;
        }
    }";
    // Inputs and counter occupy 10 bytes; each completed iteration adds 64.
    bound_pair("obligation_loop_body", &code.replace("COUNT", "2"), 74, "let scratch");
    // The same syntactic allocation must impose no cost on a zero-visit loop.
    verifies("obligation_loop_skipped", &code.replace("COUNT", "0").replace("LIMIT", "10"));
}

#[test]
fn checkpoint_erasure_does_not_supply_unproved_logical_facts() {
    rejects(
        "obligation_no_logical_assumption",
        "fn f(limit: u64)
            requires limit == 8,
            resources peak(memory) <= limit,
        {
            assert(current(memory) <= 8);
            assert(peak(memory) <= 8);
            assert(false);
        }",
        "assertion failed",
    );
}
