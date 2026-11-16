//! Detached fields survive exits; cleanup retires only the remaining owners.

use super::support::verifies;
use crate::verify_one_file;

const PAIR: &str = "struct Pair { first: Box<[u8;64]>, second: Box<[u8;32]> }";
const INITIALIZE: &str =
    "let pair = Pair { first: Box::new([0u8;64]), second: Box::new([0u8;32]) };";

/// Require an independently calculated peak and reject the same body one byte
/// below it, including helper profiles that produce symbolic diagnostics.
#[track_caller]
fn check_peak(name: &str, code: &str, peak: u64) {
    let code = format!("{PAIR}\n{code}");
    verifies(name, &code.replace("BOUND", &format!("{peak}")));
    let short = peak - 1;
    let code = code.replace("BOUND", &format!("{short}"));
    let source = format!("use vstd::prelude::*; verus! {{ {code} }}");
    let err = verify_one_file(&format!("{name}_short"), source, &[]).unwrap_err();
    // Separate exits can each exceed the same allowance. Require every
    // diagnostic to be a budget failure, rather than masking other failures.
    assert!(!err.errors.is_empty());
    for error in err.errors {
        assert!(error.code.is_none());
        assert!(error.message.contains("memory budget exceeded"), "{error:?}", error = error);
    }
}

#[test]
fn partial_returns_preserve_overlap_before_cleanup() {
    for (name, parameter, body, peak) in [
        ("branch", "stop: bool", "INITIALIZE if stop { return pair.first; } pair.first", 121),
        (
            "already_moved",
            "stop: bool",
            "INITIALIZE let first = pair.first;
            if stop { return first; }
            { let scratch = [0u8;128]; }
            first",
            249,
        ),
        (
            "stored_match",
            "",
            "let option = Some(Pair {
                first: Box::new([0u8;64]), second: Box::new([0u8;32]),
            });
            match option {
                Some(pair) => { return pair.first; }
                None => { return Box::new([0u8;64]); }
            };",
            120,
        ),
        (
            "temporary_match",
            "",
            "match Some(Pair { first: Box::new([0u8;64]), second: Box::new([0u8;32]) }) {
                Some(pair) => { return pair.first; }
                None => { return Box::new([0u8;64]); }
            };",
            137,
        ),
        (
            "nested_return",
            "stop: bool",
            "INITIALIZE if stop {
                loop { let nested = Box::new([0u8;8]); return pair.first; }
            } pair.first",
            137,
        ),
        // A boxed parent adds its own 8-byte handle to the branch case.
        (
            "boxed_parent",
            "stop: bool",
            "let parent = Box::new(Pair {
                first: Box::new([0u8;64]), second: Box::new([0u8;32]),
            });
            if stop { return parent.first; } parent.first",
            129,
        ),
        // Envelope slot 25 + tag payload 16 + pair payloads 96 + pattern
        // binding 16 + result handle 8 = 161 before arm/parent cleanup.
        (
            "matched_field",
            "",
            "let parent = Envelope {
                payload: Some(Pair {
                    first: Box::new([0u8;64]), second: Box::new([0u8;32]),
                }),
                tag: Box::new([0u8;16]),
            };
            match parent.payload {
                Some(pair) => { return pair.first; }
                None => { return Box::new([0u8;64]); }
            };",
            161,
        ),
    ] {
        // Partial extraction adds an 8-byte handle to the 16-byte parent and
        // 96 payload bytes. A flag adds one; temporary match input adds 17;
        // nested scratch adds 16; post-move scratch adds 128 while both live.
        let body = body.replace("INITIALIZE", INITIALIZE);
        let code = format!(
            "struct Envelope {{ payload: Option<Pair>, tag: Box<[u8;16]> }}
            #[verifier::exec_allows_no_decreases_clause]
            fn f({parameter}) -> Box<[u8;64]> resources peak(memory) <= BOUND {{ {body} }}"
        );
        check_peak(&format!("partial_return_{name}"), &code, peak);
    }
}

#[test]
fn value_breaks_release_only_scopes_they_leave() {
    // A parent's 16-byte slot and 32-byte sibling survive a break when declared
    // outside the loop: 48 + returned child 72 + later scratch 128 = 248.
    check_peak(
        "partial_break_outer_parent",
        &format!(
            "#[verifier::exec_allows_no_decreases_clause]
            fn f() resources peak(memory) <= BOUND {{
                {INITIALIZE}
                let result = loop {{ break pair.first; }};
                assert(current(memory) <= 120);
                {{ let scratch = [0u8;128]; }}
                drop(result);
                assert(current(memory) <= 48);
            }}"
        ),
        248,
    );

    // A labelled break releases its 16-byte nested scratch, 16-byte parent,
    // and 32-byte sibling. Immediately before cleanup all overlap the result:
    // 16 + 16 + 32 + 72 = 136. Afterwards only the 72-byte child survives.
    check_peak(
        "partial_break_labelled_cleanup",
        &format!(
            "#[verifier::exec_allows_no_decreases_clause]
            fn f() resources peak(memory) <= BOUND {{
                let result = 'outer: loop {{
                    {INITIALIZE}
                    loop {{
                        let nested = Box::new([0u8;8]);
                        break 'outer pair.first;
                    }}
                }};
                assert(current(memory) <= 72);
                drop(result);
                assert(current(memory) <= 0);
            }}"
        ),
        136,
    );
}

#[test]
fn continues_cleanup_each_partially_moved_iteration() {
    for (name, exit, peak) in [
        ("plain", "if i == 1 { continue; }", 145),
        ("labelled", "loop { let nested = Box::new([0u8;8]); continue 'outer; }", 161),
    ] {
        // Retained box 24 + counter 1 + parent 16 + both payloads 96 + moved
        // handle 8 + nested scratch (0 or 16). The back edge retains only 25.
        let code = format!(
            "#[verifier::exec_allows_no_decreases_clause]
            fn f() resources peak(memory) <= BOUND {{
                let retained = Box::new([0u8;16]);
                let mut i = 0u8;
                'outer: while i < 2 invariant i <= 2, decreases 2 - i, {{
                    {INITIALIZE}
                    let first = pair.first;
                    i += 1;
                    {exit}
                }};
                assert(current(memory) <= 25);
                {{ let scratch = [0u8;112]; }}
            }}"
        );
        check_peak(&format!("partial_continue_{name}"), &code, peak);
    }
}

#[test]
fn returned_field_remains_charged_in_the_caller() {
    // The helper's 121-byte allowance dominates its exit work. In the caller,
    // the returned 72-byte child overlaps 192 bytes of scratch and a flag.
    check_peak(
        "partial_return_caller",
        &format!(
            "fn build(stop: bool) -> Box<[u8;64]> resources peak(memory) <= 121 {{
                {INITIALIZE}
                if stop {{ return pair.first; }}
                pair.first
            }}
            fn f(stop: bool) resources peak(memory) <= BOUND {{
                let result = build(stop);
                assert(current(memory) <= 73);
                {{ let scratch = [0u8;192]; }}
                drop(result);
                assert(current(memory) <= 1);
            }}"
        ),
        265,
    );
}

#[test]
fn incoming_field_returns_retire_only_the_remaining_input() {
    for (name, after, peak) in
        [("exit", "", 121), ("retained", "{ let scratch = [0u8;192]; }", 264)]
    {
        // At exit: 17 parameter bytes, 8 result bytes, and both incoming
        // payloads (96). After return: only the 72-byte child plus scratch.
        let code = format!(
            "fn take(pair: Pair, stop: bool) -> Box<[u8;64]>
                resources peak(memory) <= 25 {{
                    if stop {{ return pair.first; }}
                    pair.first
                }}
            fn f() resources peak(memory) <= BOUND {{
                {INITIALIZE}
                let result = take(pair, true);
                assert(current(memory) <= 72);
                {after}
                drop(result);
                assert(current(memory) <= 0);
            }}"
        );
        check_peak(&format!("partial_return_incoming_{name}"), &code, peak);
    }
}

#[test]
fn partial_return_from_section_reconnects_parent_charges() {
    // The parent pays 16 + 96 bytes; the section adds an 8-byte result handle.
    // Its child must reconnect to those parent charges before outer cleanup.
    check_peak(
        "partial_return_section",
        &format!(
            "fn f() -> Box<[u8;64]> resources peak(memory) <= BOUND {{
                {INITIALIZE}
                resources peak(memory) <= 8 {{ return pair.first; }}
            }}"
        ),
        120,
    );
}
