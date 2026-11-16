//! Pattern bindings resume ordinary ownership, including current child geometry.
use super::support::{rejects, verifies};

#[test]
fn wildcard_patterns_cannot_release_ignored_owners() {
    // Both stored values and match temporaries retain ignored allocations.
    // A generous allowance cannot supply a missing ownership transition.
    for (name, code) in [
        (
            "stored_wildcard",
            "fn f() resources peak(memory) <= 80 {
                let first = Some(Box::new([0u8; 64]));
                match first { _ => {} }
                let second = Box::new([0u8; 64]);
            }",
        ),
        (
            "temporary_payload",
            "fn f() resources peak(memory) <= 90 {
                match Some(Box::new([0u8; 64])) {
                    Some(_) => { let second = Box::new([0u8; 64]); },
                    None => {},
                }
            }",
        ),
        (
            "nested_payload",
            "fn f() resources peak(memory) <= 10000 {
                let first = Some(Some(Box::new([0u8; 64])));
                match first { Some(Some(_)) => {}, Some(None) => {}, None => {} }
            }",
        ),
        (
            "helper_input",
            "fn helper(input: Option<Box<[u8; 64]>>) resources peak(memory) <= 10000 {
                match input { Some(_) => {}, None => {} }
                let second = Box::new([0u8; 64]);
            }
            fn f() resources peak(memory) <= 20000 {
                let first = Some(Box::new([0u8; 64])); helper(first);
            }",
        ),
        (
            "stored_field",
            "struct Item { child: Option<Box<[u8; 64]>>, spare: Box<[u8; 16]> }
            fn f() resources peak(memory) <= 10000 {
                let item = Item {
                    child: Some(Box::new([0u8; 64])), spare: Box::new([0u8; 16]),
                };
                match item.child { Some(_) => {}, None => {} }
            }",
        ),
        (
            "loop_local",
            "fn f() resources peak(memory) <= 10000 {
                let mut i = 0u8;
                while i < 2 invariant i <= 2, decreases 2 - i, {
                    let first = Some(Box::new([0u8; 64]));
                    match first { Some(_) => {}, None => {} }
                    let second = Box::new([0u8; 64]);
                    i += 1;
                }
            }",
        ),
    ] {
        rejects(name, code, "wildcard patterns over owning values");
    }
}

#[test]
fn named_pattern_bindings_release_owners_at_arm_exit() {
    // A named binding moves the box. The 9-byte temporary Option and 8-byte
    // payload binding overlap its 64-byte heap allocation: 81 bytes in total.
    let code = "fn f() resources peak(memory) <= BOUND {
        match Some(Box::new([0u8; 64])) {
            Some(_ignored) => {}, None => {},
        }
        let second = Box::new([0u8; 64]);
    }";
    verifies("named_pattern", &code.replace("BOUND", "81"));
    rejects("named_pattern_short", &code.replace("BOUND", "80"), "memory budget exceeded");
}

#[test]
fn stored_optional_owners_match_from_inputs_locals_and_fields() {
    verifies(
        "stored_option_moves",
        "fn consume(child: Option<Box<u32>>) resources peak(memory) <= 32 {
            match child { Some(value) => drop(value), None => {} }
        }
        fn local() resources peak(memory) <= 100 {
            let child = Box::new(1u32); let child = Some(child);
            match child { Some(value) => drop(value), None => {} }
            let scratch = [0u8;100];
        }
        struct Item { payload: Option<Box<u32>>, spare: Box<u32>, }
        fn field() resources peak(memory) <= 100 {
            let item = Item { payload: Some(Box::new(1u32)), spare: Box::new(2u32) };
            match item.payload { Some(value) => drop(value), None => {} }
            let value = *item.spare; assert(value == 2);
        }
        fn absent() resources peak(memory) <= 32 {
            let child: Option<Box<u32>> = None;
            match child { Some(value) => drop(value), None => {} }
        }",
    );
}

fn check_mutated_payload(
    name: &str,
    payload: &str,
    initial: &str,
    access: &str,
    input: &str,
    peak: u64,
) {
    let code = "struct Payload { values: Vec<u32>, }
            fn grow(child: Option<PAYLOAD>) -> (rows: Vec<PAYLOAD>)
                requires child.is_some(), child->0ACCESS.len() == 4,
                ensures rows.len() == 1, rows[0]ACCESS.len() == 5,
                resources peak(memory) <= 256 {
                let mut child = child.unwrap(); childACCESS.push(7);
                let mut rows = Vec::<PAYLOAD>::with_capacity(1); rows.push(child); rows
            }
            fn f() resources peak(memory) <= BOUND {
                let child = INITIAL;
                MATCH_INPUT {
                    Some(mut payload) => {
                        payloadACCESS.push(1); payloadACCESS.push(2);
                        payloadACCESS.push(3); payloadACCESS.push(4);
                        let option = Some(payload);
                        let rows = grow(option); let scratch = [0u8;512]; drop(rows);
                    },
                    None => {},
                }
            }"
    .replace("PAYLOAD", payload)
    .replace("INITIAL", initial)
    .replace("ACCESS", access)
    .replace("MATCH_INPUT", input);
    verifies(name, &code.replace("BOUND", &format!("{peak}")));
    rejects(
        &format!("{name}_short"),
        &code.replace("BOUND", &format!("{short}", short = peak - 1)),
        "memory budget exceeded",
    );
}

#[test]
fn stored_payloads_preserve_mutated_geometry_through_helpers() {
    // Cover a root collection and both fixed ownership edges without repeating
    // the full shape matrix for each way to produce a match input.
    for (name, payload, initial, access, peak) in [
        ("vector", "Vec<u32>", "Vec::<u32>::with_capacity(4)", "", 592),
        ("box", "Box<Vec<u32>>", "Box::new(Vec::<u32>::with_capacity(4))", "", 600),
        ("field", "Payload", "Payload { values: Vec::<u32>::with_capacity(4) }", ".values", 592),
    ] {
        check_mutated_payload(
            &format!("pattern_geometry_stored_{name}"),
            payload,
            initial,
            access,
            "let option = Some(child); match option",
            peak,
        );
    }
}

#[test]
fn temporary_payloads_preserve_mutated_geometry_through_helpers() {
    // Temporary input storage adds 25 bytes to the stored-vector case's 592.
    check_mutated_payload(
        "pattern_geometry_temporary_vector",
        "Vec<u32>",
        "Vec::<u32>::with_capacity(4)",
        "",
        "match Some(child)",
        617,
    );
}
