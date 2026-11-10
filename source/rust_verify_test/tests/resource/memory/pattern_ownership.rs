//! Pattern bindings resume ordinary ownership, including current child geometry.
use super::support::{rejects, verifies};

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

fn check_mutated_payloads(temporary: bool) {
    for (name, payload, initial, access, retained) in [
        ("vector", "Vec<u32>", "Vec::<u32>::with_capacity(4)", "", 592),
        ("box", "Box<Vec<u32>>", "Box::new(Vec::<u32>::with_capacity(4))", "", 600),
        ("field", "Payload", "Payload { values: Vec::<u32>::with_capacity(4) }", ".values", 592),
    ] {
        // A temporary match input retains its destination through the arms;
        // a named input transfers its existing slot before binding the payload.
        let peak = retained + if temporary { if name == "box" { 9 } else { 25 } } else { 0 };
        let input =
            if temporary { "match Some(child)" } else { "let option = Some(child); match option" };
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
        let name = format!("pattern_geometry_{name}_{temporary}");
        verifies(&name, &code.replace("BOUND", &format!("{peak}")));
        rejects(
            &format!("{name}_short"),
            &code.replace("BOUND", &format!("{short}", short = peak - 1)),
            "memory budget exceeded",
        );
    }
}

#[test]
fn stored_payloads_preserve_mutated_geometry_through_helpers() {
    check_mutated_payloads(false);
}

#[test]
fn temporary_payloads_preserve_mutated_geometry_through_helpers() {
    check_mutated_payloads(true);
}
