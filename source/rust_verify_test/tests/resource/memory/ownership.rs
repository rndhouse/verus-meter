use super::support::{rejects, verifies};
use crate::common::*;
use crate::verify_one_file;

#[test]
fn box_factory_retains_allocation() {
    let code = "fn make() -> Box<[u8;16]> resources peak(memory) <= 24 { Box::new([0u8;16]) }
        fn caller() resources peak(memory) <= BOUND { let first = make(); let second = make(); }";
    verifies("box_factory", &code.replace("BOUND", "48"));
    rejects(
        "box_factory_short",
        &code.replace("BOUND", "47"),
        "peak 48 bytes exceeds budget 47 bytes",
    );
}
#[test]
fn box_forwarding_does_not_duplicate_allocation() {
    let code = "fn caller() resources peak(memory) <= BOUND { let first = Box::new([0u8;16]); let second = forward(first); }
        fn forward(b: Box<[u8;16]>) -> Box<[u8;16]> resources peak(memory) <= 8 { b }";
    verifies("box_forward", &code.replace("BOUND", "24"));
    rejects(
        "box_forward_short",
        &code.replace("BOUND", "23"),
        "peak 24 bytes exceeds budget 23 bytes",
    );
}
#[test]
fn box_consumed_allocation_released_after_call() {
    verifies(
        "box_consumed",
        "fn consume(b: Box<[u8;16]>) resources peak(memory) <= 8 {} fn f() resources peak(memory) <= 32 {
        let first = Box::new([0u8;16]); consume(first); let second = Box::new([0u8;16]); }",
    );
}
#[test]
fn input_backing_ends_when_helper_drops_it() {
    let code =
        "fn consume(b: Box<[u8;16]>) resources peak(memory) <= 32 { drop(b); let other = Box::new([0u8;16]); }
        fn f() resources peak(memory) <= BOUND { let first = Box::new([0u8;16]); consume(first); }";
    verifies("box_consume_retains", &code.replace("BOUND", "32"));
    rejects(
        "box_consume_short",
        &code.replace("BOUND", "31"),
        "peak 32 bytes exceeds budget 31 bytes",
    );
}
#[test]
fn returned_local_and_nested_blocks() {
    verifies(
        "box_return_local",
        "fn make() -> Box<[u8;16]> resources peak(memory) <= 32 {
        let b = { let inner = Box::new([0u8;16]); inner }; b
    } fn f() resources peak(memory) <= 32 { let b = make(); }",
    );
}
#[test]
fn nested_factory_argument() {
    verifies(
        "nested_factory_argument",
        "fn make() -> Box<[u8;16]> resources peak(memory) <= 24 { Box::new([0u8;16]) }
        fn forward(b: Box<[u8;16]>) -> Box<[u8;16]> resources peak(memory) <= 8 { b }
        fn f() resources peak(memory) <= 24 { let b = forward(make()); }",
    );
}
#[test]
fn replace_owner_with_fresh_allocation() {
    verifies("replace_owner", "fn replace(b: Box<[u8;16]>) -> Box<[u8;16]> resources peak(memory) <= 32 { drop(b); Box::new([0u8;16]) }
        fn f() resources peak(memory) <= 56 { let a = Box::new([0u8;16]); let b = replace(a); let c = Box::new([0u8;16]); }");
}
#[test]
fn vector_factory_and_forwarded_capacity() {
    verifies(
        "vector_factory",
        "fn make(n: usize) -> (r: Vec<u32>) requires n <= 4, ensures r.len() == 0,
        resources peak(memory) <= 32 + n * 4 { Vec::with_capacity(n) }
        fn forward(v: Vec<u32>) -> (r: Vec<u32>) ensures r == v, resources peak(memory) <= 24 { v }
        fn f(n: usize) requires 0 < n <= 4, resources peak(memory) <= 56 + n * 4 {
            let first = make(n); let mut second = forward(first); second.push(7);
            assert(second[0] == 7);
        }",
    );
}
#[test]
fn vector_factory_lifetime() {
    let code = "fn make(n: usize) -> Vec<u32> requires n <= 4, resources peak(memory) <= 32 + n * 4 { Vec::with_capacity(n) }
        fn f() resources peak(memory) <= BOUND { let a = make(4); let b = make(4); }";
    verifies("vector_factory_lifetime", &code.replace("BOUND", "88"));
    rejects(
        "vector_factory_lifetime_short",
        &code.replace("BOUND", "87"),
        "memory budget exceeded",
    );
}
#[test]
fn incoming_vector_push_requires_bounded_growth() {
    rejects(
        "input_vec_push",
        "fn f(mut v: Vec<u32>) resources peak(memory) <= 100 { v.push(7); }",
        "memory budget exceeded",
    );
}
#[test]
fn return_capacity_cannot_reference_local() {
    rejects(
        "local_capacity",
        "fn f() -> Vec<u32> resources peak(memory) <= 100 { let n = 2usize; Vec::with_capacity(n) }",
        "returned vector capacities depending on locals",
    );
}
#[test]
fn conditional_owner_return_rejected() {
    rejects(
        "conditional_owner",
        "fn f(c: bool) -> Box<u32> resources peak(memory) <= 100 { if c { Box::new(1) } else { Box::new(2) } }",
        "conditional heap ownership results",
    );
}
#[test]
fn recursive_owner_return_rejected() {
    rejects(
        "recursive_owner",
        "fn f() -> Box<u32> resources peak(memory) <= 100 { f() }",
        "recursive memory contracts",
    );
}

#[test]
fn ownership_examples() {
    for (name, code) in [
        ("ownership", include_str!("../../../../../examples/resource/memory/ownership.rs")),
        (
            "vector_returns",
            include_str!("../../../../../examples/resource/memory/vector_returns.rs"),
        ),
    ] {
        verify_one_file(name, code.into(), &["--compile"]).unwrap();
    }
}
#[test]
fn returned_heap_failure_points_to_second_call() {
    let err = verify_one_file(
        "heap_returns",
        include_str!("../../../../../examples/resource/memory/expected-failures/heap_returns.rs")
            .into(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err.clone(), "peak 48 bytes exceeds budget 32 bytes");
    assert!(err.errors[0].spans.iter().any(|span| span.is_primary
        && span.text.iter().any(|line| line.text.contains("let second = make_buffer"))));
}

#[test]
fn multiple_owned_inputs_return_second() {
    let code =
        "fn second(a: Box<[u8;16]>, b: Box<[u8;16]>) -> Box<[u8;16]> resources peak(memory) <= 16 { b }
        fn f() resources peak(memory) <= BOUND { let a = Box::new([0u8;16]); let b = Box::new([0u8;16]);
            let c = second(a, b); let d = Box::new([0u8;16]); }";
    verifies("second_input", &code.replace("BOUND", "48"));
    rejects(
        "second_input_short",
        &code.replace("BOUND", "47"),
        "peak 48 bytes exceeds budget 47 bytes",
    );
}
#[test]
fn owning_argument_is_live_during_later_arguments() {
    let code = "fn consume(a: Box<[u8;16]>, b: Box<[u8;16]>) resources peak(memory) <= 16 {}
        fn f() resources peak(memory) <= BOUND { consume(Box::new([0u8;16]), Box::new([0u8;16])); }";
    verifies("owning_arguments", &code.replace("BOUND", "48"));
    rejects(
        "owning_arguments_short",
        &code.replace("BOUND", "47"),
        "peak 48 bytes exceeds budget 47 bytes",
    );
}
#[test]
fn forwarded_vector_keeps_original_capacity() {
    let code =
        "fn forward(v: Vec<u32>) -> (r: Vec<u32>) ensures r == v, resources peak(memory) <= 24 { v }
        fn f() resources peak(memory) <= 100 { let a = Vec::<u32>::with_capacity(1);
            let mut b = forward(a); b.push(1); b.push(2); }";
    verifies("forwarded_vector_can_grow", code);
}
#[test]
fn runtime_factory_charge_survives_call() {
    let code = "fn make(n: usize) -> Vec<u32> requires n <= 4, resources peak(memory) <= 32 + n * 4 { Vec::with_capacity(n) }
        fn f(n: usize) requires n <= 4, resources peak(memory) <= 64 + n * 4 { let a = make(n); let b = make(n); }";
    rejects("dynamic_lifetime", code, "memory budget exceeded");
}
#[test]
fn dynamic_return_through_multiple_helpers() {
    verifies("dynamic_chain", "fn caller(n: usize) requires n <= 4, resources peak(memory) <= 56 + n * 4 { let a = outer(n); }
        fn outer(n: usize) -> Vec<u32> requires n <= 4, resources peak(memory) <= 48 + n * 4 { middle(n) }
        fn middle(n: usize) -> Vec<u32> requires n <= 4, resources peak(memory) <= 40 + n * 4 { make(n) }
        fn make(n: usize) -> Vec<u32> requires n <= 4, resources peak(memory) <= 32 + n * 4 { Vec::with_capacity(n) }");
}
#[test]
fn incoming_vector_can_pop_and_forward() {
    verifies("incoming_pop", "fn pop(mut v: Vec<u32>) -> (r: Vec<u32>) ensures r.len() <= v.len(), resources peak(memory) <= 24 { v.pop(); v }
        fn f() resources peak(memory) <= 52 { let mut a = Vec::<u32>::with_capacity(1); a.push(3); let b = pop(a); }");
}
#[test]
fn consume_dynamic_vector_releases_reservation() {
    verifies(
        "consume_dynamic",
        "fn consume(v: Vec<u32>) resources peak(memory) <= 24 {}
        fn f(n: usize) requires n <= 4, resources peak(memory) <= 56 + n * 4 {
            let a = Vec::<u32>::with_capacity(n); consume(a); let b = Vec::<u32>::with_capacity(n);
        }",
    );
}
#[test]
fn owning_results_cannot_escape_protected_regions() {
    for (name, body) in [
        ("branch", "if c { consume(a); }"),
        ("section", "resources peak(memory) <= 100 { consume(a); }"),
    ] {
        rejects(
            name,
            &format!(
                "fn consume(v: Box<u32>) resources peak(memory) <= 8 {{}} fn f(c: bool) resources peak(memory) <= 200 {{ let a = Box::new(1u32); {body} }}"
            ),
            "moving or dropping an enclosing heap owner",
        );
    }
}
#[test]
fn returned_storage_is_checked_at_checkpoints() {
    rejects("returned_checkpoint", "fn make() -> Box<[u8;16]> resources peak(memory) <= 24 { Box::new([0u8;16]) }
        fn f() resources peak(memory) <= 100 { let a = make(); let b = make(); assert(peak(memory) <= 47); }", "peak(memory) assertion failed");
}
#[test]
fn local_factory_results_can_live_inside_sections() {
    verifies(
        "section_factory",
        "fn make() -> Box<[u8;16]> resources peak(memory) <= 24 { Box::new([0u8;16]) }
        fn f() resources peak(memory) <= 48 { let a = make(); resources peak(memory) <= 24 { let b = make(); } }",
    );
}
#[test]
fn discarded_factories_release_their_allocations() {
    verifies(
        "discarded_factory",
        "fn make() -> Box<[u8;16]> resources peak(memory) <= 24 { Box::new([0u8;16]) }
        fn f() resources peak(memory) <= 24 { make(); make(); }",
    );
}
#[test]
fn zero_sized_owned_payload() {
    verifies(
        "zero_sized_owner",
        "fn forward(b: Box<[u8;0]>) -> Box<[u8;0]> resources peak(memory) <= 8 { b }
        fn f() resources peak(memory) <= 16 { let a = Box::new([0u8;0]); let b = forward(a); }",
    );
}

#[test]
fn vector_input_can_be_replaced_by_a_box_without_retaining_its_buffer() {
    let code = "fn replace(v: Vec<u32>) -> Box<[u8;16]> resources peak(memory) <= 32 {
            drop(v); Box::new([0u8;16])
        }
        fn run() resources peak(memory) <= BOUND {
            let v = Vec::<u32>::with_capacity(4);
            let b = replace(v);
            let scratch = [0u8;32];
        }";
    verifies("vector_to_box", &code.replace("BOUND", "56"));
    rejects("vector_to_box_short", &code.replace("BOUND", "55"), "memory budget exceeded");
}

#[test]
fn box_input_can_be_replaced_by_a_runtime_sized_vector() {
    verifies(
        "box_to_runtime_vector",
        "
        fn replace(b: Box<[u8;16]>, n: usize) -> (v: Vec<u16>)
            requires n <= 4, ensures v.len() == 0,
            resources peak(memory) <= 40 + 2 * n,
        { drop(b); Vec::with_capacity(n) }
        fn run(n: usize) requires n <= 4, resources peak(memory) <= 64 + 2 * n {
            let b = Box::new([0u8;16]);
            let v = replace(b, n);
            drop(v);
            let scratch = [0u8;56];
        }",
    );
}
