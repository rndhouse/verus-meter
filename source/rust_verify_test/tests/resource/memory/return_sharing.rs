use crate::verify_one_file;

fn verifies(name: &str, code: &str) {
    verify_one_file(name, format!("use vstd::prelude::*; verus! {{ {code} }}"), &[]).unwrap();
}
fn rejects(name: &str, code: &str, message: &str) {
    let err = verify_one_file(name, format!("use vstd::prelude::*; verus! {{ {code} }}"), &[])
        .unwrap_err();
    assert!(
        !err.errors.is_empty() && err.errors.iter().all(|e| e.message.contains(message)),
        "expected {}: {:?}",
        message,
        err
    );
}

#[test]
fn moved_parameter_has_one_charge() {
    verifies(
        "parameter_handoff",
        "fn f(b: Box<u32>) -> Box<u32> mem_peak <= 8 {
        assert(current(mem_peak) <= 8); b }",
    );
    rejects(
        "parameter_handoff_short",
        "fn f(b: Box<u32>) -> Box<u32> mem_peak <= 7 { b }",
        "peak 8 bytes exceeds budget 7 bytes",
    );
}
#[test]
fn moved_local_does_not_add_a_result_handle() {
    verifies(
        "local_handoff",
        "fn f() -> Box<[u8;16]> mem_peak <= 24 {
        let b = Box::new([0u8;16]); assert(current(mem_peak) <= 24); b }",
    );
    rejects(
        "local_handoff_short",
        "fn f() -> Box<[u8;16]> mem_peak <= 23 { let b = Box::new([0u8;16]); b }",
        "peak 24 bytes exceeds budget 23 bytes",
    );
}
#[test]
fn forwarding_chain_keeps_one_charge() {
    verifies(
        "forward_chain",
        "fn outer(b: Box<u32>) -> Box<u32> mem_peak <= 8 { middle(b) }
        fn middle(b: Box<u32>) -> Box<u32> mem_peak <= 8 { inner(b) }
        fn inner(b: Box<u32>) -> Box<u32> mem_peak <= 8 { b }
        fn caller() mem_peak <= 12 { let b = outer(Box::new(7u32)); }",
    );
}
#[test]
fn intermediate_moves_keep_one_charge() {
    let code = "fn f(b: Box<u32>) -> Box<u32> mem_peak <= BOUND { let next = b; next }";
    verifies("named_handles", &code.replace("BOUND", "8"));
    rejects(
        "named_handles_short",
        &code.replace("BOUND", "7"),
        "peak 8 bytes exceeds budget 7 bytes",
    );
}
#[test]
fn fresh_result_is_independent() {
    rejects(
        "independent_handle",
        "fn f(b: Box<u32>) -> Box<u32> mem_peak <= 19 { Box::new(7u32) }",
        "peak 20 bytes exceeds budget 19 bytes",
    );
    verifies(
        "independent_handle_fits",
        "fn f(b: Box<u32>) -> Box<u32> mem_peak <= 20 { Box::new(7u32) }",
    );
}
#[test]
fn noncopy_structs_follow_the_same_rule() {
    verifies(
        "struct_handoff",
        "struct Data { value: u32 } fn f(d: Data) -> Data mem_peak <= 4 { d }
        fn local() -> Data mem_peak <= 4 { let d = Data { value: 7 }; d }
        fn caller() mem_peak <= 4 { let d = f(local()); }",
    );
}
#[test]
fn copied_values_are_still_independent() {
    rejects(
        "copy_result",
        "fn f(x: u32) -> u32 mem_peak <= 4 { x }",
        "peak 8 bytes exceeds budget 4 bytes",
    );
    rejects(
        "copy_local",
        "fn f() -> [u32;4] mem_peak <= 16 { let x = [0u32;4]; x }",
        "peak 32 bytes exceeds budget 16 bytes",
    );
}
#[test]
fn dynamic_vector_return_keeps_its_reservation() {
    verifies(
        "dynamic_local_return",
        "fn make(n: usize) -> (r: Vec<u32>) requires n <= 4, ensures r.len() == 0,
        mem_peak <= 32 + n * 4 { let v = Vec::with_capacity(n); v }
        fn forward(v: Vec<u32>) -> (r: Vec<u32>) ensures r == v, mem_peak <= 24 { v }
        fn f(n: usize) requires 0 < n <= 4, mem_peak <= 56 + n * 4 {
            let a = make(n); let mut b = forward(a); b.push(7);
        }",
    );
}
#[test]
fn conditional_contract_uses_shared_entry_storage() {
    verifies(
        "conditional_handoff",
        "fn f(b: Box<u32>, flag: bool) -> Box<u32>
        mem_peak <= 9 + if flag { 4 } else { 0 },
        { if flag { let scratch = 1u32; } b }
        fn caller(flag: bool) mem_peak <= 14 + if flag { 4 } else { 0 },
        { let b = f(Box::new(7u32), flag); }",
    );
    rejects(
        "conditional_handoff_short",
        "fn f(b: Box<u32>, flag: bool) -> Box<u32>
        mem_peak <= if flag { 8 } else { 9 }, { b }",
        "memory budget exceeded",
    );
}
#[test]
fn noncopy_return_join_shares_a_common_source() {
    verifies(
        "shared_branch_source",
        "struct Data { value: u32 } fn f(d: Data, flag: bool) -> Data
        mem_peak <= 5 { if flag { d } else { d } }",
    );
}
#[test]
fn distinct_struct_result_keeps_both_values() {
    rejects(
        "distinct_struct",
        "struct Data { value: u32 } fn f(d: Data) -> Data mem_peak <= 4 { Data { value: 2 } }",
        "peak 8 bytes exceeds budget 4 bytes",
    );
}

#[test]
fn option_match_can_hand_back_a_common_source() {
    verifies(
        "match_handoff",
        "struct Data { value: u32 } fn f(d: Data, o: Option<u32>) -> Data
        mem_peak <= 13 { match o { Some(n) => d, None => d } }",
    );
}
#[test]
fn distinct_return_sources_share_existing_values() {
    verifies(
        "different_branch_sources",
        "struct Data { value: u32 } fn f(a: Data, b: Data, c: bool) -> Data
        mem_peak <= 9 { if c { a } else { b } }",
    );
}
