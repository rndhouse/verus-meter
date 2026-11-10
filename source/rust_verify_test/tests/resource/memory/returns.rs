use super::support::{rejects, verifies};
use crate::common::*;
use crate::verify_one_file;

#[test]
fn scalar_return() {
    verifies(
        "scalar_return",
        "fn increment(x: u32) -> (r: u32) requires x < 100, ensures r == x + 1, resources peak(memory) <= mem_size(x) + mem_size(u32) { x + 1 } fn caller() resources peak(memory) <= 8 { let result = increment(2); assert(result == 3); }",
    );
    rejects(
        "short_scalar_return",
        "fn f() -> u32 resources peak(memory) <= 3 { 7 }",
        "peak 4 bytes exceeds budget 3 bytes",
    );
}

#[test]
fn array_return_shares_destination() {
    verifies(
        "array_return",
        "fn make() -> (r: [u32; 4]) ensures r[0] == 7, resources peak(memory) <= mem_size([u32; 4]) { [7u32; 4] } fn caller() resources peak(memory) <= mem_size([u32; 4]) { let data = make(); assert(data[0] == 7); }",
    );
    rejects(
        "short_array_call",
        "fn make() -> [u32; 4] resources peak(memory) <= 16 { [0u32; 4] } fn caller() resources peak(memory) <= 15 { let data = make(); }",
        "peak 16 bytes exceeds budget 15 bytes",
    );
}

#[test]
fn local_remains_live_while_returning() {
    verifies(
        "return_local",
        "fn make() -> [u32; 4] resources peak(memory) <= 32 { let data = [0u32; 4]; data } fn caller() resources peak(memory) <= 32 { let data = make(); }",
    );
    rejects(
        "short_return_local",
        "fn make() -> [u32; 4] resources peak(memory) <= 31 { let data = [0u32; 4]; data }",
        "peak 32 bytes exceeds budget 31 bytes",
    );
}

#[test]
fn nested_return_calls() {
    verifies(
        "nested_return_calls",
        "fn one() -> (r: u32) ensures r == 1, resources peak(memory) <= 4 { 1 } fn sum(a: u32, b: u32) -> u32 requires a <= 10, b <= 10, resources peak(memory) <= 12 { a + b } fn caller() resources peak(memory) <= 12 { let value = sum(one(), one()); }",
    );
}

#[test]
fn call_results_remain_live_for_expression() {
    verifies(
        "call_results",
        "fn one() -> (r: u32) ensures r == 1, resources peak(memory) <= 4 { 1 } fn caller() resources peak(memory) <= 12 { let value = one() + one(); assert(value == 2); }",
    );
    rejects(
        "call_results_short",
        "fn one() -> (r: u32) ensures r == 1, resources peak(memory) <= 4 { 1 } fn caller() resources peak(memory) <= 11 { let value = one() + one(); }",
        "peak 12 bytes exceeds budget 11 bytes",
    );
}

#[test]
fn option_return() {
    verifies(
        "option_return",
        "fn maybe(flag: bool) -> (r: Option<u32>) ensures flag ==> r == Some(7), !flag ==> r == None::<u32>, resources peak(memory) <= mem_size(flag) + mem_size(Option<u32>) { if flag { Some(7) } else { None } } fn caller() resources peak(memory) <= 9 { let result = maybe(true); let value = result.unwrap(); assert(value == 7); }",
    );
}

#[test]
fn pop_result_can_be_used() {
    verifies(
        "pop_result",
        "fn f() resources peak(memory) <= 37 { let mut values = Vec::<u32>::with_capacity(1); values.push(7); let popped = values.pop(); let value = popped.unwrap(); assert(value == 7); }",
    );
}

#[test]
fn match_option_result() {
    verifies(
        "match_option",
        "fn value(o: Option<u32>) -> (r: u32) ensures o == Some(7) ==> r == 7, resources peak(memory) <= mem_size(o) + 2 * mem_size(u32) { match o { Some(n) => n, None => 0 } } fn f() resources peak(memory) <= 13 { let n = value(Some(7)); assert(n == 7); }",
    );
}

#[test]
fn match_pop_directly() {
    verifies(
        "match_pop",
        "fn f() -> (r: u32) ensures r == 7, resources peak(memory) <= 41 { let mut values = Vec::<u32>::with_capacity(1); values.push(7); match values.pop() { Some(n) => n, None => 0 } }",
    );
}

#[test]
fn option_predicates() {
    verifies(
        "option_predicates",
        "fn f(flag: bool) -> u32 resources peak(memory) <= 10 { let value: Option<u32> = if flag { Some(7) } else { None }; if value.is_some() { value.unwrap() } else { 0 } }",
    );
}

#[test]
fn owning_option_payload_remains_rejected() {
    rejects(
        "option_owner",
        "fn f() resources peak(memory) <= 100 { let v: Option<Box<u32>> = None; }",
        "owning or reference-valued Option payloads",
    );
}

#[test]
fn result_storage_starts_when_produced() {
    verifies(
        "result_checkpoint",
        "fn f() -> u32 resources peak(memory) <= 4 { assert(peak(memory) <= 0); 7 }",
    );
}

#[test]
fn struct_result() {
    verifies(
        "struct_result",
        "struct Pair { n: u32, ready: bool } fn make() -> (p: Pair) ensures p.n == 7 && p.ready, resources peak(memory) <= mem_size(Pair) { Pair { n: 7, ready: true } } fn f() resources peak(memory) <= mem_peak(make) { let p = make(); assert(p.n == 7 && p.ready); }",
    );
}

#[test]
fn tail_call_reuses_return_destination() {
    verifies(
        "tail_call",
        "fn leaf() -> u32 resources peak(memory) <= 4 { 7 } fn middle() -> u32 resources peak(memory) <= mem_peak(leaf) { leaf() } fn f() resources peak(memory) <= mem_peak(middle()) { let n = middle(); }",
    );
}

#[test]
fn discarded_return_values_are_reused() {
    verifies(
        "discarded_returns",
        "fn make() -> [u32; 4] resources peak(memory) <= 16 { [0u32; 4] } fn f() resources peak(memory) <= 16 { make(); make(); }",
    );
}

#[test]
fn returned_value_is_retained_across_next_call() {
    rejects(
        "retained_return",
        "fn make() -> [u32; 4] resources peak(memory) <= 16 { [0u32; 4] } fn work() resources peak(memory) <= 16 { let scratch = [0u32; 4]; } fn f() resources peak(memory) <= 31 { let data = make(); work(); }",
        "peak 32 bytes exceeds budget 31 bytes",
    );
}

#[test]
fn ordinary_if_and_block_results() {
    verifies(
        "if_and_block_results",
        "fn f(flag: bool) -> u32 resources peak(memory) <= 9 { if flag { let local = 7u32; local } else { 0 } }",
    );
    rejects(
        "if_result_short",
        "fn f(flag: bool) -> u32 resources peak(memory) <= 8 { if flag { let local = 7u32; local } else { 0 } }",
        "peak 9 bytes exceeds budget 8 bytes",
    );
}

#[test]
fn option_layout_and_local_construction() {
    verifies(
        "option_sizes",
        "struct Data { n: Option<u32>, ready: bool } fn f() resources peak(memory) <= 13 { let a: Option<u32> = None; let b = Some(7u32); let c: Option<Option<()>> = Some(None); let d: Option<()> = Some(()); assert(peak(memory) <= 2 * mem_size(Option<u32>) + mem_size(Option<Option<()>>) + mem_size(Option<()>)); } fn layout() resources peak(memory) <= mem_size(Data) { let d = Data { n: Some(7), ready: true }; }",
    );
}

#[test]
fn if_let_option() {
    verifies(
        "if_let_option",
        "fn f(o: Option<u32>) resources peak(memory) <= 13 { if let Some(n) = o { let seen = n; } }",
    );
}

#[test]
fn unwrap_still_requires_some() {
    rejects(
        "invalid_unwrap",
        "fn f(o: Option<u32>) -> u32 resources peak(memory) <= 9 { o.unwrap() }",
        "precondition not satisfied",
    );
}

#[test]
fn conditional_return_budget() {
    verifies(
        "conditional_return",
        "fn f(flag: bool) -> u32 resources peak(memory) <= mem_size(flag) + mem_size(u32) + if flag { 4 } else { 0 } { if flag { let local = 7u32; local } else { 0 } } fn caller(flag: bool) resources peak(memory) <= mem_size(flag) + mem_peak(f(flag)) { let result = f(flag); }",
    );
}

#[test]
fn conditional_option_match() {
    verifies(
        "conditional_option_match",
        "fn f(flag: bool, value: Option<u32>) -> u32 requires flag ==> value.is_some(), !flag ==> value.is_none(), resources peak(memory) <= mem_size(flag) + mem_size(value) + mem_size(u32) + if flag { 4 } else { 0 } { match value { Some(n) => n, None => 0 } }",
    );
}

#[test]
fn runtime_budget_return_credit() {
    verifies(
        "runtime_return",
        "fn make(cap: usize) -> (r: u32) requires 1 <= cap <= 4, ensures r == 7, resources peak(memory) <= mem_size(cap) + mem_size(u32) + mem_size(Vec<u32>) + cap * mem_size(u32) { let mut v = Vec::<u32>::with_capacity(cap); v.push(7); v.pop().unwrap() } fn caller(cap: usize) requires 1 <= cap <= 4, resources peak(memory) <= mem_size(cap) + mem_peak(make(cap)) { let value = make(cap); assert(value == 7); }",
    );
}

#[test]
fn match_binding_keeps_source_storage() {
    rejects(
        "match_binding_short",
        "fn f(value: Option<u32>) resources peak(memory) <= 8 { match value { Some(n) => { assert(n == n); }, None => {} } }",
        "peak 9 bytes exceeds budget 8 bytes",
    );
}

#[test]
fn unsupported_return_shapes() {
    rejects(
        "reference_return",
        "fn f(x: &u32) -> &u32 resources peak(memory) <= 100 { x }",
        "reference return values",
    );
    rejects(
        "early_return",
        "fn f() -> u32 resources peak(memory) <= 4 { return 7; }",
        "executable expression or control-flow exit",
    );
    rejects(
        "guarded_match",
        "fn f(o: Option<u32>) -> u32 resources peak(memory) <= 100 { match o { Some(n) if n > 0 => n, _ => 0 } }",
        "Option match guards",
    );
}

#[test]
fn return_into_existing_storage() {
    verifies(
        "return_assignment",
        "fn make() -> [u32; 4] resources peak(memory) <= 16 { [0u32; 4] } fn f() resources peak(memory) <= 16 { let mut data = [1u32; 4]; data = make(); }",
    );
}

#[test]
fn fields_and_indexes_of_returned_values() {
    verifies(
        "returned_field",
        "struct Data { n: u32, flag: bool } fn make() -> (d: Data) ensures d.n == 7, resources peak(memory) <= 5 { Data { n: 7, flag: true } } fn f() resources peak(memory) <= 9 { let n = make().n; assert(n == 7); }",
    );
    verifies(
        "returned_index",
        "fn make() -> (a: [u32; 4]) ensures a[0] == 7, resources peak(memory) <= 16 { [7u32; 4] } fn f() resources peak(memory) <= 20 { let n = make()[0]; assert(n == 7); }",
    );
    rejects(
        "returned_index_short",
        "fn make() -> [u32; 4] resources peak(memory) <= 16 { [7u32; 4] } fn f() resources peak(memory) <= 19 { let n = make()[0]; }",
        "peak 20 bytes exceeds budget 19 bytes",
    );
}

#[test]
fn borrowed_returned_temporaries_remain_rejected() {
    rejects(
        "borrow_returned",
        "fn make() -> [u32; 4] resources peak(memory) <= 16 { [7u32; 4] } fn f() resources peak(memory) <= 100 { let borrowed = &make(); }",
        "this place or borrowed temporary",
    );
}

#[test]
fn option_with_aggregate_payload() {
    verifies(
        "option_array",
        "fn make() -> (r: Option<[u32; 4]>) ensures r.is_some(), resources peak(memory) <= 17 { Some([7u32; 4]) } fn f() resources peak(memory) <= 33 { let option = make(); let array = option.unwrap(); }",
    );
}

#[test]
fn runtime_match_bindings_are_charged() {
    verifies(
        "runtime_match",
        "fn f(o: Option<usize>) resources peak(memory) <= 57 { match o { Some(cap) => { if cap <= 4 { let v = Vec::<u32>::with_capacity(cap); } }, None => {} } }",
    );
    rejects(
        "runtime_match_short",
        "fn f(o: Option<usize>) resources peak(memory) <= 56 { match o { Some(cap) => { if cap <= 4 { let v = Vec::<u32>::with_capacity(cap); } }, None => {} } }",
        "conditional memory budget exceeded",
    );
}

#[test]
fn returns_compose_with_sections() {
    verifies(
        "return_section",
        "fn make() -> [u32; 4] resources peak(memory) <= 16 { [7u32; 4] } fn f() resources peak(memory) <= 32 { let retained = [0u32; 4]; resources peak(memory) <= 16 { let result = make(); assert(peak(memory) <= 16); } }",
    );
}

#[test]
fn returned_value_examples() {
    verify_one_file(
        "returns_example",
        include_str!("../../../../../examples/resource/memory/basics/returns.rs").into(),
        &["--compile"],
    )
    .unwrap();
    verify_one_file(
        "options_example",
        include_str!("../../../../../examples/resource/memory/basics/options.rs").into(),
        &["--compile"],
    )
    .unwrap();
    let err = verify_one_file(
        "returned_buffers",
        include_str!(
            "../../../../../examples/resource/memory/expected-failures/returned_buffers.rs"
        )
        .into(),
        &[],
    )
    .unwrap_err();
    assert_vir_error_msg(err.clone(), "peak 32 bytes exceeds budget 16 bytes");
    assert!(err.errors.iter().flat_map(|e| &e.spans).any(|s| s.is_primary
        && s.text.iter().any(|line| line.text.contains("let second = make_buffer()"))));
}

#[test]
fn returned_capacity_controls_vector_allocation() {
    verifies(
        "returned_capacity",
        "fn limit() -> (n: usize) ensures n <= 4, resources peak(memory) <= mem_size(usize) { 4 } fn f() resources peak(memory) <= 48 { let capacity = limit(); let v = Vec::<u32>::with_capacity(capacity); }",
    );
}

#[test]
fn conditional_noncopy_struct_return() {
    verifies(
        "conditional_struct_return",
        "struct Data { n: u32, flag: bool } fn f(flag: bool) -> (r: Data) ensures r.n == 7, resources peak(memory) <= mem_size(flag) + mem_size(Data) + if flag { mem_size(Data) } else { 0 } { if flag { let local = Data { n: 7, flag: true }; local } else { Data { n: 7, flag: false } } }",
    );
}
