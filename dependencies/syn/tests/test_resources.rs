use quote::ToTokens;
use verus_syn::{parse_str, ItemFn};

#[test]
fn resource_clause_survives_clone_and_printing() {
    let function: ItemFn =
        parse_str("fn f(x: bool) requires x, ensures x, peakmem <= 516, {}").unwrap();
    let copy = function.clone();
    let printed = copy.to_token_stream().to_string();
    let reparsed: ItemFn = parse_str(&printed).unwrap();
    let resources = reparsed.sig.spec.resources.unwrap();
    assert_eq!(resources.token.to_token_stream().to_string(), "peakmem");
    assert_eq!(resources.budget.to_token_stream().to_string(), "516");
    assert!(reparsed.sig.spec.requires.is_some());
    assert!(reparsed.sig.spec.ensures.is_some());
}

#[test]
fn resource_clause_is_erased_for_rust() {
    let mut function: ItemFn = parse_str("fn f() peakmem <= 0 {}").unwrap();
    function.sig.spec.erase_spec_fields();
    assert!(!function.to_token_stream().to_string().contains("peakmem"));
}

#[test]
fn malformed_resource_clauses_are_rejected() {
    for text in [
        "fn f() resources heap_bytes <= 8 {}",
        "fn f() resources peakmem <= 8 {}",
        "fn f() peakmem < 8 {}",
        "fn f() peakmem <= BUDGET {}",
        "fn f() peakmem <= -1 {}",
        "fn f() peakmem <= 18446744073709551616 {}",
        "fn f() peakmem <= 8u32 {}",
        "fn f() peakmem <= 4 - 4 {}",
        "fn f() resources peak_local_storage_bytes <= 8 {}",
        "fn f() peakmem <= peakmem(x.field) {}",
        "fn f() peakmem <= peakmem(make()) {}",
        "fn f() peakmem <= peakmem() {}",
        "fn f() resources peak_memory_bytes <= 8 {}",
        "fn f() peakmem <= memory_budget(x) {}",
        "fn f() peakmem <= memory_budget::<u32>() {}",
        "fn f() peakmem <= sizeof::<u32>() {}",
        "fn f() peakmem <= sizeof() {}",
        "fn f() peakmem <= sizeof(x.field) {}",
        "fn f() peakmem <= sizeof(make()) {}",
        "fn f() peakmem <= sizeof(4) {}",
        "fn f() peakmem <= sizeof(x, y) {}",
        "fn f() peakmem <= peakmem(x, y) {}",
        "fn f() peakmem <= peakmem([u32; 4]) {}",
        "fn f() peakmem <= 8 peakmem <= 9 {}",
    ] {
        assert!(
            parse_str::<ItemFn>(text).is_err(),
            "unexpectedly parsed {text}"
        );
    }
}

#[test]
fn resource_clause_ends_where_clause() {
    let function: ItemFn = parse_str("fn f<T>() where T: Copy peakmem <= 0 {}").unwrap();
    assert!(function.sig.spec.resources.is_some());
}

#[test]
fn expressive_budgets_round_trip() {
    for budget in [
        "4 + 4",
        "sizeof(x) + peakmem(module::f)",
        "2 * (sizeof([u32; 8]) + 4u64)",
        "sizeof(crate::Buffer) + sizeof(&mut [u32]) + sizeof(())",
        "sizeof([[u32; 4]; 2]) + sizeof(&'a Buffer)",
        "sizeof(module::Alias<u32>) + peakmem(module::f::<u32>)",
        "1 + 2 * 3 + (4 + 5) * 6",
        "sizeof((x))",
    ] {
        let code = format!("fn f(x: u32) peakmem <= {budget}, {{}}");
        let parsed: ItemFn = parse_str(&code).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn peakmem_clause_is_distinct_from_calls_in_other_clauses() {
    for text in [
        "fn f(x: u32) requires peakmem(x), ensures peakmem(x), peakmem <= sizeof(x), {}",
        "fn f(x: u32) requires peakmem(x) ensures peakmem(x) peakmem <= sizeof(x) {}",
        "fn f<T>() where T: peakmem, peakmem <= 0 {}",
    ] {
        let parsed: ItemFn = parse_str(text).unwrap();
        assert!(parsed.sig.spec.resources.is_some());
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn memory_checkpoints_round_trip_alongside_logical_assertions() {
    for statement in [
        "assert(current(peakmem) <= sizeof(local) + peakmem(helper));",
        "assert(current(peakmem) <= 2 * sizeof([u32; 4]));",
        "assert(peakmem(local) <= 10);",
        "assert(current(local) <= 10);",
        "assert(module::current(peakmem) <= 10);",
        "assert(true) by { }",
    ] {
        let parsed: ItemFn = parse_str(&format!("fn f() {{ {statement} }}")).unwrap();
        let verus_syn::Stmt::Expr(verus_syn::Expr::Assert(assertion), _) = &parsed.block.stmts[0]
        else {
            panic!("expected an assertion")
        };
        assert_eq!(
            matches!(assertion.expr, verus_syn::AssertExpr::PeakMem(..)),
            statement.starts_with("assert(current(peakmem)")
        );
        let printed = parsed.clone().to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn checkpoints_reject_proof_overrides_and_runtime_budgets() {
    for statement in [
        "assert(peakmem <= 0);",
        "assert(current(peakmem) < 0);",
        "assert(current(peakmem) == 0);",
        "assert(current(peakmem) <= sizeof(x)) by { }",
        "assert(current(peakmem) <= 0) by(compute)",
        "assert(current(peakmem) <= x);",
        "assert(current(peakmem) <= sizeof(make()));",
        "assert(current(peakmem) <= 4 - 1);",
    ] {
        assert!(parse_str::<ItemFn>(&format!("fn f() {{ {statement} }}")).is_err());
    }
}
