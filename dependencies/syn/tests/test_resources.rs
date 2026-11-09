use quote::ToTokens;
use verus_syn::{parse_str, ItemFn};

#[test]
fn resource_clause_survives_clone_and_printing() {
    let function: ItemFn =
        parse_str("fn f(x: bool) requires x, ensures x, mem_peak <= 516, {}").unwrap();
    let copy = function.clone();
    let printed = copy.to_token_stream().to_string();
    let reparsed: ItemFn = parse_str(&printed).unwrap();
    let resources = reparsed.sig.spec.resources.unwrap();
    assert_eq!(resources.token.to_token_stream().to_string(), "mem_peak");
    assert_eq!(resources.budget.to_token_stream().to_string(), "516");
    assert!(reparsed.sig.spec.requires.is_some());
    assert!(reparsed.sig.spec.ensures.is_some());
}

#[test]
fn resource_clause_is_erased_for_rust() {
    let mut function: ItemFn = parse_str("fn f() mem_peak <= 0 {}").unwrap();
    function.sig.spec.erase_spec_fields();
    assert!(!function.to_token_stream().to_string().contains("mem_peak"));
}

#[test]
fn malformed_resource_clauses_are_rejected() {
    for text in [
        "fn f() peakmem <= 0 {}",
        "fn f() resources heap_bytes <= 8 {}",
        "fn f() resources mem_peak <= 8 {}",
        "fn f() mem_peak < 8 {}",
        "fn f() mem_peak <= -1 {}",
        "fn f() mem_peak <= 18446744073709551616 {}",
        "fn f() mem_peak <= 8u32 {}",
        "fn f() mem_peak <= 4 - 4 {}",
        "fn f() resources peak_local_storage_bytes <= 8 {}",
        "fn f() mem_peak <= mem_peak(x.field) {}",
        "fn f() mem_peak <= mem_peak(object.make()) {}",
        "fn f() mem_peak <= mem_peak() {}",
        "fn f() resources peak_memory_bytes <= 8 {}",
        "fn f() mem_peak <= mem_size::<u32>() {}",
        "fn f() mem_peak <= mem_size() {}",
        "fn f() mem_peak <= mem_size(x.field) {}",
        "fn f() mem_peak <= mem_size(make()) {}",
        "fn f() mem_peak <= mem_size(4) {}",
        "fn f() mem_peak <= mem_size(x, y) {}",
        "fn f() mem_peak <= mem_peak(x, y) {}",
        "fn f() mem_peak <= mem_peak([u32; 4]) {}",
        "fn f() mem_peak <= 8 mem_peak <= 9 {}",
    ] {
        assert!(
            parse_str::<ItemFn>(text).is_err(),
            "unexpectedly parsed {text}"
        );
    }
}

#[test]
fn resource_clause_ends_where_clause() {
    let function: ItemFn = parse_str("fn f<T>() where T: Copy mem_peak <= 0 {}").unwrap();
    assert!(function.sig.spec.resources.is_some());
}

#[test]
fn expressive_budgets_round_trip() {
    for budget in [
        "BUDGET",
        "budgets::workspace(flag, n as nat)",
        "mem_size(n) + workspace(n) * 2",
        "workspace::<u32>()",
        "mem_size(n) + n * mem_size(u32)",
        "4 + 4",
        "mem_size(x) + mem_peak(module::f)",
        "2 * (mem_size([u32; 8]) + 4u64)",
        "mem_size(crate::Buffer) + mem_size(&mut [u32]) + mem_size(())",
        "mem_size([[u32; 4]; 2]) + mem_size(&'a Buffer)",
        "mem_size(module::Alias<u32>) + mem_peak(module::f::<u32>)",
        "1 + 2 * 3 + (4 + 5) * 6",
        "mem_size((x))",
        "mem_peak(helper(false))",
        "mem_peak(module::helper(count <= 4, !flag)) + mem_peak(empty())",
    ] {
        let code = format!("fn f(x: u32) mem_peak <= {budget}, {{}}");
        let parsed: ItemFn = parse_str(&code).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn bare_budget_names_are_quantities() {
    // Name resolution and restrictions on quantities belong to the verifier.
    let parsed: ItemFn = parse_str("fn f() mem_peak <= BUDGET {}").unwrap();
    let verus_syn::ResourceExpr::Quantity(name) = parsed.sig.spec.resources.unwrap().budget else {
        panic!("expected a quantity")
    };
    assert_eq!(name, "BUDGET");
}

#[test]
fn mem_peak_clause_is_distinct_from_calls_in_other_clauses() {
    for text in [
        "fn f(x: u32) requires mem_peak(x), ensures mem_peak(x), mem_peak <= mem_size(x), {}",
        "fn f(x: u32) requires mem_peak(x) ensures mem_peak(x) mem_peak <= mem_size(x) {}",
        "fn f<T>() where T: mem_peak, mem_peak <= 0 {}",
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
        "assert(current(mem_peak) <= mem_size(local) + mem_peak(helper));",
        "assert(current(mem_peak) <= 2 * mem_size([u32; 4]));",
        "assert(current(mem_peak) <= x);",
        "assert(mem_peak(local) <= 10);",
        "assert(current(local) <= 10);",
        "assert(module::current(mem_peak) <= 10);",
        "assert(true) by { }",
    ] {
        let parsed: ItemFn = parse_str(&format!("fn f() {{ {statement} }}")).unwrap();
        let verus_syn::Stmt::Expr(verus_syn::Expr::Assert(assertion), _) = &parsed.block.stmts[0]
        else {
            panic!("expected an assertion")
        };
        assert_eq!(
            matches!(assertion.expr, verus_syn::AssertExpr::MemPeak(..)),
            statement.starts_with("assert(current(mem_peak)")
        );
        let printed = parsed.clone().to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn checkpoints_reject_proof_overrides_and_malformed_budgets() {
    for statement in [
        "assert(mem_peak <= 0);",
        "assert(current(mem_peak) < 0);",
        "assert(current(mem_peak) == 0);",
        "assert(current(mem_peak) <= mem_size(x)) by { }",
        "assert(current(mem_peak) <= 0) by(compute)",
        "assert(current(mem_peak) <= mem_size(make()));",
        "assert(current(mem_peak) <= 4 - 1);",
    ] {
        assert!(parse_str::<ItemFn>(&format!("fn f() {{ {statement} }}")).is_err());
    }
}

#[test]
fn memory_sections_round_trip_and_end_statements() {
    for body in [
        "mem_peak <= 0 {} let x = 1;",
        "mem_peak <= unknown {}",
        "mem_peak <= mem_size(x) { mem_peak <= 0 {} } mem_peak <= 0 {};",
        "#[allow(unused)] mem_peak <= 2 * (mem_size([u32; 4]) + mem_peak(helper)) { let x = 1; }",
        "let x = mem_peak <= 0 {};",
        "if true { mem_peak <= 0 {} } else { mem_peak <= 0 {} }",
    ] {
        let parsed: ItemFn = parse_str(&format!("fn f() {{ {body} }}")).unwrap();
        let printed = parsed.clone().to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
    let parsed: ItemFn = parse_str("fn f() { mem_peak(helper); }").unwrap();
    assert!(matches!(
        parsed.block.stmts[0],
        verus_syn::Stmt::Expr(verus_syn::Expr::Call(_), _)
    ));
}

#[test]
fn memory_sections_reject_invalid_budgets() {
    for body in [
        "mem_peak <= mem_size(make()) {}",
        "mem_peak <= 4 - 1 {}",
        "mem_peak <= 4;",
    ] {
        assert!(parse_str::<ItemFn>(&format!("fn f() {{ {body} }}")).is_err());
    }
}

#[test]
fn conditional_resource_budgets_round_trip() {
    for budget in [
        "mem_size(flag) + if flag { mem_size([u32; 8]) } else { mem_size([u32; 4]) }",
        "if count <= 4 { 16 } else { 32 }",
        "if flag { 4 } else { runtime_value }",
        "2 * (if a && !b { 32 } else { if b { 16 } else { 0 } })",
    ] {
        let parsed: ItemFn = parse_str(&format!("fn f() mem_peak <= {budget}, {{}}")).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn conditional_resource_budgets_require_both_formula_branches() {
    for budget in ["if flag { 4 }", "if flag { let x = 4; x } else { 0 }"] {
        assert!(parse_str::<ItemFn>(&format!("fn f() mem_peak <= {budget} {{}}")).is_err());
    }
}
