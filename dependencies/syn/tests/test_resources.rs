use quote::ToTokens;
use verus_syn::{parse_str, ItemFn};

#[test]
fn resource_clause_survives_clone_and_printing() {
    let function: ItemFn =
        parse_str("fn f(x: bool) requires x, ensures x, resources peak(memory) <= 516, {}")
            .unwrap();
    let copy = function.clone();
    let printed = copy.to_token_stream().to_string();
    let reparsed: ItemFn = parse_str(&printed).unwrap();
    let resources = reparsed.sig.spec.resources.unwrap();
    assert!(resources.resources_token.is_some());
    assert!(resources.peak.is_some());
    assert_eq!(resources.token.to_token_stream().to_string(), "memory");
    assert_eq!(resources.budget.to_token_stream().to_string(), "516");
    assert!(reparsed.sig.spec.requires.is_some());
    assert!(reparsed.sig.spec.ensures.is_some());
}

#[test]
fn resource_clause_is_erased_for_rust() {
    let mut function: ItemFn = parse_str("fn f() resources peak(memory) <= 0 {}").unwrap();
    function.sig.spec.erase_spec_fields();
    assert!(!function.to_token_stream().to_string().contains("mem_peak"));
}

#[test]
fn malformed_resource_clauses_are_rejected() {
    for text in [
        "fn f() peakmem <= 0 {}",
        "fn f() resources heap_bytes <= 8 {}",
        "fn f() mem_peak <= 8 {}",
        "fn f() resources mem_peak <= 8 {}",
        "fn f() resources memory <= 8 {}",
        "fn f() resources peak memory <= 8 {}",
        "fn f() resources peak() <= 8 {}",
        "fn f() resources peak(other) <= 8 {}",
        "fn f() resources peak(memory, memory) <= 8 {}",
        "fn f() resources current(memory) <= 8 {}",
        "fn f() resources {}",
        "fn f() resources work <= 8 {}",
        "fn f() resources peak(memory) <= 8, mem_peak <= 9 {}",
        "fn f() resources peak(memory) < 8 {}",
        "fn f() resources peak(memory) <= -1 {}",
        "fn f() resources peak(memory) <= 18446744073709551616 {}",
        "fn f() resources peak(memory) <= 8u32 {}",
        "fn f() resources peak(memory) <= 4 - 4 {}",
        "fn f() resources peak_local_storage_bytes <= 8 {}",
        "fn f() resources peak(memory) <= mem_peak(x.field) {}",
        "fn f() resources peak(memory) <= mem_peak(object.make()) {}",
        "fn f() resources peak(memory) <= mem_peak() {}",
        "fn f() resources peak_memory_bytes <= 8 {}",
        "fn f() resources peak(memory) <= mem_size::<u32>() {}",
        "fn f() resources peak(memory) <= mem_size() {}",
        "fn f() resources peak(memory) <= mem_size(x.field) {}",
        "fn f() resources peak(memory) <= mem_size(make()) {}",
        "fn f() resources peak(memory) <= mem_size(4) {}",
        "fn f() resources peak(memory) <= mem_size(x, y) {}",
        "fn f() resources peak(memory) <= mem_peak(x, y) {}",
        "fn f() resources peak(memory) <= mem_peak([u32; 4]) {}",
        "fn f() resources peak(memory) <= 8 resources peak(memory) <= 9 {}",
    ] {
        assert!(
            parse_str::<ItemFn>(text).is_err(),
            "unexpectedly parsed {text}"
        );
    }
}

#[test]
fn resource_clause_ends_where_clause() {
    let function: ItemFn =
        parse_str("fn f<T>() where T: Copy resources peak(memory) <= 0 {}").unwrap();
    assert!(function.sig.spec.resources.is_some());
}

#[test]
fn expressive_budgets_round_trip() {
    for budget in [
        "BUDGET",
        "budgets::workspace(flag, n as nat)",
        "budgets::formula(4)(n as nat)",
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
        let code = format!("fn f(x: u32) resources peak(memory) <= {budget}, {{}}");
        let parsed: ItemFn = parse_str(&code).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn bare_budget_names_are_quantities() {
    // Name resolution and restrictions on quantities belong to the verifier.
    let parsed: ItemFn = parse_str("fn f() resources peak(memory) <= BUDGET {}").unwrap();
    let verus_syn::ResourceExpr::Quantity(name) = parsed.sig.spec.resources.unwrap().budget else {
        panic!("expected a quantity")
    };
    assert_eq!(name, "BUDGET");
}

#[test]
fn mem_peak_clause_is_distinct_from_calls_in_other_clauses() {
    for text in [
        "fn f(x: u32) requires mem_peak(x), ensures mem_peak(x), resources peak(memory) <= mem_size(x), {}",
        "fn f(x: u32) requires mem_peak(x) ensures mem_peak(x) resources peak(memory) <= mem_size(x) {}",
        "fn f<T>() where T: mem_peak, resources peak(memory) <= 0 {}",
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
        "assert(peak(memory) <= mem_size(local) + mem_peak(helper));",
        "assert(peak(memory) <= 2 * mem_size([u32; 4]));",
        "assert(peak(memory) <= x);",
        "assert(current(memory) <= mem_size(local));",
        "assert(mem_peak(local) <= 10);",
        "assert(current(local) <= 10);",
        "assert(peak(local) <= 10);",
        "assert(module::peak(memory) <= 10);",
        "assert(true) by { }",
    ] {
        let parsed: ItemFn = parse_str(&format!("fn f() {{ {statement} }}")).unwrap();
        let verus_syn::Stmt::Expr(verus_syn::Expr::Assert(assertion), _) = &parsed.block.stmts[0]
        else {
            panic!("expected an assertion")
        };
        assert_eq!(
            matches!(assertion.expr, verus_syn::AssertExpr::Memory(..)),
            statement.starts_with("assert(peak(memory)")
                || statement.starts_with("assert(current(memory)")
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
        "assert(peak(memory) < 0);",
        "assert(current(memory) < 0);",
        "assert(current(memory) <= 0) by { }",
        "assert(peak(memory) == 0);",
        "assert(peak(memory) <= mem_size(x)) by { }",
        "assert(peak(memory) <= 0) by(compute)",
        "assert(peak(memory) <= mem_size(make()));",
        "assert(peak(memory) <= 4 - 1);",
    ] {
        assert!(parse_str::<ItemFn>(&format!("fn f() {{ {statement} }}")).is_err());
    }
}

#[test]
fn memory_sections_round_trip_and_end_statements() {
    for body in [
        "resources peak(memory) <= 0 {} let x = 1;",
        "resources peak(memory) <= unknown {}",
        "resources peak(memory) <= mem_size(x) { resources peak(memory) <= 0 {} } resources peak(memory) <= 0 {};",
        "#[allow(unused)] resources peak(memory) <= 2 * (mem_size([u32; 4]) + mem_peak(helper)) { let x = 1; }",
        "let x = resources peak(memory) <= 0 {};",
        "if true { resources peak(memory) <= 0 {} } else { resources peak(memory) <= 0 {} }",
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
        "resources peak(memory) <= mem_size(make()) {}",
        "resources peak(memory) <= 4 - 1 {}",
        "resources peak(memory) <= 4;",
        "mem_peak <= 4 {}",
        "resources memory <= 4 {}",
        "resources current(memory) <= 4 {}",
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
        let parsed: ItemFn =
            parse_str(&format!("fn f() resources peak(memory) <= {budget}, {{}}")).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}

#[test]
fn conditional_resource_budgets_require_both_formula_branches() {
    for budget in ["if flag { 4 }", "if flag { let x = 4; x } else { 0 }"] {
        assert!(
            parse_str::<ItemFn>(&format!("fn f() resources peak(memory) <= {budget} {{}}"))
                .is_err()
        );
    }
}

#[test]
fn removed_capacity_clause_is_rejected() {
    assert!(parse_str::<ItemFn>(
        "fn f(v: &Vec<u32>) mem_capacity(v) >= 1, resources peak(memory) <= 8 {}"
    )
    .is_err());
}

#[test]
fn resources_remains_an_ordinary_name_outside_clauses() {
    for text in [
        "fn f(x: u32) requires resources(x), ensures resources(x), resources peak(memory) <= 4 {}",
        "fn f() { resources(); let x = resources { field: 0 }; }",
        "fn f<T>() where T: resources, resources peak(memory) <= 0 {}",
    ] {
        let parsed: ItemFn = parse_str(text).unwrap();
        let printed = parsed.to_token_stream().to_string();
        let reparsed: ItemFn = parse_str(&printed).unwrap();
        assert_eq!(printed, reparsed.to_token_stream().to_string());
    }
}
