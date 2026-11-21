use super::*;

/// Instantiate fixed child selection on the finite constructors actually
/// reached by a result. The ordinary algebra keeps these recursive operations
/// opaque to avoid unfolding unrelated collections.
pub(in crate::resource::memory) fn fixed_selection_facts(
    span: &Span,
    term: &Expr,
    facts: &mut Vec<Stmt>,
) {
    fn project(span: &Span, forest: &Expr, path: &Expr, lookup: bool, facts: &mut Vec<Stmt>) {
        use simplify::inspect::call;
        let (operation, parts) = if let Some(parts) = call(forest, "add") {
            for child in parts.iter() {
                project(span, child, path, lookup, facts);
            }
            (if lookup { "lookup_add" } else { "select_add" }, parts)
        } else if let Some(parts) = call(forest, "push") {
            project(span, &parts[0], path, lookup, facts);
            (if lookup { "lookup_push" } else { "select_push" }, parts)
        } else if let Some(parts) = call(forest, "prefix") {
            if lookup {
                facts.push(expr::lemma(
                    span,
                    "contains_prefix",
                    vec![parts[0].clone(), parts[1].clone(), path.clone()],
                ));
            }
            (if lookup { "lookup_prefix" } else { "select_prefix" }, parts)
        } else {
            if simplify::inspect::empty(forest) {
                facts.push(expr::lemma(
                    span,
                    if lookup { "lookup_empty" } else { "select_empty" },
                    vec![path.clone()],
                ));
            }
            return;
        };
        facts.push(expr::lemma(
            span,
            operation,
            vec![parts[0].clone(), parts[1].clone(), path.clone()],
        ));
    }

    let _ = crate::ast_visitor::expr_visitor_check(term, &mut |_, node| {
        use simplify::inspect::call;
        if let Some(args) = call(node, "subtree").or_else(|| call(node, "without")) {
            project(span, &args[0], &args[1], false, facts);
            if call(node, "without").is_some() {
                facts.push(expr::lemma(
                    span,
                    "cost_partition",
                    vec![args[0].clone(), args[1].clone(), expr::integer(span, 0)],
                ));
            }
        } else if let Some(args) = call(node, "lookup") {
            project(span, &args[0], &args[1], true, facts);
        }
        Ok::<(), ()>(())
    });
}
