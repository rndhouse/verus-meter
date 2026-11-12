//! Proof generation must reuse shared facts without crossing lexical guards.

use super::*;

fn span() -> Span {
    Span { raw_span: Arc::new(()), id: 0, data: Arc::new([]), as_string: "forest proofs".into() }
}

fn memory(span: &Span) -> Expr {
    expr::push(
        span,
        expr::empty(span, expr::record_type()),
        allocated(span, expr::integer(span, 16), expr::integer(span, 0), expr::integer(span, 0)),
    )
}

fn condition(span: &Span) -> Expr {
    SpannedTyped::new(
        span,
        &crate::ast_util::bool_typ(),
        ExprX::Var(VarIdent(Arc::new("flag".into()), VarIdentDisambiguate::VirTemp(0))),
    )
}

fn branches(span: &Span, memory: &Expr) -> Expr {
    SpannedTyped::new(
        span,
        &memory.typ,
        ExprX::If(condition(span), memory.clone(), Some(memory.clone())),
    )
}

fn calls(proofs: &[Stmt], name: &str) -> usize {
    let mut count = 0;
    for statement in proofs {
        let StmtX::Expr(value) = &statement.x else { continue };
        crate::ast_visitor::expr_visitor_walk(value, &mut |value| {
            count += usize::from(simplify::call(value, name).is_some());
            if matches!(value.x, ExprX::Call { .. }) {
                crate::ast_visitor::VisitorControlFlow::Return
            } else {
                crate::ast_visitor::VisitorControlFlow::Recurse
            }
        });
    }
    count
}

#[test]
fn shared_forests_do_not_repeat_allocation_proofs() {
    let span = span();
    let mut value = memory(&span);
    // A small expression graph has exponentially many tree occurrences. Each
    // occurrence still contributes bytes; proving its facts need not repeat.
    for _ in 0..16 {
        value = expr::add(
            &span,
            expr::prefix(&span, value.clone(), expr::path(&span, [-1])),
            expr::prefix(&span, value, expr::path(&span, [-2])),
        );
    }
    let mut proofs = Vec::new();
    forest(&span, &value, &mut proofs).unwrap();
    assert_eq!(calls(&proofs, "well_formed_record"), 1);
}

#[test]
fn branch_facts_do_not_escape_to_siblings_or_following_operations() {
    let span = span();
    let shared = memory(&span);
    let value = expr::add(&span, branches(&span, &shared), shared);
    let mut proofs = Vec::new();
    forest(&span, &value, &mut proofs).unwrap();
    // Each branch and the operation after the conditional need their own proof.
    assert_eq!(calls(&proofs, "well_formed_record"), 3);
}

#[test]
fn branches_reuse_unconditionally_established_facts() {
    let span = span();
    let shared = memory(&span);
    let branch = branches(&span, &shared);
    let value = expr::add(&span, shared, branch);
    let mut proofs = Vec::new();
    forest(&span, &value, &mut proofs).unwrap();
    assert_eq!(calls(&proofs, "well_formed_record"), 1);
}

#[test]
fn separate_proof_queries_establish_their_own_facts() {
    let span = span();
    let value = memory(&span);
    for _ in 0..2 {
        let mut proofs = Vec::new();
        forest(&span, &value, &mut proofs).unwrap();
        assert_eq!(calls(&proofs, "well_formed_record"), 1);
    }
}

#[test]
fn different_operations_reuse_the_same_lemma_but_keep_distinct_paths() {
    let span = span();
    let source = memory(&span);
    let mut emitter = ForestProofs::new();
    let mut proofs = Vec::new();
    let subtree = expr::subtree(&span, source.clone(), expr::path(&span, []));
    emitter.forest(&span, &subtree, &mut proofs).unwrap();
    for path in [vec![], vec![0]] {
        let lookup = expr::operation(
            &span,
            "lookup",
            vec![source.clone(), expr::path(&span, path)],
            expr::record_type(),
        );
        emitter.forest(&span, &lookup, &mut proofs).unwrap();
    }
    // Subtree selection and root lookup request the same inspect facts. The
    // later child lookup still needs a separate instance for its own path.
    assert_eq!(calls(&proofs, "inspect"), 2);
}

#[test]
fn ordered_views_visit_a_shared_removal_once() {
    let span = span();
    let mut value = expr::operation(
        &span,
        "remove_index",
        vec![memory(&span), expr::integer(&span, 0)],
        expr::memory_type(),
    );
    for _ in 0..16 {
        value = expr::add(&span, value.clone(), value);
    }
    let mut proofs = Vec::new();
    forest_views(&span, &value, &mut proofs, true).unwrap();
    assert_eq!(calls(&proofs, "remove_index_requested_views"), 1);
}

#[test]
fn ordered_views_do_not_escape_a_bound_builder() {
    let span = span();
    let name = VarIdent(Arc::new("index".into()), VarIdentDisambiguate::VirTemp(1));
    let index = SpannedTyped::new(&span, &crate::ast_util::int_typ(), ExprX::Var(name.clone()));
    let body =
        expr::operation(&span, "remove_index", vec![memory(&span), index], expr::memory_type());
    let builder = SpannedTyped::new(
        &span,
        &Arc::new(TypX::SpecFn(Arc::new(vec![crate::ast_util::int_typ()]), expr::memory_type())),
        ExprX::Closure(
            Arc::new(vec![Arc::new(VarBinderX { name, a: crate::ast_util::int_typ() })]),
            body,
        ),
    );
    let mut proofs = Vec::new();
    forest_views(&span, &builder, &mut proofs, true).unwrap();
    assert_eq!(calls(&proofs, "remove_index_requested_views"), 0);
}

#[test]
fn quantified_builders_establish_facts_under_their_own_requirements() {
    let span = span();
    let name = VarIdent(Arc::new("index".into()), VarIdentDisambiguate::VirTemp(1));
    let builder = SpannedTyped::new(
        &span,
        &Arc::new(TypX::SpecFn(Arc::new(vec![crate::ast_util::int_typ()]), expr::memory_type())),
        ExprX::Closure(
            Arc::new(vec![Arc::new(VarBinderX { name, a: crate::ast_util::int_typ() })]),
            expr::prefix(&span, memory(&span), expr::path(&span, [0])),
        ),
    );
    let mut emitter = ForestProofs::new();
    let mut proofs = Vec::new();
    for count in [2, 3] {
        let generated = expr::operation(
            &span,
            "generate_children",
            vec![
                builder.clone(),
                expr::integer(&span, 1),
                expr::integer(&span, count),
                expr::integer(&span, 0),
            ],
            expr::memory_type(),
        );
        emitter.forest(&span, &generated, &mut proofs).unwrap();
    }
    // The shared body is checked in two separate quantified proof queries.
    assert_eq!(calls(&proofs, "well_formed_record"), 2);
}
