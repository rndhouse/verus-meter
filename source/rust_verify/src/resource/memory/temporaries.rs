//! Recover native receiver temporary lifetimes without changing functional VIR.
//!
//! A borrowed receiver can survive the call and later operands. Use rustc's
//! destruction scope, then require an exact executable boundary in the original
//! VIR; source proximity and last-use estimates cannot establish this relation.

use crate::context::BodyCtxt;
use rustc_hir::{Expr, ExprKind, Node, StmtKind};
use rustc_middle::middle::region::ScopeData;
use vir::{
    ast::Function,
    messages::AstId,
    resource::memory::concurrency::{ErasedOperation, Evidence, TemporaryBoundary, TemporaryScope},
};

/// Query the lifetime of the owned receiver, including explicit borrow syntax.
pub(crate) fn receiver_scope(
    bctx: &BodyCtxt<'_>,
    mut receiver: &Expr<'_>,
) -> Option<TemporaryScope> {
    // Associated-function syntax can write Arc::clone(&temporary). The owned
    // temporary is inside that explicit borrow, not the reference value.
    if let ExprKind::AddrOf(_, _, inner) = receiver.kind {
        receiver = inner;
    }
    let tcx = bctx.ctxt.tcx;
    let tree = tcx.region_scope_tree(bctx.fun_id.as_local()?);
    let scope = tree.temporary_scope(receiver.hir_id.local_id).temp_lifetime?;
    if !matches!(scope.data, ScopeData::Node | ScopeData::Remainder(_)) {
        return None;
    }
    let (span, boundary) = match tcx.hir_node(scope.hir_id(tree)?) {
        Node::Stmt(stmt) => match stmt.kind {
            StmtKind::Let(local) => (local.pat.span, TemporaryBoundary::Statement),
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                (expr.span, TemporaryBoundary::Statement)
            }
            _ => return None,
        },
        Node::LetStmt(local) => (local.pat.span, TemporaryBoundary::Statement),
        Node::Expr(expr) => (expr.span, TemporaryBoundary::Expression),
        Node::Block(block) => (block.span, TemporaryBoundary::Expression),
        _ => return None,
    };
    Some(TemporaryScope { span: bctx.ctxt.spans.to_air_span(span), boundary })
}

/// Resolve only exact, unique boundaries. Identity-erased calls can supply an
/// expression boundary even when their original source span no longer appears
/// on the surviving expression. Its source AST ID remains the proof anchor.
pub(super) fn resolve(
    function: &Function,
    operations: &std::collections::HashMap<AstId, Vec<ErasedOperation>>,
    evidence: &mut Evidence,
) {
    struct Boundaries {
        expressions: Vec<(rustc_span::Span, AstId)>,
        statements: Vec<(rustc_span::Span, AstId)>,
    }
    let mut boundaries = Boundaries { expressions: vec![], statements: vec![] };
    if let Some(body) = &function.x.body {
        let _ = vir::ast_visitor::ast_visitor_check(
            body,
            &mut boundaries,
            &mut |boundaries, _, expr| {
                if let Some(span) = crate::spans::from_raw_span(&expr.span.raw_span) {
                    boundaries.expressions.push((span, expr.span.id));
                }
                Ok::<(), ()>(())
            },
            &mut |boundaries, _, stmt| {
                if let Some(span) = crate::spans::from_raw_span(&stmt.span.raw_span) {
                    boundaries.statements.push((span, stmt.span.id));
                }
                Ok(())
            },
            &mut |_, _, _| Ok(()),
            &mut |_, _, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
        );
    }
    for (anchor, operations) in operations {
        for operation in operations {
            if let Some(span) = crate::spans::from_raw_span(&operation.span.raw_span) {
                boundaries.expressions.push((span, *anchor));
            }
        }
    }
    for operation in operations.values().flatten() {
        let Some(TemporaryScope { span, boundary }) = &operation.receiver_scope else { continue };
        let Some(span) = crate::spans::from_raw_span(&span.raw_span) else { continue };
        let candidates = match boundary {
            TemporaryBoundary::Statement => &boundaries.statements,
            TemporaryBoundary::Expression => &boundaries.expressions,
        };
        let matches: std::collections::BTreeSet<_> =
            candidates.iter().filter_map(|(source, id)| (*source == span).then_some(*id)).collect();
        if matches.len() == 1 {
            evidence.record_temporary_scope(operation.span.id, *matches.first().unwrap());
        }
    }
}
