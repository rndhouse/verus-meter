//! One-step collection laws for exact loop membership invariants.
//!
//! Constructors establish descriptor properties separately. These transition
//! proofs treat each child's observations as opaque and preserve them verbatim.

use super::*;
use crate::ast_visitor::{VisitorControlFlow, expr_visitor_dfs};
use crate::resource::memory::contracts;
use std::collections::{HashMap, HashSet};

pub(in super::super) fn prefix(
    span: &Span,
    value: &Expr,
    proofs: &mut Vec<Stmt>,
) -> Result<(), VirErr> {
    let mut emitter = ForestProofs::new();
    emitter.forest(span, value, proofs)?;
    let mut visited = HashSet::new();
    let _ =
        expr_visitor_dfs::<(), _>(value, &mut air::scope_map::ScopeMap::new(), &mut |_, value| {
            if !visited.insert(Arc::as_ptr(value) as usize)
                || matches!(value.x, ExprX::Closure(..))
                || simplify::inspect::call(value, "worker_observation").is_some()
            {
                return VisitorControlFlow::Return;
            }
            if let Some(args) = simplify::inspect::call(value, "generate_children") {
                emitter.lemma(span, "generate_children_step", args.as_ref().clone(), proofs);
                last_block(span, args, proofs);
            }
            if let Some(args) = simplify::inspect::call(value, "take_children") {
                emitter.lemma(span, "take_children_pop", args.as_ref().clone(), proofs);
            }
            VisitorControlFlow::Recurse
        });
    Ok(())
}

/// A singleton block's final shift changes its runtime slot alone. Guard the
/// predecessor so capture expressions never use a negative construction index.
fn last_block(span: &Span, args: &Exprs, proofs: &mut Vec<Stmt>) {
    let ExprX::Closure(binders, body) = &args[0].x else { return };
    let Some(parts) = simplify::inspect::call(body, "prefix") else { return };
    let Some(path) = simplify::inspect::path(&parts[1]).filter(|path| path.len() == 1) else {
        return;
    };
    if contracts::constant(&path[0]).is_none() {
        return;
    }
    let previous = contracts::subtract(span, args[2].clone(), expr::integer(span, 1));
    let values = HashMap::from([(binders[0].name.clone(), previous.clone())]);
    let lemma = expr::lemma(
        span,
        "shift_children_prefix",
        vec![
            substitute(&parts[0], &values),
            path[0].clone(),
            contracts::add(
                span,
                args[3].clone(),
                contracts::multiply(span, args[1].clone(), previous),
            ),
        ],
    );
    proofs.push(crate::def::Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::If(
                crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &args[2], InequalityOp::Lt),
                crate::ast_util::mk_block(span, vec![lemma], None),
                None,
            ),
        )),
    ));
}
