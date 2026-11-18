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
    // Finite publications can occur literally in the invariant, outside a
    // generated builder. Reestablish their construction facts in this loop's
    // proof context; transport still treats selected records as opaque.
    let mut descriptions = Vec::new();
    builders::worker_descriptions(
        span,
        value,
        crate::ast_util::mk_bool(span, true),
        &mut descriptions,
    );
    for result in descriptions {
        emitter.forest(span, &result, proofs)?;
        proofs.push(expr::check(
            span,
            expr::operation(span, "well_formed", vec![result], crate::ast_util::bool_typ()),
            "cannot prove retained worker result validity",
        ));
    }

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
                // A source pop may consume the last remaining record after a
                // partial drain. Expose the predecessor's empty-prefix case.
                let previous = contracts::subtract(span, args[1].clone(), expr::integer(span, 1));
                emitter.lemma(span, "take_children_facts", vec![args[0].clone(), previous], proofs);
                // A cut transports the original forest unchanged. Its pop law
                // does not require expanding historical construction steps.
                return VisitorControlFlow::Return;
            }
            VisitorControlFlow::Recurse
        });
    Ok(())
}

/// Shift every child in the final block while preserving opaque observations.
/// Guard the predecessor so captures never use a negative construction index.
fn last_block(span: &Span, args: &Exprs, proofs: &mut Vec<Stmt>) {
    let ExprX::Closure(binders, body) = &args[0].x else { return };
    let previous = contracts::subtract(span, args[2].clone(), expr::integer(span, 1));
    let values = HashMap::from([(binders[0].name.clone(), previous.clone())]);
    let base =
        contracts::add(span, args[3].clone(), contracts::multiply(span, args[1].clone(), previous));
    let mut shifted = Vec::new();
    shift_block(span, &substitute(body, &values), &base, &mut shifted);
    if shifted.is_empty() {
        return;
    }
    proofs.push(crate::def::Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::If(
                crate::ast_util::mk_ineq(span, &expr::integer(span, 0), &args[2], InequalityOp::Lt),
                crate::ast_util::mk_block(span, shifted, None),
                None,
            ),
        )),
    ));
}

/// Only recurse through collection composition, never a worker's descriptions.
fn shift_block(span: &Span, block: &Expr, base: &Expr, proofs: &mut Vec<Stmt>) {
    if let Some(parts) = simplify::inspect::call(block, "add") {
        shift_block(span, &parts[0], base, proofs);
        shift_block(span, &parts[1], base, proofs);
        proofs.push(expr::lemma(
            span,
            "shift_children_add",
            vec![parts[0].clone(), parts[1].clone(), base.clone()],
        ));
    } else if let Some(parts) = simplify::inspect::call(block, "prefix") {
        if let Some(path) = simplify::inspect::path(&parts[1]).filter(|path| path.len() == 1)
            && contracts::constant(&path[0]).is_some()
        {
            proofs.push(expr::lemma(
                span,
                "shift_children_prefix",
                vec![parts[0].clone(), path[0].clone(), base.clone()],
            ));
        }
    }
}
