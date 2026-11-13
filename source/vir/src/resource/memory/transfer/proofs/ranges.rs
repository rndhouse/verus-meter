//! Structural child-block bounds and local runtime-filter retention facts.

use super::super::{expr, simplify};
use super::{builders::generated, scope::ForestProofs};
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{contracts, model};

/// Establish a block's logical index range structurally, independently of bytes.
pub(super) fn block(
    span: &Span,
    value: &Expr,
    width: &Expr,
    proofs: &mut Vec<Stmt>,
    emitter: &mut ForestProofs,
) -> Result<(), VirErr> {
    if !emitter.needs_block(value, width) {
        return Ok(());
    }
    let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } = &value.x else {
        return Err(model::unsupported(
            span,
            "an ownership block without a structural index range",
        ));
    };
    let Some(Segment::V(name, _)) = function.path.segments.last() else { unreachable!() };
    match name.as_str() {
        "empty" => {}
        "prefix" => {
            let path = simplify::inspect::path(&args[1])
                .filter(|path| path.len() == 1)
                .ok_or_else(|| {
                    model::unsupported(span, "an ownership block without a single runtime index")
                })?;
            emitter.lemma(
                span,
                "block_bounds_prefix",
                vec![args[0].clone(), path[0].clone(), width.clone()],
                proofs,
            );
        }
        "add" => {
            block(span, &args[0], width, proofs, emitter)?;
            block(span, &args[1], width, proofs, emitter)?;
            emitter.lemma(
                span,
                "block_bounds_add",
                vec![args[0].clone(), args[1].clone(), width.clone()],
                proofs,
            );
        }
        "shift_children" => {
            let inner = contracts::subtract(span, width.clone(), args[1].clone());
            block(span, &args[0], &inner, proofs, emitter)?;
            emitter.lemma(
                span,
                "block_bounds_shift",
                vec![args[0].clone(), inner, args[1].clone()],
                proofs,
            );
        }
        "repeat" => emitter.lemma(
            span,
            "block_bounds_repeat",
            vec![args[0].clone(), args[1].clone(), args[2].clone(), width.clone()],
            proofs,
        ),
        "generate_children" => {
            let applied = generated(span, args, proofs, emitter)?;
            emitter.lemma(span, "block_bounds_generate", applied, proofs);
            let extent = contracts::add(
                span,
                args[3].clone(),
                contracts::multiply(span, args[1].clone(), args[2].clone()),
            );
            emitter.lemma(
                span,
                "block_bounds_weaken",
                vec![value.clone(), extent, width.clone()],
                proofs,
            );
        }
        "tile_children" => {
            block(span, &args[0], &args[1], proofs, emitter)?;
            emitter.lemma(span, "block_bounds_tile", args.as_ref().clone(), proofs);
            let extent = contracts::add(
                span,
                args[3].clone(),
                contracts::multiply(span, args[1].clone(), args[2].clone()),
            );
            emitter.lemma(
                span,
                "block_bounds_weaken",
                vec![value.clone(), extent, width.clone()],
                proofs,
            );
        }
        _ => return Err(model::unsupported(span, "this structural ownership block")),
    }
    emitter.complete_block(value, width);
    Ok(())
}

/// Instantiate runtime-filter cuts at the range expressions that use them.
/// Keeping this law local avoids expanding unrelated counterexample terms.
pub(super) fn retention(
    span: &Span,
    memory: &Expr,
    length: &Expr,
    proofs: &mut Vec<Stmt>,
    emitter: &mut ForestProofs,
) {
    if !emitter.needs_retention(memory, length) {
        return;
    }
    let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } = &memory.x else {
        return;
    };
    if expr::is_operation(function, "runtime") {
        emitter.lemma(span, "take_children_runtime", vec![args[0].clone(), length.clone()], proofs);
    } else if *function == crate::fun!(CrateId::Vstd => "seq", "Seq"; "add") {
        retention(span, &args[0], length, proofs, emitter);
        retention(span, &args[1], length, proofs, emitter);
    }
    emitter.complete_retention(memory, length);
}
