//! Exact runtime child maps and bounded finite builder expansion.
//!
//! Symbolic and larger counts retain their verified operators rather than
//! substituting uniform descriptors or approximate byte totals.

use super::super::{choice, expr, iteration};
use super::inspect::{call, closed, empty, make_path, path, same_expression};
use super::{simplify, specialize};
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::contracts;
use std::collections::HashMap;

/// Expand small finite forests directly; larger counts keep the verified operator.
pub(in super::super) const FINITE_GENERATION_LIMIT: u32 = 8;

/// Normalize exact reverse-range maps for closed forests.
pub(super) fn reverse_children(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let Some(args) = call(value, "reverse_children").filter(|args| closed(&args[0])) {
        let memory = &args[0];
        let (start, end, base) = (&args[1], &args[2], &args[3]);
        let apply = |memory| {
            expr::operation(
                span,
                "reverse_children",
                vec![memory, start.clone(), end.clone(), base.clone()],
                expr::memory_type(),
            )
        };
        if empty(memory) || call(memory, "nonruntime").is_some() || same_expression(start, end) {
            return Some(expr::empty(span, expr::record_type()));
        }
        if let Some(parts) = call(memory, "add") {
            return Some(simplify(&expr::add(
                span,
                apply(parts[0].clone()),
                apply(parts[1].clone()),
            )));
        }
        if let Some(parts) = call(memory, "push") {
            if call(&parts[1], "allocated").is_some_and(|record| empty(&record[0])) {
                return Some(simplify(&apply(parts[0].clone())));
            }
        }
        // Reversal selects runtime children only. A previous prefix cut ending
        // exactly at this extraction's end cannot remove any selected child.
        if let Some(parts) =
            call(memory, "take_children").filter(|parts| same_expression(&parts[1], end))
        {
            return Some(simplify(&apply(parts[0].clone())));
        }
        // Keep runtime filters explicit: scoped prefix-cut proofs use them to
        // connect source descriptors to the local collection's child records.
        if let Some(parts) = call(memory, "descendants") {
            return Some(simplify(&apply(parts[0].clone())));
        }
        if let Some(parts) = call(memory, "prefix") {
            if let Some(mut path) = path(&parts[1]) {
                if let Some(index) = path.first().cloned() {
                    let selected = crate::ast_util::conjoin(
                        span,
                        &vec![
                            crate::ast_util::mk_ineq(
                                span,
                                &expr::integer(span, 0),
                                &index,
                                InequalityOp::Le,
                            ),
                            crate::ast_util::mk_ineq(span, start, &index, InequalityOp::Le),
                            crate::ast_util::mk_ineq(span, &index, end, InequalityOp::Lt),
                        ],
                    );
                    path[0] = contracts::add(
                        span,
                        base.clone(),
                        contracts::subtract(
                            span,
                            contracts::subtract(span, end.clone(), expr::integer(span, 1)),
                            index,
                        ),
                    );
                    return Some(simplify(&choice(
                        span,
                        selected,
                        expr::prefix(span, parts[0].clone(), make_path(span, &path)),
                        expr::empty(span, expr::record_type()),
                    )));
                }
            }
        }
    }
    None
}

/// Normalize runtime child offsets through finite forest constructors.
pub(super) fn shift_children(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let Some(args) = call(value, "shift_children") {
        let memory = &args[0];
        let base = &args[1];
        if empty(memory) || contracts::constant(base) == Some(0) {
            return Some(memory.clone());
        }
        if let Some(parts) = call(memory, "add") {
            return Some(simplify(&expr::add(
                span,
                expr::operation(
                    span,
                    "shift_children",
                    vec![parts[0].clone(), base.clone()],
                    expr::memory_type(),
                ),
                expr::operation(
                    span,
                    "shift_children",
                    vec![parts[1].clone(), base.clone()],
                    expr::memory_type(),
                ),
            )));
        }
        if let Some(parts) = call(memory, "prefix") {
            if let Some(mut slots) = path(&parts[1]) {
                if let Some(first) = slots.first_mut() {
                    if contracts::constant(first).is_some() {
                        *first = contracts::add(span, first.clone(), base.clone());
                        return Some(simplify(&expr::prefix(
                            span,
                            parts[0].clone(),
                            make_path(span, &slots),
                        )));
                    }
                }
            }
        }
        if let Some(parts) = call(memory, "tile_children") {
            return Some(simplify(&expr::operation(
                span,
                "tile_children",
                vec![
                    parts[0].clone(),
                    parts[1].clone(),
                    parts[2].clone(),
                    contracts::add(span, parts[3].clone(), base.clone()),
                ],
                expr::memory_type(),
            )));
        }
    }
    None
}

/// Expand bounded finite builders and normalize tiled child blocks.
pub(super) fn finite_collections(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let Some(args) = call(value, "iterate") {
        if let (ExprX::Closure(binders, body), Some(count)) =
            (&args[0].x, contracts::constant(&args[2]))
        {
            if binders.len() == 2 && count <= u64::from(FINITE_GENERATION_LIMIT) {
                let mut memory = args[1].clone();
                for index in 0..count {
                    memory = specialize(
                        body,
                        &HashMap::from([
                            (binders[0].name.clone(), expr::integer(span, index as i128)),
                            (binders[1].name.clone(), memory),
                        ]),
                    );
                }
                return Some(memory);
            }
        }
    }
    if let Some(args) = call(value, "generate_children") {
        if let (ExprX::Closure(binders, body), Some(count)) =
            (&args[0].x, contracts::constant(&args[2]))
        {
            // Small finite callers are ordinary forest expressions. Symbolic
            // counts keep the verified generator and its indexed view laws.
            if binders.len() == 1 && (0..=u64::from(FINITE_GENERATION_LIMIT)).contains(&count) {
                let mut memory = expr::empty(span, expr::record_type());
                for index in 0..count {
                    let body = specialize(
                        body,
                        &HashMap::from([(
                            binders[0].name.clone(),
                            expr::integer(span, index as i128),
                        )]),
                    );
                    let start = contracts::add(
                        span,
                        args[3].clone(),
                        contracts::multiply(
                            span,
                            args[1].clone(),
                            expr::integer(span, index as i128),
                        ),
                    );
                    memory = expr::add(
                        span,
                        memory,
                        expr::operation(
                            span,
                            "shift_children",
                            vec![body, start],
                            expr::memory_type(),
                        ),
                    );
                }
                return Some(simplify(&memory));
            }
        }
    }
    if let Some(args) = call(value, "tile_children") {
        if contracts::constant(&args[1]) == Some(1) {
            if let Some(parts) = call(&args[0], "prefix") {
                if path(&parts[1])
                    .is_some_and(|path| path.len() == 1 && contracts::constant(&path[0]) == Some(0))
                {
                    return Some(simplify(&expr::operation(
                        span,
                        "repeat",
                        vec![parts[0].clone(), args[3].clone(), args[2].clone()],
                        expr::memory_type(),
                    )));
                }
            }
        }
        if let Some(parts) = call(&args[0], "tile_children") {
            if contracts::constant(&parts[3]) == Some(0) {
                if let (Some(inner), Some(count), Some(width)) = (
                    contracts::constant(&parts[1]),
                    contracts::constant(&parts[2]),
                    contracts::constant(&args[1]),
                ) {
                    if inner.checked_mul(count) == Some(width) {
                        return Some(simplify(&expr::operation(
                            span,
                            "tile_children",
                            vec![
                                parts[0].clone(),
                                parts[1].clone(),
                                contracts::multiply(span, parts[2].clone(), args[2].clone()),
                                args[3].clone(),
                            ],
                            expr::memory_type(),
                        )));
                    }
                }
            }
        }
        if empty(&args[0]) || contracts::constant(&args[2]) == Some(0) {
            return Some(expr::empty(span, expr::record_type()));
        }
        if contracts::constant(&args[2]) == Some(1) {
            return Some(simplify(&expr::operation(
                span,
                "shift_children",
                vec![args[0].clone(), args[3].clone()],
                expr::memory_type(),
            )));
        }
    }
    None
}

/// Normalize retained child ranges while keeping symbolic runtime filters explicit.
pub(super) fn take_children(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let Some(args) = call(value, "take_children") {
        let memory = &args[0];
        let length = &args[1];
        let apply = |memory| {
            expr::operation(
                span,
                "take_children",
                vec![memory, length.clone()],
                expr::memory_type(),
            )
        };
        if empty(memory) {
            return Some(memory.clone());
        }
        if let Some(parts) = call(memory, "take_children") {
            let retained = if same_expression(&parts[1], length) {
                length.clone()
            } else {
                contracts::minimum(span, parts[1].clone(), length.clone())
            };
            return Some(simplify(&expr::operation(
                span,
                "take_children",
                vec![parts[0].clone(), retained],
                expr::memory_type(),
            )));
        }
        if call(memory, "nonruntime").is_some() {
            return Some(expr::empty(span, expr::record_type()));
        }
        // Prefix retention counts only nonnegative runtime indices. Keep the
        // conditional theorem for symbolic starts in the proof algebra.
        if let Some(parts) =
            call(memory, "repeat").filter(|parts| contracts::constant(&parts[1]).is_some())
        {
            let count = contracts::minimum(
                span,
                parts[2].clone(),
                contracts::maximum(
                    span,
                    expr::integer(span, 0),
                    contracts::subtract(span, length.clone(), parts[1].clone()),
                ),
            );
            return Some(simplify(&expr::operation(
                span,
                "repeat",
                vec![parts[0].clone(), parts[1].clone(), count],
                expr::memory_type(),
            )));
        }
        if let Some(parts) = call(memory, "add") {
            return Some(simplify(&expr::add(
                span,
                apply(parts[0].clone()),
                apply(parts[1].clone()),
            )));
        }
        if let Some(parts) = call(memory, "push") {
            if call(&parts[1], "allocated").is_some_and(|record| empty(&record[0])) {
                return Some(simplify(&apply(parts[0].clone())));
            }
        }
        if let Some(parts) = call(memory, "prefix") {
            if let Some(prefix) = path(&parts[1]) {
                if let Some(slot) = prefix.first() {
                    let conditions = vec![
                        crate::ast_util::mk_ineq(
                            span,
                            &expr::integer(span, 0),
                            slot,
                            InequalityOp::Le,
                        ),
                        crate::ast_util::mk_ineq(span, slot, length, InequalityOp::Lt),
                    ];
                    return Some(simplify(&choice(
                        span,
                        crate::ast_util::conjoin(span, &conditions),
                        memory.clone(),
                        expr::empty(span, expr::record_type()),
                    )));
                }
            }
        }
    }
    None
}

/// Expose a fixed proof window once when building the recurrence. The residual
/// operator remains exact for every larger count; no uniform descriptor or byte
/// approximation replaces it. Call specialization can discard decided branches.
pub(in super::super) fn finite_iteration(
    span: &Span,
    builder: Expr,
    initial: Expr,
    count: Expr,
    window: Option<u64>,
) -> Expr {
    let large = contracts::constant(&count)
        .map_or(window.is_none_or(|n| n > u64::from(FINITE_GENERATION_LIMIT)), |n| {
            n > u64::from(FINITE_GENERATION_LIMIT)
        });
    if large {
        if let Some(closed) = iteration::closed(span, &builder, &initial, &count) {
            return closed;
        }
    }
    let make = |count| {
        expr::operation(
            span,
            "iterate",
            vec![builder.clone(), initial.clone(), count],
            expr::memory_type(),
        )
    };
    let mut memory = simplify(&make(count.clone()));
    if contracts::constant(&count).is_some() {
        return memory;
    }
    // A smaller syntactic size hint avoids constructing unused symbolic visits.
    // It need not be a proved bound: all other counts retain the exact operator.
    let window = window
        .unwrap_or(u64::from(FINITE_GENERATION_LIMIT))
        .min(u64::from(FINITE_GENERATION_LIMIT));
    for ordinal in (0..=window).rev() {
        let amount = expr::integer(span, i128::from(ordinal));
        let selected = simplify(&make(amount.clone()));
        let condition = crate::ast_util::mk_eq(span, &count, &amount);
        memory = choice(span, condition, selected, memory);
    }
    simplify(&memory)
}
