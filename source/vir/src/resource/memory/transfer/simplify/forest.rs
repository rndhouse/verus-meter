//! Exact forest composition, branch projection, and owning-path rewrites.

use super::super::{choice, expr};
use super::inspect::{call, closed, empty, known_root, make_path, path, rootless, same_expression};
use super::simplify;
use crate::ast::*;
use crate::resource::memory::{contracts, metadata::operations};

/// Remove empty inputs from operations that cannot create allocation records.
pub(super) fn empty_forest(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    // Partial views and original-only substitutions often leave empty input
    // forests. These operators cannot create descriptors from an empty forest.
    for name in [
        "subtree",
        "without",
        "descendants",
        "runtime",
        "nonruntime",
        "remove_index",
        "prefix",
        "take_children",
        "reverse_children",
        "shift_children",
        "tile_children",
        "repeat",
    ] {
        if call(value, name).is_some_and(|args| empty(&args[0])) {
            return Some(expr::empty(span, expr::record_type()));
        }
    }
    None
}

/// Collapse identical branches and project observations through forest joins.
pub(super) fn branch_projection(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let ExprX::If(_, yes, Some(no)) = &value.x {
        if same_expression(yes, no) {
            return Some(yes.clone());
        }
    }
    // Project a branch join before inspecting its children. Otherwise selecting
    // one fixed role retains every sibling forest in both alternatives, and
    // sequential updates duplicate the entire enclosing ownership tree.
    for name in [
        "subtree",
        "without",
        "descendants",
        "runtime",
        "nonruntime",
        "lookup",
        "cost",
        "take_children",
        "reverse_children",
    ] {
        if let Some(args) = call(value, name) {
            if let ExprX::If(condition, yes, Some(no)) = &args[0].x {
                let apply = |memory| {
                    let mut args = args.as_ref().clone();
                    args[0] = memory;
                    expr::operation(span, name, args, value.typ.clone())
                };
                return Some(simplify(&choice(
                    span,
                    condition.clone(),
                    apply(yes.clone()),
                    apply(no.clone()),
                )));
            }
        }
    }
    if let ExprX::UnaryOpr(op @ UnaryOpr::Field(_), record) = &value.x {
        if let ExprX::If(condition, yes, Some(no)) = &record.x {
            let apply =
                |record| SpannedTyped::new(span, &value.typ, ExprX::UnaryOpr(op.clone(), record));
            return Some(simplify(&choice(
                span,
                condition.clone(),
                apply(yes.clone()),
                apply(no.clone()),
            )));
        }
    }
    None
}

/// Normalize root lookup, composition, descendants, and replacement.
pub(super) fn ownership(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let Some(args) = call(value, "lookup") {
        if empty(&args[1]) {
            if let Some(parts) = call(&args[0], "add") {
                if rootless(&parts[1]) {
                    return Some(simplify(&expr::lookup(span, parts[0].clone(), args[1].clone())));
                }
            }
            // Cutting a proper child or reindexing runtime siblings preserves
            // the root record, even when that record is an abstract input.
            if let Some(parts) = call(&args[0], "without") {
                if path(&parts[1]).is_some_and(|path| !path.is_empty()) {
                    return Some(simplify(&expr::lookup(span, parts[0].clone(), args[1].clone())));
                }
            }
            if let Some(parts) = call(&args[0], "remove_index") {
                return Some(simplify(&expr::lookup(span, parts[0].clone(), args[1].clone())));
            }
            if let Some(record) = known_root(&args[0]) {
                return Some(record);
            }
        }
    }
    if let Some(args) = call(value, "add") {
        if empty(&args[0]) {
            return Some(args[1].clone());
        }
        if empty(&args[1]) {
            return Some(args[0].clone());
        }
    }
    if let Some(args) = call(value, "prefix") {
        if empty(&args[0]) {
            return Some(args[0].clone());
        }
        if empty(&args[1]) {
            return Some(args[0].clone());
        }
    }
    if let Some(args) = call(value, "with_root") {
        let descendants =
            expr::operation(span, "descendants", vec![args[0].clone()], expr::memory_type());
        return Some(simplify(&expr::push(span, descendants, args[1].clone())));
    }
    if let Some(args) = call(value, "descendants") {
        let memory = &args[0];
        if rootless(memory) {
            return Some(memory.clone());
        }
        if let Some(parts) = call(memory, "add") {
            return Some(simplify(&expr::add(
                span,
                expr::operation(span, "descendants", vec![parts[0].clone()], expr::memory_type()),
                expr::operation(span, "descendants", vec![parts[1].clone()], expr::memory_type()),
            )));
        }
        if let Some(parts) = call(memory, "push") {
            if let Some(record) = call(&parts[1], "allocated") {
                let previous = expr::operation(
                    span,
                    "descendants",
                    vec![parts[0].clone()],
                    expr::memory_type(),
                );
                if empty(&record[0]) {
                    return Some(simplify(&previous));
                }
                if path(&record[0]).is_some_and(|path| !path.is_empty()) {
                    return Some(simplify(&expr::push(span, previous, parts[1].clone())));
                }
            }
        }
    }
    if let Some(args) = call(value, "replace") {
        return Some(simplify(&operations::replace(
            span,
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
        )));
    }
    None
}

/// Remove a runtime child while preserving the root and reindexing survivors.
pub(super) fn remove_child(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    if let Some(args) = call(value, "remove_index") {
        let memory = &args[0];
        let index = &args[1];
        let apply = |memory| {
            expr::operation(span, "remove_index", vec![memory, index.clone()], expr::memory_type())
        };
        if empty(memory) {
            return Some(memory.clone());
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
                return Some(simplify(&expr::push(
                    span,
                    apply(parts[0].clone()),
                    parts[1].clone(),
                )));
            }
        }
        if let Some(parts) = call(memory, "prefix") {
            if let Some(mut prefix) = path(&parts[1]) {
                if !prefix.is_empty() {
                    let slot = prefix[0].clone();
                    let shifted = choice(
                        span,
                        crate::ast_util::mk_ineq(span, index, &slot, InequalityOp::Lt),
                        contracts::subtract(span, slot.clone(), expr::integer(span, 1)),
                        slot.clone(),
                    );
                    prefix[0] = shifted;
                    return Some(simplify(&choice(
                        span,
                        crate::ast_util::mk_eq(span, &slot, index),
                        expr::empty(span, expr::record_type()),
                        expr::prefix(span, parts[0].clone(), make_path(span, &prefix)),
                    )));
                }
            }
        }
    }
    None
}

/// Select or exclude an ownership path using exact prefix and index maps.
pub(super) fn select_path(value: &Expr) -> Option<Expr> {
    let span = &value.span;
    for (operation, cutting) in [("subtree", false), ("without", true)] {
        let Some(args) = call(value, operation) else {
            continue;
        };
        let memory = &args[0];
        let selected = &args[1];
        if empty(memory) {
            return Some(memory.clone());
        }
        let Some(selected_path) = path(selected) else {
            continue;
        };
        if selected_path.is_empty() {
            return Some(if cutting {
                expr::empty(span, expr::record_type())
            } else {
                memory.clone()
            });
        }
        let apply = |memory| {
            if cutting {
                expr::without(span, memory, selected.clone())
            } else {
                expr::subtree(span, memory, selected.clone())
            }
        };
        if !cutting {
            if let Some(parts) = call(memory, "descendants") {
                return Some(simplify(&expr::subtree(span, parts[0].clone(), selected.clone())));
            }
            for (filter, op) in [("runtime", InequalityOp::Le), ("nonruntime", InequalityOp::Gt)] {
                if let Some(parts) = call(memory, filter) {
                    return Some(simplify(&choice(
                        span,
                        crate::ast_util::mk_ineq(
                            span,
                            &expr::integer(span, 0),
                            &selected_path[0],
                            op,
                        ),
                        expr::subtree(span, parts[0].clone(), selected.clone()),
                        expr::empty(span, expr::record_type()),
                    )));
                }
            }
            if let Some(parts) = call(memory, "remove_index") {
                let mut original = selected_path.clone();
                original[0] = choice(
                    span,
                    crate::ast_util::mk_ineq(span, &selected_path[0], &parts[1], InequalityOp::Lt),
                    selected_path[0].clone(),
                    contracts::add(span, selected_path[0].clone(), expr::integer(span, 1)),
                );
                return Some(simplify(&expr::subtree(
                    span,
                    parts[0].clone(),
                    make_path(span, &original),
                )));
            }
            if let Some(parts) = call(memory, "without") {
                if let Some(cut) = path(&parts[1]) {
                    let comparisons: Vec<_> = cut
                        .iter()
                        .zip(&selected_path)
                        .map(|(a, b)| simplify(&crate::ast_util::mk_eq(span, a, b)))
                        .collect();
                    if comparisons
                        .iter()
                        .all(|value| matches!(value.x, ExprX::Const(Constant::Bool(true))))
                    {
                        if cut.len() <= selected_path.len() {
                            return Some(expr::empty(span, expr::record_type()));
                        }
                        return Some(simplify(&expr::without(
                            span,
                            expr::subtree(span, parts[0].clone(), selected.clone()),
                            make_path(span, &cut[selected_path.len()..]),
                        )));
                    }
                    if comparisons
                        .iter()
                        .any(|value| matches!(value.x, ExprX::Const(Constant::Bool(false))))
                    {
                        return Some(simplify(&expr::subtree(
                            span,
                            parts[0].clone(),
                            selected.clone(),
                        )));
                    }
                }
            }
        }
        if !cutting {
            if let Some(parts) = call(memory, "shift_children") {
                if contracts::constant(&selected_path[0]).is_some() {
                    let mut relative = selected_path.clone();
                    relative[0] = contracts::subtract(span, relative[0].clone(), parts[1].clone());
                    return Some(simplify(&choice(
                        span,
                        crate::ast_util::mk_ineq(
                            span,
                            &parts[1],
                            &selected_path[0],
                            InequalityOp::Le,
                        ),
                        expr::subtree(span, parts[0].clone(), make_path(span, &relative)),
                        expr::empty(span, expr::record_type()),
                    )));
                }
            }
            // Whole-range transfers have an exact inverse index map. Select
            // the original child directly before introducing general range view
            // facts; this also keeps failing-budget queries finite.
            if let Some(parts) = call(memory, "reverse_children").filter(|parts| closed(&parts[0]))
            {
                let index = contracts::subtract(
                    span,
                    contracts::add(
                        span,
                        parts[3].clone(),
                        contracts::subtract(span, parts[2].clone(), expr::integer(span, 1)),
                    ),
                    selected_path[0].clone(),
                );
                let conditions = crate::ast_util::conjoin(
                    span,
                    &vec![
                        crate::ast_util::mk_ineq(
                            span,
                            &expr::integer(span, 0),
                            &index,
                            InequalityOp::Le,
                        ),
                        crate::ast_util::mk_ineq(span, &parts[1], &index, InequalityOp::Le),
                        crate::ast_util::mk_ineq(span, &index, &parts[2], InequalityOp::Lt),
                    ],
                );
                let mut relative = selected_path.clone();
                relative[0] = index;
                return Some(simplify(&choice(
                    span,
                    conditions,
                    expr::subtree(span, parts[0].clone(), make_path(span, &relative)),
                    expr::empty(span, expr::record_type()),
                )));
            }
            // Ordered blocks are built with precisely their declared width.
            // Select one block arithmetically rather than expanding its count.
            if let Some(parts) = call(memory, "tile_children") {
                if let (Some(width), Some(start), Some(index)) = (
                    contracts::constant(&parts[1]),
                    contracts::constant(&parts[3]),
                    contracts::constant(&selected_path[0]),
                ) {
                    if width > 0 && index >= start {
                        let iteration = (index - start) / width;
                        let mut relative = selected_path.clone();
                        relative[0] = contracts::literal(span, (index - start) % width);
                        return Some(simplify(&choice(
                            span,
                            crate::ast_util::mk_ineq(
                                span,
                                &contracts::literal(span, iteration),
                                &parts[2],
                                InequalityOp::Lt,
                            ),
                            expr::subtree(span, parts[0].clone(), make_path(span, &relative)),
                            expr::empty(span, expr::record_type()),
                        )));
                    } else if index < start {
                        return Some(expr::empty(span, expr::record_type()));
                    }
                }
            }
        }
        if !cutting && selected_path.len() == 1 {
            let index = &selected_path[0];
            if let Some(parts) = call(memory, "repeat") {
                let conditions = vec![
                    crate::ast_util::mk_ineq(span, &parts[1], index, InequalityOp::Le),
                    crate::ast_util::mk_ineq(
                        span,
                        index,
                        &contracts::add(span, parts[1].clone(), parts[2].clone()),
                        InequalityOp::Lt,
                    ),
                ];
                return Some(simplify(&choice(
                    span,
                    crate::ast_util::conjoin(span, &conditions),
                    parts[0].clone(),
                    expr::empty(span, expr::record_type()),
                )));
            }
            if let Some(parts) = call(memory, "take_children") {
                let conditions = vec![
                    crate::ast_util::mk_ineq(
                        span,
                        &expr::integer(span, 0),
                        index,
                        InequalityOp::Le,
                    ),
                    crate::ast_util::mk_ineq(span, index, &parts[1], InequalityOp::Lt),
                ];
                return Some(simplify(&choice(
                    span,
                    crate::ast_util::conjoin(span, &conditions),
                    expr::subtree(span, parts[0].clone(), selected.clone()),
                    expr::empty(span, expr::record_type()),
                )));
            }
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
                let prior = apply(parts[0].clone());
                return Some(simplify(&if cutting {
                    expr::push(span, prior, parts[1].clone())
                } else {
                    prior
                }));
            }
        }
        if let Some(parts) = call(memory, "prefix") {
            let Some(prefix) = path(&parts[1]) else {
                continue;
            };
            let count = prefix.len().min(selected_path.len());
            let equalities = prefix
                .iter()
                .zip(selected_path.iter())
                .take(count)
                .map(|(a, b)| crate::ast_util::mk_eq(span, a, b))
                .collect();
            let condition = contracts::simplify(&crate::ast_util::conjoin(span, &equalities));
            let matched = if selected_path.len() >= prefix.len() {
                let suffix = make_path(span, &selected_path[prefix.len()..]);
                if cutting {
                    expr::prefix(
                        span,
                        expr::without(span, parts[0].clone(), suffix),
                        parts[1].clone(),
                    )
                } else {
                    expr::subtree(span, parts[0].clone(), suffix)
                }
            } else if cutting {
                expr::empty(span, expr::record_type())
            } else {
                expr::prefix(
                    span,
                    parts[0].clone(),
                    make_path(span, &prefix[selected_path.len()..]),
                )
            };
            let unmatched =
                if cutting { memory.clone() } else { expr::empty(span, expr::record_type()) };
            return Some(simplify(&SpannedTyped::new(
                span,
                &value.typ,
                ExprX::If(condition, matched, Some(unmatched)),
            )));
        }
    }
    None
}
