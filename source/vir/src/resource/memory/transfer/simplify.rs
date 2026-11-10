//! Normalize finite forest descriptions before exporting or instantiating them.
//! These are structural algebra identities, not guesses about symbolic inputs.

use super::*;
use crate::resource::memory::contracts;

fn call<'a>(value: &'a Expr, name: &str) -> Option<&'a Exprs> {
    let ExprX::Call { target: CallTarget::Fun(_, function, _, _, _), args, .. } = &value.x else {
        return None;
    };
    let expected = match name {
        "empty" => crate::fun!(CrateId::Vstd => "seq", "Seq"; "empty"),
        "push" => crate::fun!(CrateId::Vstd => "seq", "Seq"; "push"),
        "add" => crate::fun!(CrateId::Vstd => "seq", "Seq"; "add"),
        _ => return expr::is_operation(function, name).then_some(args),
    };
    (*function == expected).then_some(args)
}

fn empty(value: &Expr) -> bool {
    call(value, "empty").is_some()
}

fn path(value: &Expr) -> Option<Vec<Expr>> {
    if empty(value) {
        return Some(vec![]);
    }
    let args = call(value, "push")?;
    let mut path = path(&args[0])?;
    path.push(args[1].clone());
    Some(path)
}

fn make_path(span: &Span, values: &[Expr]) -> Expr {
    values.iter().fold(expr::path(span, []), |path, value| expr::push(span, path, value.clone()))
}

fn rootless(value: &Expr) -> bool {
    empty(value)
        || call(value, "runtime").is_some()
        || call(value, "descendants").is_some()
        || call(value, "repeat").is_some()
        || call(value, "take_children").is_some()
        || call(value, "prefix")
            .is_some_and(|args| path(&args[1]).is_some_and(|path| !path.is_empty()))
        || call(value, "add").is_some_and(|args| rootless(&args[0]) && rootless(&args[1]))
}

fn known_root(value: &Expr) -> Option<Expr> {
    if let Some(args) = call(value, "with_root") {
        return Some(args[1].clone());
    }
    if let Some(args) = call(value, "push") {
        if call(&args[1], "allocated").is_some_and(|record| empty(&record[0])) {
            return Some(args[1].clone());
        }
    }
    if let Some(args) = call(value, "add") {
        if rootless(&args[1]) {
            return known_root(&args[0]);
        }
    }
    None
}

pub(super) fn simplify(value: &Expr) -> Expr {
    crate::ast_visitor::map_expr_visitor(value, &|value| Ok::<_, VirErr>(node(value)))
        .expect("infallible forest normalization")
}

fn node(value: &Expr) -> Expr {
    let span = &value.span;
    if let ExprX::UnaryOpr(UnaryOpr::Field(field), record) = &value.x {
        if let Some(args) = call(record, "allocated") {
            let index = match field.field.as_str() {
                "kind" => 1,
                "bytes" => 2,
                "capacity" => 3,
                "length" => 4,
                _ => return value.clone(),
            };
            return SpannedTyped::new(span, &value.typ, args[index].x.clone());
        }
    }
    if let Some(args) = call(value, "lookup") {
        if empty(&args[1]) {
            if let Some(record) = known_root(&args[0]) {
                return record;
            }
        }
    }
    if let Some(args) = call(value, "add") {
        if empty(&args[0]) {
            return args[1].clone();
        }
        if empty(&args[1]) {
            return args[0].clone();
        }
    }
    if let Some(args) = call(value, "prefix") {
        if empty(&args[0]) {
            return args[0].clone();
        }
        if empty(&args[1]) {
            return args[0].clone();
        }
    }
    if let Some(args) = call(value, "with_root") {
        let descendants =
            expr::operation(span, "descendants", vec![args[0].clone()], expr::memory_type());
        return simplify(&expr::push(span, descendants, args[1].clone()));
    }
    if let Some(args) = call(value, "descendants") {
        let memory = &args[0];
        if rootless(memory) {
            return memory.clone();
        }
        if let Some(parts) = call(memory, "add") {
            return simplify(&expr::add(
                span,
                expr::operation(span, "descendants", vec![parts[0].clone()], expr::memory_type()),
                expr::operation(span, "descendants", vec![parts[1].clone()], expr::memory_type()),
            ));
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
                    return simplify(&previous);
                }
                if path(&record[0]).is_some_and(|path| !path.is_empty()) {
                    return simplify(&expr::push(span, previous, parts[1].clone()));
                }
            }
        }
    }
    if let Some(args) = call(value, "replace") {
        return simplify(&expr::add(
            span,
            expr::without(span, args[0].clone(), args[1].clone()),
            expr::prefix(span, args[2].clone(), args[1].clone()),
        ));
    }
    if let Some(args) = call(value, "remove_index") {
        let memory = &args[0];
        let index = &args[1];
        let apply = |memory| {
            expr::operation(span, "remove_index", vec![memory, index.clone()], expr::memory_type())
        };
        if empty(memory) {
            return memory.clone();
        }
        if let Some(parts) = call(memory, "add") {
            return simplify(&expr::add(span, apply(parts[0].clone()), apply(parts[1].clone())));
        }
        if let Some(parts) = call(memory, "push") {
            if call(&parts[1], "allocated").is_some_and(|record| empty(&record[0])) {
                return simplify(&expr::push(span, apply(parts[0].clone()), parts[1].clone()));
            }
        }
        if let Some(parts) = call(memory, "prefix") {
            if let Some(mut prefix) = path(&parts[1]) {
                if !prefix.is_empty() {
                    let slot = prefix[0].clone();
                    let shifted = super::choice(
                        span,
                        crate::ast_util::mk_ineq(span, index, &slot, InequalityOp::Lt),
                        contracts::subtract(span, slot.clone(), expr::integer(span, 1)),
                        slot.clone(),
                    );
                    prefix[0] = shifted;
                    return simplify(&super::choice(
                        span,
                        crate::ast_util::mk_eq(span, &slot, index),
                        expr::empty(span, expr::record_type()),
                        expr::prefix(span, parts[0].clone(), make_path(span, &prefix)),
                    ));
                }
            }
        }
    }
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
            return memory.clone();
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
            return simplify(&expr::operation(
                span,
                "repeat",
                vec![parts[0].clone(), parts[1].clone(), count],
                expr::memory_type(),
            ));
        }
        if let Some(parts) = call(memory, "add") {
            return simplify(&expr::add(span, apply(parts[0].clone()), apply(parts[1].clone())));
        }
        if let Some(parts) = call(memory, "push") {
            if call(&parts[1], "allocated").is_some_and(|record| empty(&record[0])) {
                return simplify(&apply(parts[0].clone()));
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
                    return simplify(&super::choice(
                        span,
                        crate::ast_util::conjoin(span, &conditions),
                        memory.clone(),
                        expr::empty(span, expr::record_type()),
                    ));
                }
            }
        }
    }
    for (operation, cutting) in [("subtree", false), ("without", true)] {
        let Some(args) = call(value, operation) else {
            continue;
        };
        let memory = &args[0];
        let selected = &args[1];
        if empty(memory) {
            return memory.clone();
        }
        let Some(selected_path) = path(selected) else {
            continue;
        };
        if selected_path.is_empty() {
            return if cutting { expr::empty(span, expr::record_type()) } else { memory.clone() };
        }
        let apply = |memory| {
            if cutting {
                expr::without(span, memory, selected.clone())
            } else {
                expr::subtree(span, memory, selected.clone())
            }
        };
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
                return simplify(&super::choice(
                    span,
                    crate::ast_util::conjoin(span, &conditions),
                    parts[0].clone(),
                    expr::empty(span, expr::record_type()),
                ));
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
                return simplify(&super::choice(
                    span,
                    crate::ast_util::conjoin(span, &conditions),
                    expr::subtree(span, parts[0].clone(), selected.clone()),
                    expr::empty(span, expr::record_type()),
                ));
            }
        }
        if let Some(parts) = call(memory, "add") {
            return simplify(&expr::add(span, apply(parts[0].clone()), apply(parts[1].clone())));
        }
        if let Some(parts) = call(memory, "push") {
            if call(&parts[1], "allocated").is_some_and(|record| empty(&record[0])) {
                let prior = apply(parts[0].clone());
                return simplify(&if cutting {
                    expr::push(span, prior, parts[1].clone())
                } else {
                    prior
                });
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
            return simplify(&SpannedTyped::new(
                span,
                &value.typ,
                ExprX::If(condition, matched, Some(unmatched)),
            ));
        }
    }
    contracts::simplify(value)
}
