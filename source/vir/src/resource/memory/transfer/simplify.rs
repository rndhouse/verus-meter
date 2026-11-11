//! Normalize finite forest descriptions before exporting or instantiating them.
//! These are structural algebra identities, not guesses about symbolic inputs.

use super::*;
use crate::resource::memory::contracts;
use std::sync::Arc;

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

pub(super) fn path(value: &Expr) -> Option<Vec<Expr>> {
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
        || call(value, "tile_children").is_some()
        || call(value, "shift_children").is_some_and(|args| rootless(&args[0]))
        || call(value, "take_children").is_some()
        || call(value, "reverse_children").is_some()
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

/// Normalize a shared expression graph once per node. Branch composition reuses
/// entry forests; preserving that sharing avoids repeatedly expanding unchanged
/// subtrees and skips alternatives already decided by caller specialization.
pub(super) fn simplify(value: &Expr) -> Expr {
    rewrite(value, None)
}

pub(super) fn specialize(value: &Expr, values: &HashMap<VarIdent, Expr>) -> Expr {
    rewrite(value, Some(values))
}

fn rewrite(value: &Expr, values: Option<&HashMap<VarIdent, Expr>>) -> Expr {
    use crate::ast_visitor::{AstVisitor, NoScoper, Rewrite};
    struct Normalize<'a> {
        /// Immutable caller observations replacing template symbols.
        values: Option<&'a HashMap<VarIdent, Expr>>,
        /// Normalized results keyed by nodes in the still-live input graph.
        cache: HashMap<usize, Expr>,
    }
    impl AstVisitor<Rewrite, VirErr, NoScoper> for Normalize<'_> {
        fn visit_expr(&mut self, value: &Expr) -> Result<Expr, VirErr> {
            let key = Arc::as_ptr(value) as usize;
            if let Some(value) = self.cache.get(&key) {
                return Ok(value.clone());
            }
            if let ExprX::Var(name) = &value.x {
                if let Some(replacement) = self.values.and_then(|values| values.get(name)) {
                    let result = simplify(replacement);
                    self.cache.insert(key, result.clone());
                    return Ok(result);
                }
            }
            if let ExprX::If(condition, yes, Some(no)) = &value.x {
                let condition = self.visit_expr(condition)?;
                if let ExprX::Const(Constant::Bool(selected)) = condition.x {
                    let result = self.visit_expr(if selected { yes } else { no })?;
                    self.cache.insert(key, result.clone());
                    return Ok(result);
                }
            }
            let result = node(&self.visit_expr_rec(value)?);
            self.cache.insert(key, result.clone());
            Ok(result)
        }
        fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
            Ok(typ.clone())
        }
        fn visit_place(&mut self, place: &Place) -> Result<Place, VirErr> {
            self.visit_place_rec(place)
        }
        fn visit_pattern(&mut self, pattern: &Pattern) -> Result<Pattern, VirErr> {
            self.visit_pattern_rec(pattern)
        }
        fn visit_stmt(&mut self, stmt: &Stmt) -> Result<Vec<Stmt>, VirErr> {
            Ok(vec![self.visit_stmt_rec(stmt)?])
        }
    }
    Normalize { values, cache: HashMap::new() }
        .visit_expr(value)
        .expect("infallible forest normalization")
}

/// Structural equality for pure expressions used by forest maps and joins.
/// Unknown forms stay distinct; this never asks the solver or guesses an index.
pub(super) fn same_expression(a: &Expr, b: &Expr) -> bool {
    if Arc::ptr_eq(a, b) {
        return true;
    }
    if !crate::ast_util::types_equal(&a.typ, &b.typ) {
        return false;
    }
    match (&a.x, &b.x) {
        (ExprX::Var(a), ExprX::Var(b)) => a == b,
        (ExprX::Const(Constant::Int(a)), ExprX::Const(Constant::Int(b))) => a == b,
        (ExprX::Const(Constant::Bool(a)), ExprX::Const(Constant::Bool(b))) => a == b,
        (ExprX::Binary(a, al, ar), ExprX::Binary(b, bl, br)) => {
            a == b && same_expression(al, bl) && same_expression(ar, br)
        }
        (ExprX::Unary(a, al), ExprX::Unary(b, bl)) => a == b && same_expression(al, bl),
        (ExprX::If(ac, al, Some(ar)), ExprX::If(bc, bl, Some(br))) => {
            same_expression(ac, bc) && same_expression(al, bl) && same_expression(ar, br)
        }
        (
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, af, at, ai, _),
                args: aa,
                post_args: None,
                body: None,
            },
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, bf, bt, bi, _),
                args: ba,
                post_args: None,
                body: None,
            },
        ) => {
            af == bf
                && ai.is_empty()
                && bi.is_empty()
                && crate::ast_util::n_types_equal(at, bt)
                && aa.len() == ba.len()
                && aa.iter().zip(ba.iter()).all(|(a, b)| same_expression(a, b))
        }
        _ => false,
    }
}

/// Expand finite closed forests without disturbing the scoped range algebra
/// used for symbolic caller-supplied ownership. Its requested views and prefix
/// cuts deliberately stay opaque for counterexample queries.
fn closed(value: &Expr) -> bool {
    crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
        if matches!(value.x, ExprX::Var(_)) { Err(()) } else { Ok(()) }
    })
    .is_ok()
}

fn node(value: &Expr) -> Expr {
    let span = &value.span;
    if let ExprX::If(_, yes, Some(no)) = &value.x {
        if same_expression(yes, no) {
            return yes.clone();
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
                return simplify(&super::choice(
                    span,
                    condition.clone(),
                    apply(yes.clone()),
                    apply(no.clone()),
                ));
            }
        }
    }
    if let ExprX::UnaryOpr(op @ UnaryOpr::Field(_), record) = &value.x {
        if let ExprX::If(condition, yes, Some(no)) = &record.x {
            let apply =
                |record| SpannedTyped::new(span, &value.typ, ExprX::UnaryOpr(op.clone(), record));
            return simplify(&super::choice(
                span,
                condition.clone(),
                apply(yes.clone()),
                apply(no.clone()),
            ));
        }
    }
    if let ExprX::Binary(BinaryOp::Arith(op), left, right) = &value.x {
        match op {
            ArithOp::Add(OverflowBehavior::Allow) | ArithOp::Sub(OverflowBehavior::Allow)
                if contracts::constant(right) == Some(0) =>
            {
                return left.clone();
            }
            ArithOp::Mul(OverflowBehavior::Allow)
                if contracts::constant(right) == Some(0)
                    || contracts::constant(left) == Some(0) =>
            {
                return expr::integer(span, 0);
            }
            ArithOp::Mul(OverflowBehavior::Allow) if contracts::constant(right) == Some(1) => {
                return left.clone();
            }
            ArithOp::Mul(OverflowBehavior::Allow) if contracts::constant(left) == Some(1) => {
                return right.clone();
            }
            _ => {}
        }
    }
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
            return expr::empty(span, expr::record_type());
        }
        if let Some(parts) = call(memory, "add") {
            return simplify(&expr::add(span, apply(parts[0].clone()), apply(parts[1].clone())));
        }
        if let Some(parts) = call(memory, "push") {
            if call(&parts[1], "allocated").is_some_and(|record| empty(&record[0])) {
                return simplify(&apply(parts[0].clone()));
            }
        }
        // Reversal selects runtime children only. A previous prefix cut ending
        // exactly at this extraction's end cannot remove any selected child.
        if let Some(parts) =
            call(memory, "take_children").filter(|parts| same_expression(&parts[1], end))
        {
            return simplify(&apply(parts[0].clone()));
        }
        // Keep runtime filters explicit: scoped prefix-cut proofs use them to
        // connect source descriptors to the local collection's child records.
        if let Some(parts) = call(memory, "descendants") {
            return simplify(&apply(parts[0].clone()));
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
                    return simplify(&super::choice(
                        span,
                        selected,
                        expr::prefix(span, parts[0].clone(), make_path(span, &path)),
                        expr::empty(span, expr::record_type()),
                    ));
                }
            }
        }
    }
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
    if let Some(args) = call(value, "cost") {
        let memory = &args[0];
        let kind = &args[1];
        let cost = |memory: Expr| expr::cost(span, memory, kind.clone());
        if empty(memory) {
            return expr::integer(span, 0);
        }
        if let Some(parts) = call(memory, "add") {
            return simplify(&contracts::add(span, cost(parts[0].clone()), cost(parts[1].clone())));
        }
        if let Some(parts) = call(memory, "prefix").or_else(|| call(memory, "shift_children")) {
            return simplify(&cost(parts[0].clone()));
        }
        if let Some(parts) = call(memory, "repeat").or_else(|| call(memory, "tile_children")) {
            return simplify(&contracts::multiply(span, parts[2].clone(), cost(parts[0].clone())));
        }
        if let Some(parts) = call(memory, "push") {
            if let Some(record) = call(&parts[1], "allocated") {
                let amount = super::choice(
                    span,
                    crate::ast_util::mk_eq(span, &record[1], kind),
                    record[2].clone(),
                    expr::integer(span, 0),
                );
                return simplify(&contracts::add(span, cost(parts[0].clone()), amount));
            }
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
        return simplify(&super::super::metadata::operations::replace(
            span,
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
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
    if let Some(args) = call(value, "shift_children") {
        let memory = &args[0];
        let base = &args[1];
        if empty(memory) || contracts::constant(base) == Some(0) {
            return memory.clone();
        }
        if let Some(parts) = call(memory, "add") {
            return simplify(&expr::add(
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
            ));
        }
        if let Some(parts) = call(memory, "prefix") {
            if let Some(mut slots) = path(&parts[1]) {
                if let Some(first) = slots.first_mut() {
                    if contracts::constant(first).is_some() {
                        *first = contracts::add(span, first.clone(), base.clone());
                        return simplify(&expr::prefix(
                            span,
                            parts[0].clone(),
                            make_path(span, &slots),
                        ));
                    }
                }
            }
        }
        if let Some(parts) = call(memory, "tile_children") {
            return simplify(&expr::operation(
                span,
                "tile_children",
                vec![
                    parts[0].clone(),
                    parts[1].clone(),
                    parts[2].clone(),
                    contracts::add(span, parts[3].clone(), base.clone()),
                ],
                expr::memory_type(),
            ));
        }
    }
    if let Some(args) = call(value, "tile_children") {
        if contracts::constant(&args[1]) == Some(1) {
            if let Some(parts) = call(&args[0], "prefix") {
                if path(&parts[1])
                    .is_some_and(|path| path.len() == 1 && contracts::constant(&path[0]) == Some(0))
                {
                    return simplify(&expr::operation(
                        span,
                        "repeat",
                        vec![parts[0].clone(), args[3].clone(), args[2].clone()],
                        expr::memory_type(),
                    ));
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
                        return simplify(&expr::operation(
                            span,
                            "tile_children",
                            vec![
                                parts[0].clone(),
                                parts[1].clone(),
                                contracts::multiply(span, parts[2].clone(), args[2].clone()),
                                args[3].clone(),
                            ],
                            expr::memory_type(),
                        ));
                    }
                }
            }
        }
        if empty(&args[0]) || contracts::constant(&args[2]) == Some(0) {
            return expr::empty(span, expr::record_type());
        }
        if contracts::constant(&args[2]) == Some(1) {
            return simplify(&expr::operation(
                span,
                "shift_children",
                vec![args[0].clone(), args[3].clone()],
                expr::memory_type(),
            ));
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
        if let Some(parts) = call(memory, "take_children") {
            let retained = if same_expression(&parts[1], length) {
                length.clone()
            } else {
                contracts::minimum(span, parts[1].clone(), length.clone())
            };
            return simplify(&expr::operation(
                span,
                "take_children",
                vec![parts[0].clone(), retained],
                expr::memory_type(),
            ));
        }
        if call(memory, "nonruntime").is_some() {
            return expr::empty(span, expr::record_type());
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
        if !cutting {
            if let Some(parts) = call(memory, "shift_children") {
                if contracts::constant(&selected_path[0]).is_some() {
                    let mut relative = selected_path.clone();
                    relative[0] = contracts::subtract(span, relative[0].clone(), parts[1].clone());
                    return simplify(&super::choice(
                        span,
                        crate::ast_util::mk_ineq(
                            span,
                            &parts[1],
                            &selected_path[0],
                            InequalityOp::Le,
                        ),
                        expr::subtree(span, parts[0].clone(), make_path(span, &relative)),
                        expr::empty(span, expr::record_type()),
                    ));
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
                return simplify(&super::choice(
                    span,
                    conditions,
                    expr::subtree(span, parts[0].clone(), make_path(span, &relative)),
                    expr::empty(span, expr::record_type()),
                ));
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
                        return simplify(&super::choice(
                            span,
                            crate::ast_util::mk_ineq(
                                span,
                                &contracts::literal(span, iteration),
                                &parts[2],
                                InequalityOp::Lt,
                            ),
                            expr::subtree(span, parts[0].clone(), make_path(span, &relative)),
                            expr::empty(span, expr::record_type()),
                        ));
                    } else if index < start {
                        return expr::empty(span, expr::record_type());
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
    let constant = |value: &Expr| matches!(value.x, ExprX::Const(_));
    let fold = match &value.x {
        ExprX::Unary(_, a) => constant(a),
        ExprX::Binary(_, a, b) | ExprX::Logical(_, a, b) => constant(a) && constant(b),
        _ => false,
    };
    if fold { contracts::simplify(value) } else { value.clone() }
}
