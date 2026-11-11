//! Parametric ownership transformations inferred from checked executable bodies.
//!
//! Templates describe physical allocation forests, independently of a callee's
//! frame-local charges. Calls substitute their own forests and scalar snapshots;
//! no ghost arguments or user annotations cross the executable interface.
//! Runtime ownership interfaces require a representable template. Missing rules
//! are unsupported; byte bounds cannot substitute for ownership effects.

mod calls;
pub(super) mod checked;
mod consistency;
mod proofs;
mod simplify;
mod trace;

use super::metadata::{
    expr,
    reservations::{Floor, Minima, Step},
};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{BTreeMap, HashMap};

pub(super) use checked::Checked;
pub(super) use consistency::{modified_parameters, validate};

#[derive(Clone)]
pub(super) enum Input {
    /// An immutable snapshot of an executable scalar argument.
    Scalar(usize),
    /// The complete physical forest supplied by an owning argument.
    Forest(usize),
    /// One root descriptor property at a finite fixed ownership path.
    Property(usize, super::heap::OwnerPath, &'static str),
    /// A checked reservation floor for a fixed or repeated ownership class.
    Minimum(usize, Vec<Step>),
}

#[derive(Clone)]
pub(super) struct Symbol {
    /// Compiler-owned variable replaced at each call site.
    pub(super) name: VarIdent,
    /// The caller observation substituted for that variable.
    pub(super) input: Input,
}

/// A complete owner expression and conservative uniform reservation candidates.
#[derive(Clone)]
pub(super) struct Node {
    /// The ownership layout whose operations produced this forest.
    pub(super) typ: Typ,
    /// Physical allocation descriptors, independent of frame-local charges.
    pub(super) memory: Expr,
    /// Reservation lower bounds indexed by ownership class.
    pub(super) minima: Minima,
}

#[derive(Clone)]
pub(super) enum Value {
    Owner(Node),
    Scalar(Expr),
    Unit,
    Unknown,
}

/// A transformation of supplied forests, not an aggregate allocation allowance.
#[derive(Clone)]
pub(super) struct Template {
    /// Only observations needed by the final transformation are retained.
    pub(super) symbols: Vec<Symbol>,
    /// Reusable append effects still use the aggregate length induction. Other
    /// finite transfers can preserve forests through a caller's checked loop.
    pub(super) appends: bool,
    /// Only modified mutable parameters appear here; paths remain within forests.
    pub(super) borrowed: BTreeMap<usize, Node>,
    /// Ownership or scalar value produced by the checked body.
    pub(super) result: Value,
}

pub(super) fn summarize(
    function: &Function,
    layouts: &super::layout::Layouts,
    functions: &HashMap<Fun, Function>,
    summaries: &HashMap<Fun, super::summary::FunctionSummary>,
    modes: &HashMap<VarIdent, Mode>,
    checked: &Checked,
) -> Result<Option<Template>, VirErr> {
    let template = trace::summarize(function, layouts, functions, summaries, modes, checked);
    if template.is_none() && required(function, layouts)? {
        return Err(super::model::unsupported(
            &function.span,
            "this runtime ownership transformation; no precise helper summary can be inferred",
        ));
    }
    Ok(template)
}

/// Fixed trees have an explicit structural summary. Runtime owning children
/// additionally require a forest transformation, even beneath fixed wrappers.
pub(super) fn required(
    function: &Function,
    layouts: &super::layout::Layouts,
) -> Result<bool, VirErr> {
    let mut types: Vec<_> = function
        .x
        .params
        .iter()
        .filter(|parameter| parameter.x.mode == Mode::Exec)
        .map(|parameter| {
            layouts.borrowed_owner(&parameter.x.typ).unwrap_or(&parameter.x.typ).clone()
        })
        .collect();
    types.push(function.x.outer_ret.x.typ.clone());
    while let Some(typ) = types.pop() {
        if layouts.owning_elements(&typ) {
            return Ok(true);
        }
        if layouts.owner(&typ) {
            types.extend(layouts.owned_children(&typ, &function.span)?.into_values());
        }
    }
    Ok(false)
}

fn substitute(value: &Expr, values: &HashMap<VarIdent, Expr>) -> Expr {
    let value = crate::ast_visitor::map_expr_visitor(value, &|value| {
        Ok::<_, VirErr>(match &value.x {
            ExprX::Var(name) => values.get(name).cloned().unwrap_or_else(|| value.clone()),
            _ => value.clone(),
        })
    })
    .expect("infallible template substitution");
    simplify::simplify(&value)
}

fn instantiate_node(node: &Node, values: &HashMap<VarIdent, Expr>) -> Node {
    Node {
        typ: node.typ.clone(),
        memory: substitute(&node.memory, values),
        minima: node
            .minima
            .iter()
            .map(|(path, floor)| {
                (
                    path.clone(),
                    Floor { capacity: substitute(&floor.capacity, values), element: floor.element },
                )
            })
            .collect(),
    }
}

fn instantiate_value(value: &Value, values: &HashMap<VarIdent, Expr>) -> Value {
    match value {
        Value::Owner(node) => Value::Owner(instantiate_node(node, values)),
        Value::Scalar(value) => Value::Scalar(substitute(value, values)),
        _ => value.clone(),
    }
}

fn root(span: &Span, memory: Expr) -> Expr {
    simplify::simplify(&expr::lookup(span, memory, expr::path(span, [])))
}

fn property(span: &Span, memory: Expr, field: &str) -> Expr {
    simplify::simplify(&expr::record_field(span, root(span, memory), field))
}

fn allocated(span: &Span, bytes: Expr, capacity: Expr, length: Expr) -> Expr {
    expr::operation(
        span,
        "allocated",
        vec![expr::path(span, []), expr::integer(span, 0), bytes, capacity, length],
        expr::record_type(),
    )
}

fn with_root(
    span: &Span,
    memory: Expr,
    bytes: Expr,
    capacity: Expr,
    length: Expr,
    owns_children: bool,
) -> Expr {
    if !owns_children {
        // A leaf allocation has no descendant storage to retain. Its updated
        // descriptor still uses the original byte and reservation expressions.
        return expr::push(
            span,
            expr::empty(span, expr::record_type()),
            allocated(span, bytes, capacity, length),
        );
    }
    simplify::simplify(&expr::operation(
        span,
        "with_root",
        vec![memory, allocated(span, bytes, capacity, length)],
        expr::memory_type(),
    ))
}

fn choice(span: &Span, condition: Expr, yes: Expr, no: Expr) -> Expr {
    if std::sync::Arc::ptr_eq(&yes, &no) {
        return yes;
    }
    simplify::simplify(&SpannedTyped::new(
        span,
        &yes.typ,
        ExprX::If(condition, yes.clone(), Some(no)),
    ))
}
