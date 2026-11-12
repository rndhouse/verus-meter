//! Parametric ownership transformations inferred from checked executable bodies.
//!
//! Templates transform complete forests or local charges with logical geometry.
//! Original lifetimes compose separately. Calls substitute forests and snapshots;
//! no ghost arguments or user annotations cross the executable interface.
//! Runtime ownership interfaces require a representable template. Missing rules
//! are unsupported; byte bounds cannot substitute for ownership effects.

mod calls;
pub(super) mod checked;
mod consistency;
pub(super) mod effects;
mod origins;
mod proofs;
pub(super) mod simplify;
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

/// Disjoint original regions at fixed output paths. `None` names the result;
/// `Some(parameter)` names a borrowed parameter after the operation.
pub(super) type Origins<T> = BTreeMap<Option<usize>, BTreeMap<super::heap::OwnerPath, T>>;

#[derive(Clone)]
pub(super) enum Input {
    /// Complete byte charges permit exact-capacity inference; local views do not.
    Complete,
    /// An immutable snapshot of an executable scalar argument.
    Scalar(usize),
    /// The supplied descriptor forest, with complete or frame-local byte charges.
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
    /// An unchanged whole parameter. Cleared whenever its forest is modified or
    /// projected; helper composition uses this identity independently of the
    /// descriptor expression chosen to encode that forest.
    pub(super) origin: Option<usize>,
    /// The ownership layout whose operations produced this forest.
    pub(super) typ: Typ,
    /// Descriptors in the supplied charge view, retaining logical geometry.
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
    /// Overlapping iterations need inverse indexed views when callers inspect
    /// their completed forests; ordinary summaries keep these laws dormant.
    pub(super) ordered: bool,
    /// Original input forests retained by each result or borrowed output node.
    pub(super) origins: Origins<Expr>,
    /// Original allocation regions used by lifetime profiles after a split.
    /// These exclude allocations introduced in the helper's own frame.
    pub(super) regions: BTreeMap<usize, Expr>,
    /// Only observations needed by the final transformation are retained.
    pub(super) symbols: Vec<Symbol>,
    /// Checked parameter effects reusable in an enclosing iteration. Absent
    /// when branches, ownership dependencies or mutations cannot be composed.
    pub(super) effects: Option<Vec<(usize, effects::Effect)>>,
    /// Only modified mutable parameters appear here; paths remain within forests.
    pub(super) borrowed: BTreeMap<usize, Node>,
    /// Ownership or scalar value produced by the checked body.
    pub(super) result: Value,
}

/// A complete ownership template and structural evidence for local loop proofs.
/// Nothing is published if any part of template inference fails.
pub(super) struct Inferred {
    /// Physical ownership transformation substituted by callers.
    pub(super) template: Template,
    /// Whole-child transfer relationships, resolved against checked loop roles.
    pub(super) loops: HashMap<u64, Vec<super::loops::Transfer>>,
    /// Fresh append costs used as ordinary inductive length envelopes.
    pub(super) growth: HashMap<u64, Vec<(super::paths::LocalPath, Expr)>>,
    /// Ordinary operation-site bounds supporting newly retained loop storage.
    pub(super) checks: Vec<(Span, Expr)>,
    /// Checked helper workspace ceilings with all iteration-local aliases closed.
    pub(super) scratch: HashMap<u64, Expr>,
    /// Per-visit allocation ceilings for evolving collection recurrences.
    pub(super) repetitions: HashMap<u64, Expr>,
}

pub(super) fn summarize(
    function: &Function,
    layouts: &super::layout::Layouts,
    functions: &HashMap<Fun, Function>,
    summaries: &HashMap<Fun, super::summary::FunctionSummary>,
    modes: &HashMap<VarIdent, Mode>,
    checked: &Checked,
) -> Result<Option<Inferred>, VirErr> {
    let template = trace::summarize(function, layouts, functions, summaries, modes, checked);
    if template.is_none() && requires_summary(function, layouts, checked, summaries)? {
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

/// Internal runtime ownership must retain its precise interface when a helper
/// returns a leaf owner or forwards another such helper's result.
pub(super) fn requires_summary(
    function: &Function,
    layouts: &super::layout::Layouts,
    checked: &Checked,
    summaries: &HashMap<Fun, super::summary::FunctionSummary>,
) -> Result<bool, VirErr> {
    if required(function, layouts)? || checked.has_regions() {
        return Ok(true);
    }
    if !layouts.owner(&function.x.outer_ret.x.typ) {
        return Ok(false);
    }
    Ok(checked.operations.values().any(|operation| match operation {
        checked::Operation::Push { receiver, .. }
        | checked::Operation::Remove { receiver, .. }
        | checked::Operation::Length { receiver } => layouts.owning_elements(&receiver.typ),
        checked::Operation::Call { target, .. } => {
            summaries.get(target).is_some_and(|summary| summary.transfer_required)
        }
        _ => false,
    }))
}

fn substitute(value: &Expr, values: &HashMap<VarIdent, Expr>) -> Expr {
    simplify::specialize(value, values)
}

fn instantiate_node(node: &Node, values: &HashMap<VarIdent, Expr>) -> Node {
    Node {
        origin: None,
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
    if simplify::same_expression(&yes, &no) {
        return yes;
    }
    simplify::simplify(&SpannedTyped::new(
        span,
        &yes.typ,
        ExprX::If(condition, yes.clone(), Some(no)),
    ))
}
