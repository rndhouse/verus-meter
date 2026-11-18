//! Bind body-local views to one executable construction epoch. Source names are
//! not worker identities: partial captures and distinct publications get separate
//! binders while retaining the same allocation and synchronization targets.

use super::super::{concurrency, heap::OwnerSlot, layout::Layouts, model::unsupported, paths};
use crate::{ast::*, messages::Span};
use std::sync::Arc;

/// Give the existing parametric transfer pass the worker's capture interface.
/// This is an analysis signature only: it creates no executable call, parameter
/// storage, or new functional contract.
pub(super) fn signature(
    definition: &Expr,
    body: Expr,
    inputs: &[Input],
    closure: &concurrency::Closure,
    functions: &std::collections::HashMap<Fun, Function>,
) -> Result<Function, VirErr> {
    let mut enclosing = Vec::new();
    for function in functions.values() {
        let Some(source) = &function.x.body else { continue };
        let mut contains = false;
        crate::ast_visitor::expr_visitor_check(source, &mut |_, value| {
            contains |= value.span.id == definition.span.id
                && matches!(value.x, ExprX::NonSpecClosure { .. });
            Ok::<(), VirErr>(())
        })?;
        if contains {
            enclosing.push(function);
        }
    }
    let [enclosing] = enclosing.as_slice() else {
        return Err(unsupported(
            &definition.span,
            "worker summary without one enclosing source signature",
        ));
    };
    let ExprX::NonSpecClosure { ret, requires, ensures, mask_spec, .. } = &definition.x else {
        unreachable!()
    };
    let parameter = |name, typ| {
        crate::def::Spanned::new(
            definition.span.clone(),
            ParamX { name, typ, mode: Mode::Exec, user_mut: false, unwrapped_info: None },
        )
    };
    let mut function = (*enclosing).clone();
    let f = &mut Arc::make_mut(&mut function).x;
    f.name = closure.function.clone();
    f.params = Arc::new(
        inputs.iter().map(|input| parameter(input.name.clone(), input.typ.clone())).collect(),
    );
    f.outer_ret = parameter(ret.name.clone(), ret.a.clone());
    f.inner_ret = f.outer_ret.clone();
    f.require =
        Arc::new(requires.iter().map(|value| self::body(value, inputs)).collect::<Result<_, _>>()?);
    f.ensure = (
        Arc::new(ensures.iter().map(|value| self::body(value, inputs)).collect::<Result<_, _>>()?),
        Arc::new(vec![]),
    );
    f.returns = None;
    f.decrease = Arc::new(vec![]);
    f.decrease_when = None;
    f.decrease_by = None;
    f.mask_spec = mask_spec.clone();
    Arc::make_mut(&mut f.attrs).resource_contract = None;
    f.body = Some(body);
    Ok(function)
}

/// One capture field's body-local name and immutable construction observation.
#[derive(Clone)]
pub(in super::super) struct Input {
    /// Fresh name in the private accounting body, never an executable parameter.
    pub(super) name: VarIdent,
    /// Type of this one runtime capture field.
    pub(super) typ: Typ,
    /// Original lexical binding and its exact fixed projection.
    pub(super) source: paths::LocalPath,
    /// Matching field in the transferred environment owner tree.
    pub(super) slot: OwnerSlot,
    /// Direct scalar's construction snapshot, when this field is scalar.
    pub(super) scalar: Option<Expr>,
    /// Construction observations for supported fixed scalar projections.
    pub(super) projections: Vec<(Vec<Ident>, Expr)>,
    /// A captured closure retains its own construction epoch.
    pub(super) environment: Option<super::super::closures::observations::EnvironmentId>,
    /// Original body proof context, distinct from the frozen caller observation.
    pub(super) source_place: Place,
    pub(super) source_value: Expr,
}

impl super::super::analysis::Analysis<'_> {
    /// Express a worker path condition at publication using immutable scalar observations.
    pub(in super::super) fn captured_checkpoint_guard(&self, condition: &Expr) -> Option<Expr> {
        let snapshots: std::collections::HashMap<_, _> = self
            .worker_inputs
            .iter()
            .filter(|input| self.stable_scalars.contains(&input.name))
            .filter_map(|input| Some((input.name.clone(), input.scalar.clone()?)))
            .collect();
        let condition =
            super::super::contracts::predicate(condition, &snapshots.keys().cloned().collect())
                .ok()?;
        Some(super::super::transfer::simplify::specialize(&condition, &snapshots))
    }

    /// Compiler capture places use lexical source names. Nested construction
    /// must read the executing parent's views, never its caller's old slots.
    pub(in super::super) fn worker_capture_place(&self, place: Place) -> Result<Place, VirErr> {
        let read = SpannedTyped::new(
            &place.span,
            &place.typ,
            ExprX::ReadPlace(
                place.clone(),
                UnfinalizedReadKind { preliminary_kind: ReadKind::Spec, id: 0 },
            ),
        );
        let read = body(&read, &self.worker_inputs)?;
        let ExprX::ReadPlace(place, _) = &read.x else { unreachable!() };
        Ok(place.clone())
    }
}

pub(super) fn bind(
    closure: &concurrency::Closure,
    environment: super::super::closures::observations::EnvironmentId,
    observations: &super::super::closures::observations::Environments,
    layouts: &Layouts,
    span: &Span,
) -> Result<Vec<Input>, VirErr> {
    closure
        .captures
        .iter()
        .enumerate()
        .map(|(index, capture)| {
            let place = layouts.capture_place(capture, span)?;
            let source = paths::place(&place, &capture.typ).ok_or_else(|| {
                unsupported(span, "a worker capture without an exact source projection")
            })?;
            let scalar = observations.scalar(environment, index).cloned();
            if super::super::contracts::scalar(&capture.typ) && scalar.is_none() {
                return Err(unsupported(
                    span,
                    "a worker scalar without its construction observation",
                ));
            }
            Ok(Input {
                name: VarIdent(
                    Arc::new("$memory_worker_capture".into()),
                    VarIdentDisambiguate::VirTemp(
                        super::super::accounting::Accounting::fresh_allocation(),
                    ),
                ),
                source_value: super::super::projections::spec_value(&SpannedTyped::new(
                    span,
                    &capture.typ,
                    ExprX::ReadPlace(
                        place.clone(),
                        UnfinalizedReadKind { preliminary_kind: ReadKind::Spec, id: 0 },
                    ),
                ))?,
                source_place: place,
                typ: capture.typ.clone(),
                source,
                slot: OwnerSlot::Capture(index),
                scalar,
                projections: observations.projections(environment, index).to_vec(),
                environment: observations.nested(environment, index),
            })
        })
        .collect()
}

/// Body obligations are proved in the original closure's lexical context.
/// Cross-actor summaries separately use construction observations; restoring a
/// proof binding must never reread a parent local at publication or collection.
pub(in super::super) fn restore_proof_bindings(
    function: &Function,
    growth: &super::super::growth::Growth,
    fresh_span: &dyn Fn(&Span) -> Span,
) -> Result<Function, VirErr> {
    let bindings: std::collections::HashMap<_, _> = growth
        .worker_executions
        .values()
        .flat_map(|worker| worker.inputs.iter().map(|input| (&input.name, input)))
        .collect();
    let fresh = |value: &Expr| {
        let statement = crate::def::Spanned::new(value.span.clone(), StmtX::Expr(value.clone()));
        let statement =
            crate::ast_visitor::map_stmt_spans(&statement, &mut |span| fresh_span(span));
        let StmtX::Expr(value) = &statement.x else { unreachable!() };
        value.clone()
    };
    crate::ast_visitor::map_function_visitor_env(
        function,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_, _, value| {
            Ok(match &value.x {
                ExprX::Var(name) if bindings.contains_key(name) => {
                    fresh(&bindings[name].source_value)
                }
                _ => value.clone(),
            })
        },
        &|_, _, statement| Ok(vec![statement.clone()]),
        &|_, typ| Ok(typ.clone()),
        &|_, _, place| {
            let PlaceX::Local(name) = &place.x else { return Ok(place.clone()) };
            let Some(input) = bindings.get(name) else { return Ok(place.clone()) };
            let read = fresh(&SpannedTyped::new(
                &place.span,
                &place.typ,
                ExprX::ReadPlace(
                    input.source_place.clone(),
                    UnfinalizedReadKind { preliminary_kind: ReadKind::Spec, id: 0 },
                ),
            ));
            let ExprX::ReadPlace(place, _) = &read.x else { unreachable!() };
            Ok(place.clone())
        },
        &|_, _, pattern| Ok(pattern.clone()),
    )
}

/// Only an exact typed source projection becomes a view. Ancestors of a partial
/// capture remain unavailable; they cannot silently resolve to a parent local.
pub(super) fn body(body: &Expr, inputs: &[Input]) -> Result<Expr, VirErr> {
    let find = |path: Option<paths::LocalPath>, typ: &Typ| {
        inputs.iter().find(|input| {
            path.as_ref() == Some(&input.source) && crate::ast_util::types_equal(typ, &input.typ)
        })
    };
    crate::ast_visitor::map_expr_visitor_env(
        body,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_, _, value| {
            if let Some(input) = find(paths::expr(value, &value.typ), &value.typ) {
                // Places are rewritten below. This handles specification reads
                // and scalar expressions that no longer contain a place node.
                if matches!(value.x, ExprX::Var(_) | ExprX::UnaryOpr(UnaryOpr::Field(_), _)) {
                    return Ok(SpannedTyped::new(
                        &value.span,
                        &value.typ,
                        ExprX::Var(input.name.clone()),
                    ));
                }
            }
            Ok(value.clone())
        },
        &|_, _, statement| Ok(vec![statement.clone()]),
        &|_, typ| Ok(typ.clone()),
        &|_, _, place| {
            Ok(if let Some(input) = find(paths::place(place, &place.typ), &place.typ) {
                SpannedTyped::new(&place.span, &place.typ, PlaceX::Local(input.name.clone()))
            } else {
                place.clone()
            })
        },
        &|_, _, pattern| Ok(pattern.clone()),
    )
}
