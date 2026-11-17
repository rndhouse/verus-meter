//! A publication retains the actual executable closure definition, separately
//! from its dynamic captures. Entry must consume both; a closure type or a
//! manually supplied completion value cannot stand in for checked body effects.

use super::super::{
    concurrency, heap::OwnerSlot, layout::Layouts, lifetime::Storage, model::unsupported,
};
use crate::ast::*;

/// The exact source definition and existing storage transferred at worker entry.
/// Consuming this frame does not itself prove execution, completion or a bound.
pub(in super::super) struct Entry {
    /// NonSpecClosure from the accounting AST, including restored native calls.
    pub(in super::super) definition: Expr,
    /// Inline captures and separately owned descendants, without a second charge.
    pub(in super::super) storage: Storage,
}

impl Entry {
    /// Check the transferred environment against actual executable fields. Its
    /// inline storage stays whole; fields are views into it, never copied input
    /// slots. Later body analysis must account for moves out of those views.
    pub(super) fn checked(
        definition: Expr,
        storage: Storage,
        evidence: &concurrency::Evidence,
        layouts: &Layouts,
    ) -> Result<Self, VirErr> {
        let span = &definition.span;
        let TypX::AnonymousClosure(_, _, kind, id) = &*definition.typ else {
            return Err(unsupported(span, "worker entry without a concrete closure definition"));
        };
        let evidence = evidence
            .closures
            .get(id)
            .ok_or_else(|| unsupported(span, "worker entry without executable capture evidence"))?;
        if !crate::ast_util::types_equal(&definition.typ, &storage.typ)
            || layouts.size(&storage.typ, span)? != storage.value.bytes
        {
            return Err(unsupported(span, "incomplete inline worker environment storage"));
        }
        if !evidence.by_move
            || evidence
                .captures
                .iter()
                .any(|capture| capture.mode == concurrency::CaptureMode::Borrow)
        {
            return Err(unsupported(span, "borrowed or non-move worker environments"));
        }
        if *kind != ClosureKind::FnOnce && evidence.once_adapter.is_none() {
            return Err(unsupported(
                span,
                "worker entry without its executable FnOnce cleanup adapter",
            ));
        }
        if evidence.body.arguments != 1
            || evidence.captures.iter().any(|capture| {
                capture
                    .body_place
                    .as_ref()
                    .is_none_or(|place| place.local != 1 || place.local >= evidence.body.locals)
            })
        {
            return Err(unsupported(
                span,
                "worker captures without exact compiler body projections",
            ));
        }
        let fields: std::collections::BTreeSet<_> = evidence
            .captures
            .iter()
            .enumerate()
            .filter_map(|(index, capture)| {
                layouts.owner(&capture.typ).then_some(OwnerSlot::Capture(index))
            })
            .collect();
        if let Some(owner) = &storage.owner {
            if owner.closure != Some(*id)
                || owner.bytes != 0
                || owner.dynamic.is_some()
                || owner.shared.is_some()
                || owner.worker.is_some()
                || owner.elements.is_some()
                || owner.vector.is_some()
                || owner.children.keys().cloned().collect::<std::collections::BTreeSet<_>>()
                    != fields
                || !layouts.owner(&storage.typ)
            {
                return Err(unsupported(span, "incomplete or duplicated worker capture ownership"));
            }
        } else if layouts.owner(&storage.typ) || !fields.is_empty() {
            return Err(unsupported(span, "worker entry missing owned capture storage"));
        }
        Ok(Self { definition, storage })
    }
}

/// Resolve moved closure values against canonical source bodies. Direct closure
/// arguments already belong to the accounting AST and are not restored again.
pub(super) fn definition<'a>(
    argument: &Expr,
    evidence: &concurrency::Evidence,
    bodies: impl Iterator<Item = &'a Expr>,
) -> Result<Expr, VirErr> {
    let TypX::AnonymousClosure(_, result, _, id) = &*argument.typ else {
        return Err(unsupported(&argument.span, "a worker without a concrete closure type"));
    };
    let definition = if matches!(argument.x, ExprX::NonSpecClosure { proof_fn_modes: None, .. }) {
        // The enclosing accounting AST has already restored native calls
        // hidden by functional identity translation. Never restore twice.
        argument.clone()
    } else {
        // A local closure can move through source bindings before spawn.
        // Resolve its definition by compiler type identity, not its latest
        // binding name. Inspect every candidate so ambiguity fails closed.
        let mut definitions = Vec::new();
        for body in bodies {
            crate::ast_visitor::expr_visitor_check(body, &mut |_, value| {
                if matches!(value.x, ExprX::NonSpecClosure { proof_fn_modes: None, .. })
                    && matches!(&*value.typ, TypX::AnonymousClosure(_, _, _, source) if source == id)
                {
                    definitions.push(value.clone());
                }
                Ok::<(), VirErr>(())
            })?;
        }
        let [definition] = definitions.as_slice() else {
            return Err(unsupported(
                &argument.span,
                "worker publication without one executable source definition",
            ));
        };
        concurrency::accounting_expression(definition, evidence)?
    };
    let evidence = evidence.closures.get(id).ok_or_else(|| {
        unsupported(&argument.span, "a worker definition without compiler capture evidence")
    })?;
    let ExprX::NonSpecClosure { params, proof_fn_modes: None, ret, .. } = &definition.x else {
        return Err(unsupported(&argument.span, "this worker source definition"));
    };
    if definition.span.id != evidence.span.id
        || !crate::ast_util::types_equal(&definition.typ, &argument.typ)
        || !params.is_empty()
        || !crate::ast_util::types_equal(&ret.a, result)
    {
        return Err(unsupported(
            &argument.span,
            "inconsistent worker source, capture or result identities",
        ));
    }
    Ok(definition)
}
