//! A publication retains the actual executable closure definition, separately
//! from its dynamic captures. Entry must consume both; a closure type or a
//! manually supplied completion value cannot stand in for checked body effects.

use super::super::{concurrency, layout::Layouts, lifetime::Storage, model::unsupported};
use crate::ast::*;

/// The exact source definition and existing storage transferred at worker entry.
/// Consuming this frame does not itself prove execution, completion or a bound.
pub(in super::super) struct Entry {
    /// NonSpecClosure from the accounting AST, including restored native calls.
    pub(in super::super) definition: Expr,
    /// Existing inline captures and separately owned descendants, without a
    /// second charge. Never reconstruct their values by rereading parent
    /// variables at publication: captures belong to their construction epoch.
    pub(in super::super) storage: Storage,
    /// Disjoint source/compiler views into the original environment storage.
    pub(super) captures: super::captures::Captures,
    /// Source receiver convention and responsibility for remaining capture cleanup.
    pub(super) invocation: concurrency::invocation::Invocation,
    /// Only the actual captured strong handles, with backing retained in the
    /// enclosing domain. Local final release is not global reclamation.
    pub(in super::super) shared: super::super::shared::SharedRoots,
}

impl Entry {
    /// Move only owned descendants out of a captured field, using the original
    /// source binding's exact path. The environment's inline charge stays live;
    /// body accounting must preserve the destination's actual value storage.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "worker body ownership effects consume capture views")
    )]
    pub(in super::super) fn take_capture_owner(
        &mut self,
        source: &super::super::paths::LocalPath,
    ) -> Result<super::super::heap::Owner, VirErr> {
        if self.invocation.cleans_up_after_body() {
            return Err(unsupported(
                &self.definition.span,
                "moving a capture out of a borrowed worker body without replacement",
            ));
        }
        let path = self.captures.source_path(source).ok_or_else(|| {
            unsupported(&self.definition.span, "a worker access outside its executable captures")
        })?;
        self.storage.owner.as_mut().and_then(|owner| owner.take_child(&path)).ok_or_else(|| {
            unsupported(&self.definition.span, "an absent or already moved worker capture owner")
        })
    }

    /// End a normal invocation after checked body effects have been applied.
    /// The returned storage still owns its inline environment and, for a borrowed
    /// body, the remaining captures. The caller must destroy that storage while
    /// retaining the separately produced result; this is not worker completion.
    ///
    /// Implicit capture cleanup is an unordered group under Rust's source rules.
    /// A synchronization-aware consumer must cover every permitted release order,
    /// not use the owner map's iteration order to infer exclusion. Explicit body
    /// moves/drops retain their own control-flow ordering. Unwind is not a normal
    /// exit and cannot use this operation to discharge panic-free obligations.
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "checked worker body returns are connected in TODO 03.2")
    )]
    pub(in super::super) fn into_return_cleanup(
        self,
        layouts: &Layouts,
    ) -> Result<Storage, VirErr> {
        let remaining: std::collections::BTreeSet<_> =
            self.storage.owner.iter().flat_map(|owner| owner.children.keys().cloned()).collect();
        if self.invocation.cleans_up_after_body() {
            if remaining != self.captures.owned_slots(layouts) {
                return Err(unsupported(
                    &self.definition.span,
                    "a borrowed worker body returning with incomplete capture ownership",
                ));
            }
        } else if !remaining.is_empty() {
            return Err(unsupported(
                &self.definition.span,
                "an owned worker body returning before its capture moves and cleanup are accounted for",
            ));
        }
        Ok(self.storage)
    }

    /// Check the transferred environment against actual executable fields. Its
    /// inline storage stays whole; fields are views into it, never copied input
    /// slots. Later body analysis must account for moves out of those views.
    pub(super) fn checked(
        definition: Expr,
        storage: Storage,
        evidence: &concurrency::Evidence,
        layouts: &Layouts,
        environments: &super::super::closures::observations::Environments,
        shared: &super::super::shared::SharedRoots,
    ) -> Result<Self, VirErr> {
        let span = &definition.span;
        let TypX::AnonymousClosure(_, _, kind, id) = &*definition.typ else {
            return Err(unsupported(span, "worker entry without a concrete closure definition"));
        };
        let evidence = evidence
            .closures
            .get(id)
            .ok_or_else(|| unsupported(span, "worker entry without executable capture evidence"))?;
        if storage
            .value
            .environment
            .is_none_or(|environment| !environments.matches(environment, *id, &evidence.captures))
        {
            return Err(unsupported(
                span,
                "worker entry without its construction-epoch capture observations",
            ));
        }
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
        if *kind != evidence.kind {
            return Err(unsupported(
                span,
                "inconsistent source and compiler closure invocation kinds",
            ));
        }
        let invocation = concurrency::invocation::Invocation::checked(evidence, span)?;
        let captures = super::captures::Captures::new(evidence, layouts, span)?;
        let fields = captures.owned_slots(layouts);
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
        let shared = shared.captured_view(storage.owner.as_ref(), span)?;
        Ok(Self { definition, storage, captures, invocation, shared })
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
