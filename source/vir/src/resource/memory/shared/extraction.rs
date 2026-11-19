//! Recover the executable contents of a proved unique Arc.
use super::*;

impl Analysis<'_> {
    /// Only an owned, uniquely identified allocation can yield its payload. A
    /// worker awaiting collection or an alias in a collection can defeat uniqueness.
    pub(super) fn take_shared_payload(
        &mut self,
        expr: &Expr,
        source: &Expr,
    ) -> Result<Owner, VirErr> {
        let span = &expr.span;
        let payload = self.layouts.option_payload(&expr.typ, span)?;
        if !matches!(&*source.typ, TypX::Decorate(TypDecoration::Arc, _, inner)
            if crate::ast_util::types_equal(inner, payload))
        {
            return Err(unsupported(span, "this Arc::into_inner payload type"));
        }
        let handle = self.produce(source)?;
        let root = self
            .result_owner
            .take()
            .and_then(|o| o.shared)
            .and_then(StrongLink::known)
            .ok_or_else(|| {
                unsupported(span, "extracting a shared payload without a known allocation")
            })?;
        if !(self.transitions.owns_fixed_root(root) || self.transitions.recovered_job(root))
            || self.growth.section_shared.contains(&root)
            || self.growth.peer_results.contains_key(&root)
            || self.growth.occurrence_peers.contains_key(&root)
            || !self
                .heap
                .shared
                .roots
                .get(&root)
                .is_some_and(|r| r.strong == 1 && matches!(r.storage, Backing::Owned(_)))
        {
            return Err(unsupported(
                span,
                "extracting a shared payload without exclusive ownership",
            ));
        }
        if let Some(claims) = self.growth.indexed_shared.get(&root) {
            self.growth.before.entry(span.id).or_default().push(
                super::super::metadata::expr::check(
                    span,
                    crate::ast_util::mk_eq(
                        span,
                        &claims.population.pending,
                        &super::super::metadata::expr::integer(span, 0),
                    ),
                    "cannot extract a shared payload while indexed aliases still own it",
                ),
            );
        }
        let mut backing = self.heap.shared.release(root).unwrap();
        let mut result = Owner {
            extracted_arc: Some(root),
            geometry: Some(super::super::contracts::literal(span, 1)),
            ..Owner::default()
        };
        if self.layouts.owner(payload) && !backing.children.contains_key(&OwnerSlot::Contents) {
            return Err(unsupported(
                span,
                "unique Arc extraction without its original payload ownership",
            ));
        }
        if let Some(child) = backing.children.remove(&OwnerSlot::Contents) {
            result.children.insert(OwnerSlot::Contents, child);
        }
        self.release_owner(backing, span);
        self.release_value(handle, span);
        self.transitions.operation(
            span,
            super::super::transfer::checked::Operation::StrongTake { source: source.clone(), root },
        );
        Ok(result)
    }
}
