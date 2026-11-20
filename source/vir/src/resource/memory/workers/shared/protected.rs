//! Transfer the canonical backing at a fixed publication that owns all handles.
//! Outstanding indexed or aliased backing keeps its existing accounting domain.

use crate::{
    ast::*,
    messages::Span,
    resource::memory::{
        accounting::Accounting,
        analysis::Analysis,
        lifetime::{Storage, Value},
        workers::{WorkerId, Workers, body::Entry},
    },
};

impl Analysis<'_> {
    /// Keep ordinary strong-handle publications on their existing reference
    /// interface. Payload transport is needed only by an executable protected
    /// borrow or a helper with an owning protected parameter.
    fn accesses_protected_payload(&self, body: &Expr) -> bool {
        use crate::resource::memory::synchronization::Operation::{GuardBorrow, GuardBorrowMut};
        use crate::visitor::VisitorControlFlow::{Recurse, Return, Stop};
        matches!(
            crate::ast_visitor::expr_visitor_dfs(
                body,
                &mut air::scope_map::ScopeMap::new(),
                &mut |_, expr| match &expr.x {
                    ExprX::NonSpecClosure { .. } => Return,
                    ExprX::Call { target: CallTarget::Fun(_, target, _, _, attrs), .. } => {
                        if matches!(
                            attrs.resource_intrinsic,
                            Some(ResourceIntrinsic::Synchronization(GuardBorrow | GuardBorrowMut))
                        ) && self
                            .layouts
                            .owner(crate::resource::memory::paths::referent(&expr.typ))
                            || self.summaries.contains_key(target)
                                && self.functions[target].x.params.iter().any(|param| {
                                    self.layouts.synchronization_parameter(&param.x.typ).is_some()
                                        && self.layouts.borrowed_owner(&param.x.typ).is_some()
                                })
                        {
                            Stop(())
                        } else {
                            Recurse
                        }
                    }
                    _ => Recurse,
                }
            ),
            Stop(())
        )
    }

    pub(in crate::resource::memory::workers) fn transfer_protected_captures(
        &mut self,
        actor: WorkerId,
        span: &Span,
        body: &Expr,
        result_type: &Typ,
        entry: &mut Entry,
        storage: &mut Accounting,
    ) -> Result<(), VirErr> {
        // A fixed worker receiving every handle can take the owning tree and
        // its existing charges with it. An imported view never copies another
        // actor's mutable vector state. Indexed and delegated reservations keep
        // their own conservation protocol.
        if self.growth.worker_occurrences[&actor].is_empty()
            && !self.layouts.contains_references(result_type)
            && self.accesses_protected_payload(body)
            && Workers::captured_workers(entry.storage.owner.as_ref(), span)?.is_empty()
        {
            let excluded = self
                .growth
                .section_shared
                .iter()
                .chain(self.growth.indexed_shared.keys())
                .chain(self.growth.occurrence_peers.keys())
                .chain(self.growth.peer_results.keys())
                .copied()
                .chain(self.growth.versioned_shared.keys().copied())
                .collect();
            self.heap.shared.take_exclusive_protected(
                &mut entry.shared,
                &mut self.heap.workers.records.get_mut(&actor).unwrap().entry_shared,
                &excluded,
            );
            let backing = entry.shared.owned_backing();
            if !backing.children.is_empty() {
                let moved = Storage {
                    typ: crate::ast_util::unit_typ(),
                    value: Value::unit(),
                    owner: Some(backing),
                };
                storage.receive_storage(
                    self.storage.take_storage(&moved, &self.growth, span)?,
                    span,
                )?;
            }
        }
        Ok(())
    }
}
