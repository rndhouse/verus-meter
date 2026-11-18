//! Keep a canonical payload intact when its destructor has effects beyond releasing local bytes.
//! A join recovers that same tree. A checked end of its outstanding population runs its drops.
use super::*;
use crate::resource::memory::elements::References;

impl Analysis<'_> {
    pub(in crate::resource::memory) fn ends_indexed_carrier(&self, owner: &Owner) -> bool {
        !self.growth.indexed_shared.is_empty() && owner.references() != References::None
    }

    pub(in crate::resource::memory) fn finish_indexed_payloads(
        &mut self,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        if self.heap.shared.held_payloads.is_empty() || self.current_worker.is_some() {
            return;
        }
        // A live handle collection or selected result may still own a reservation.
        // Even when no such local remains, the generated check must prove zero:
        // temporaries, helper calls and delegated workers cannot forge a final drop.
        let mut outstanding = false;
        for owner in self.heap.owners.values().chain(self.heap.borrowed.values()) {
            owner.visit(&mut |node| {
                outstanding |= node.selected_worker.is_some()
                    || matches!(node.shared, Some(StrongLink::Selected(_)))
                    || node
                        .elements
                        .as_ref()
                        .is_some_and(|elements| elements.references != References::None);
            });
        }
        if outstanding {
            return;
        }
        while let Some(root) =
            self.heap.shared.held_payloads.difference(&self.growth.section_shared).next().copied()
        {
            self.heap.shared.held_payloads.remove(&root);
            let claims = &self.growth.indexed_shared[&root];
            proofs.push(expr::check(
                span,
                crate::ast_util::mk_eq(span, &claims.population.pending, &expr::integer(span, 0)),
                "cannot destroy a shared payload while indexed aliases still own it",
            ));
            self.destroy_owner(claims.backing.clone(), span, true, proofs);
        }
    }
}
