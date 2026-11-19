//! Move reservations between named Arc handles and runtime vector slots.
//! The publishing frame owns the backing through both representations.

use super::*;
use crate::resource::memory::shared::selected_record;

impl Analysis<'_> {
    /// A known returned Arc entering a vector exchanges its finite reference for
    /// one reservation on the same root. The payload stays in the publisher.
    pub(in crate::resource::memory) fn reserve_known_slot(
        &mut self,
        span: &Span,
        owner: &mut Owner,
    ) -> Result<(), VirErr> {
        let Some(StrongLink::Known(root)) = owner.shared else { return Ok(()) };
        let Some(claims) = self.growth.indexed_shared.get(&root) else { return Ok(()) };
        self.require_indexed_claim_owner(span)?;
        let pending = &claims.population.pending;
        let mut proofs = vec![expr::assign(
            span,
            pending,
            contracts::add(span, pending.clone(), expr::integer(span, 1)),
        )];
        if let Some(backing) = self.heap.shared.release(root) {
            self.release_shared_backing(root, backing, span, &mut proofs);
        }
        self.growth.before.entry(span.id).or_default().extend(proofs);
        owner.shared = self
            .heap
            .shared
            .select_alias(expr::integer(span, root.serial()), [root].into(), None)
            .shared;
        Ok(())
    }

    /// Move a local alias into a vector slot. If other local clones survive,
    /// reserve the new slot separately; otherwise its existing reservation moves.
    pub(in crate::resource::memory) fn store_selected_slot(
        &mut self,
        span: &Span,
        id: u64,
        forest: &Expr,
        child: &Expr,
        path: &Expr,
    ) -> Result<(), VirErr> {
        self.require_indexed_claim_owner(span)?;
        let alias = self.heap.shared.selection(id).clone();
        let last = self.heap.shared.release_selection(id).is_some();
        let proofs = self.growth.before.entry(span.id).or_default();
        for (root, claims) in &self.growth.indexed_shared {
            let key = expr::integer(span, root.serial());
            proofs.push(expr::lemma(span, "shared_count_empty", vec![key.clone()]));
            proofs.push(expr::lemma(
                span,
                "shared_count_slot",
                vec![alias.identity.clone(), key.clone()],
            ));
            proofs.push(expr::lemma(
                span,
                "shared_count_insert",
                vec![forest.clone(), child.clone(), path.clone(), key],
            ));
            if !last && alias.roots.contains(root) {
                let next = contracts::add(
                    span,
                    claims.population.pending.clone(),
                    alias.reservation(span, *root),
                );
                proofs.push(expr::assign(span, &claims.population.pending, next));
            }
        }
        Ok(())
    }

    pub(in crate::resource::memory) fn take_selected_slot(
        &mut self,
        span: &Span,
        child: Expr,
    ) -> Result<Owner, VirErr> {
        self.require_indexed_claim_owner(span)?;
        let roots = self.growth.indexed_shared.keys().copied().collect();
        let owner = self.reserve_arc_result(span, child.clone(), roots);
        let Some(StrongLink::Selected(id)) = owner.shared else { unreachable!() };
        let identity = self.heap.shared.selection(id).identity.clone();
        let singleton = expr::push(
            span,
            expr::empty(span, expr::record_type()),
            selected_record(span, identity.clone()),
        );
        let proofs = self.growth.before.entry(span.id).or_default();
        proofs.push(expr::check(
            span,
            crate::ast_util::mk_eq(span, &child, &singleton),
            "cannot establish the selected Arc slot's complete ownership",
        ));
        for root in self.growth.indexed_shared.keys() {
            let key = expr::integer(span, root.serial());
            proofs.push(expr::lemma(span, "shared_count_slot", vec![identity.clone(), key]));
        }
        // If only one canonical root is possible, the checked slot record can
        // return directly to a finite handle and recover its original payload.
        if self.growth.indexed_shared.len() == 1 {
            let root = *self.growth.indexed_shared.keys().next().unwrap();
            let alias = self.heap.shared.release_selection(id).expect("fresh selected slot");
            let mut proofs = vec![];
            self.release_selected_alias(span, alias, &mut proofs);
            self.growth.before.entry(span.id).or_default().extend(proofs);
            return self.restore_indexed_alias(span, root);
        }
        Ok(owner)
    }

    pub(in crate::resource::memory) fn release_selected_slots(
        &self,
        span: &Span,
        forest: &Expr,
        proofs: &mut Vec<Stmt>,
    ) {
        for (root, claims) in &self.growth.indexed_shared {
            let count = expr::operation(
                span,
                "shared_count",
                vec![forest.clone(), expr::integer(span, root.serial())],
                crate::ast_util::int_typ(),
            );
            proofs.push(expr::lemma(
                span,
                "shared_count_nonnegative",
                vec![forest.clone(), expr::integer(span, root.serial())],
            ));
            claims.population.release(
                span,
                count,
                "cannot reconcile stored Arc reservations",
                proofs,
            );
        }
    }
}
