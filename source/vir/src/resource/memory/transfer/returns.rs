//! Ordinary helpers can return an extracted owner on one edge and an empty
//! result on another. Keep the local charge at each source exit and select
//! its original regions with the same condition as the returned forest.

use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{
    accounting::Accounting,
    analysis::Analysis,
    control::Edge,
    elements::References,
    footprint::MemoryKind,
    heap::Owner,
    lifetime::{Storage, Value},
    metadata::expr,
    model::unsupported,
};
use std::sync::Arc;

impl Analysis<'_> {
    pub(in super::super) fn prepare_guard_returns(
        &mut self,
        function: &Function,
        body: &Span,
    ) -> Result<(), VirErr> {
        let typ = &function.x.outer_ret.x.typ;
        if !self.transitions.synchronization_inputs.has_guards()
            || self.flow.exits.is_empty()
            || !self.layouts.owner(typ)
            || !self.layouts.plain_protected_payload(typ)
        {
            return Ok(());
        }
        let mut owners = self
            .flow
            .exits
            .iter()
            .filter_map(|edge| edge.owner.as_ref())
            .chain(self.result_owner.iter().filter(|_| self.flow.reachable));
        let Some(first) = owners.next() else { return Ok(()) };
        if owners.all(|owner| crate::resource::memory::control::compatible(first, owner)) {
            return Ok(());
        }
        let (amount, declaration) = expr::local(
            body,
            "returned_bytes",
            crate::ast_util::int_typ(),
            expr::integer(body, 0),
            Mode::Spec,
        );
        self.growth.declarations.push(declaration);
        let role = Accounting::fresh_allocation();
        let mut normal = self.result_owner.take();
        if self.flow.reachable {
            self.pack_guard_return(body, &mut normal, &amount, role)?;
        }
        let state = self.branch_state();
        let mut edges = std::mem::take(&mut self.flow.exits);
        for edge in &mut edges {
            self.restore_branch(&edge.state);
            let site = edge.value_site.as_ref().ok_or_else(|| {
                unsupported(&edge.span, "an owning return without a source operand")
            })?;
            self.pack_guard_return(site, &mut edge.owner, &amount, role)?;
            edge.state = self.branch_state();
        }
        self.restore_branch(&state);
        self.flow.exits = edges;
        self.result_owner = normal;
        self.transitions.packed_returns = true;
        Ok(())
    }

    fn pack_guard_return(
        &mut self,
        site: &Span,
        result: &mut Option<Owner>,
        amount: &Expr,
        role: u64,
    ) -> Result<(), VirErr> {
        let actual = result
            .take()
            .ok_or_else(|| unsupported(site, "an owning exit without returned storage"))?;
        let mut plain = actual.references() == References::None;
        actual.visit(&mut |node| {
            plain &= node.kind == MemoryKind::host_heap()
                && node.synchronization.is_none()
                && node.suspended_payload.is_none()
                && node.elements.as_ref().is_none_or(|e| {
                    e.inputs.is_empty()
                        && e.states.keys().all(|kind| *kind == MemoryKind::host_heap())
                });
        });
        if !plain {
            return Err(unsupported(
                site,
                "a conditional helper result without a plain allocation and input-region description",
            ));
        }
        self.transitions
            .returned
            .extend(self.storage.returned_storage(Some(&actual), &self.growth.elements));
        let storage =
            Storage { typ: crate::ast_util::unit_typ(), value: Value::unit(), owner: Some(actual) };
        let charge = self.storage.take_storage(&storage, &self.growth, site)?;
        self.growth.after.entry(site.id).or_default().push(expr::assign(
            site,
            amount,
            charge.live_expression(site).total(),
        ));
        // Geometry and ordered children are instantiated by the mandatory
        // body-derived transfer template. Keep each fixed original region at
        // its structural path, independently of the freshly retained bytes.
        fn originals(node: Owner) -> Owner {
            Owner {
                input: node.input,
                children: node
                    .children
                    .into_iter()
                    .map(|(slot, child)| (slot, originals(child)))
                    .collect(),
                ..Owner::default()
            }
        }
        let mut packed = originals(storage.owner.expect("detached return"));
        for id in packed.inputs() {
            self.storage.add_input(id);
        }
        self.storage.set_allocation(role, packed.kind.clone(), amount.clone());
        packed.dynamic = Some(role);
        packed.extent = Some(amount.clone());
        *result = Some(packed);
        Ok(())
    }

    pub(in super::super) fn align_guard_exit(
        &mut self,
        normal: &mut Option<Owner>,
        edge: &mut Edge,
    ) -> Result<(), VirErr> {
        // Temporarily give the detached result a role alongside the surviving
        // parameters so the same branch join partitions *all* original regions.
        // It never becomes a source local or acquires an inline charge.
        let role = VarIdent(
            Arc::new("$memory_returned_owner".into()),
            VarIdentDisambiguate::VirTemp(edge.span.id),
        );
        if self.transitions.packed_returns {
            self.heap.owners.insert(role.clone(), normal.take().expect("packed return"));
            edge.state.heap.owners.insert(role.clone(), edge.owner.take().expect("packed return"));
        }
        self.join_conditional_inputs(&edge.span, &mut edge.state)?;
        if self.transitions.packed_returns {
            *normal = self.heap.owners.remove(&role);
            edge.owner = edge.state.heap.owners.remove(&role);
        }
        Ok(())
    }
}
