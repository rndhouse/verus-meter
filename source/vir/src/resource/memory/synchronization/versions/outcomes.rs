//! Owning results and final cell contents are projections of the same mutex
//! history. A source return freezes the complete result before its proof
//! variables leave scope. The completion retains those bytes until receipt.

use super::*;
use crate::resource::memory::{elements::References, workers::WorkerId};

pub(in crate::resource::memory) struct Observation {
    pub(super) snapshot: Expr,
    /// The returning worker, or the surviving cell at this join.
    pub(in crate::resource::memory) result: Option<WorkerId>,
    /// A release at this join must belong to a published worker.
    pub(super) published: std::collections::BTreeSet<WorkerId>,
    /// Every release by one of these workers must already have happened.
    pub(super) completed: std::collections::BTreeSet<WorkerId>,
}

fn storage(owner: Owner) -> Storage {
    Storage { typ: crate::ast_util::unit_typ(), value: Value::unit(), owner: Some(owner) }
}

impl Analysis<'_> {
    pub(in crate::resource::memory) fn freeze_protected_returns(
        &mut self,
        body: &Span,
        typ: &Typ,
    ) -> Result<(), VirErr> {
        if !self.layouts.owner(typ)
            || self.transitions.protected_versions.bindings.len() != 1
            || !self.layouts.plain_protected_payload(typ)
            || self.transitions.retained_workers
        {
            return Ok(());
        }
        let (result, decl) = expr::local(
            body,
            "protected_result",
            expr::memory_type(),
            expr::empty(body, expr::record_type()),
            Mode::Spec,
        );
        self.growth.declarations.push(decl);
        let role = Accounting::fresh_allocation();
        let mut normal_owner = self.result_owner.take();
        if self.flow.reachable {
            self.freeze_return(body, &mut normal_owner, &result, role)?;
        }
        let normal = self.branch_state();
        let mut edges = std::mem::take(&mut self.flow.exits);
        for edge in &mut edges {
            let site = edge.value_site.as_ref().ok_or_else(|| {
                unsupported(&edge.span, "a protected result without an executable return operand")
            })?;
            self.restore_branch(&edge.state);
            self.freeze_return(site, &mut edge.owner, &result, role)?;
            edge.state = self.branch_state();
        }
        self.flow.exits = edges;
        self.restore_branch(&normal);
        self.result_owner = normal_owner;
        Ok(())
    }

    fn freeze_return(
        &mut self,
        site: &Span,
        owner: &mut Option<Owner>,
        result: &Expr,
        role: u64,
    ) -> Result<(), VirErr> {
        let mut actual = owner
            .take()
            .filter(|o| {
                complete_contents(o) && o.inputs().is_empty() && o.references() == References::None
            })
            .ok_or_else(|| unsupported(site, "an incomplete protected result at a worker exit"))?;
        // Option construction, replacement and pop supply the discriminant as
        // part of the owned value. Its old local binding has just been moved.
        if actual.geometry.is_some()
            && actual.source.as_ref().is_some_and(|(typ, _)| self.layouts.option(typ))
        {
            actual.source = None;
        }
        let origins = self.storage.returned_storage(Some(&actual), &self.growth.elements);
        let start = self.growth.before.get(&site.id).map_or(0, Vec::len);
        let contents = self.snapshot_owner_metadata(site, &actual);
        let mut actions = self.growth.before.get_mut(&site.id).unwrap().split_off(start);
        let detached = self.storage.take_storage(&storage(actual), &self.growth, site)?;
        actions.push(expr::check(
            site,
            crate::ast_util::mk_eq(
                site,
                &detached.live_expression(site).total(),
                &expr::cost(site, contents.clone(), expr::integer(site, 0)),
            ),
            "protected worker result differs from its retained storage",
        ));
        actions.push(expr::assign(site, result, contents.clone()));
        self.growth.after.entry(site.id).or_default().extend(actions);
        self.transitions.protected_versions.returns.push(Publication { contents, origins });
        let amount = expr::cost(site, result.clone(), expr::integer(site, 0));
        let packed =
            Owner { dynamic: Some(role), extent: Some(amount.clone()), ..Owner::default() };
        self.storage.set_allocation(role, packed.kind.clone(), amount);
        *owner = Some(packed);
        Ok(())
    }

    /// Unknown cell contents range over every well-formed descriptor. A
    /// correlated result additionally requires a complete history at domain close.
    fn history_observation(
        &mut self,
        site: &Span,
        root: RootId,
        result: Option<WorkerId>,
        joining: WorkerId,
    ) -> Result<Expr, VirErr> {
        if self.current_worker.is_some() || self.growth.loop_depth != 0 {
            return Err(unsupported(site, "a protected outcome outside its fixed joining domain"));
        }
        let snapshot = self.unrestricted_payload(site, "joined_contents");
        let published: std::collections::BTreeSet<_> =
            self.growth.worker_executions.keys().copied().collect();
        let mut completed = self.heap.shared.joined_holders(root);
        completed.insert(joining);
        self.growth.protected_observations.entry(root).or_default().push(Observation {
            snapshot: snapshot.clone(),
            result,
            published,
            completed,
        });
        Ok(snapshot)
    }

    pub(in crate::resource::memory) fn receive_protected_result(
        &mut self,
        site: &Span,
        actor: WorkerId,
        root: RootId,
        typ: &Typ,
        packed: Owner,
        retained: &mut Accounting,
    ) -> Result<Owner, VirErr> {
        retained.take_storage(&storage(packed), &self.growth, site)?;
        let memory = self.history_observation(site, root, Some(actor), actor)?;
        self.owner_from_metadata(site, typ, memory, metadata::View::Complete, false)
    }

    pub(in crate::resource::memory) fn observe_joined_payload(
        &mut self,
        root: RootId,
        joining: WorkerId,
        site: &Span,
    ) -> Result<(), VirErr> {
        if self.current_worker.is_some()
            || self.growth.indexed_shared.contains_key(&root)
            || self.growth.section_shared.contains(&root)
            || self.growth.peer_results.contains_key(&root)
            || self.growth.occurrence_peers.contains_key(&root)
        {
            return Err(unsupported(
                site,
                "observing a protected payload before all its fixed workers have joined",
            ));
        }
        let typ = self
            .heap
            .shared
            .protected_type(root)
            .ok_or_else(|| unsupported(site, "a joined payload without its mutex type"))?;
        let path = [OwnerSlot::Contents, OwnerSlot::Contents];
        let old = self
            .heap
            .root_mut(&root.binder())
            .and_then(|o| o.take_child(&path))
            .ok_or_else(|| unsupported(site, "a joined payload outside its owning domain"))?;
        self.storage.take_storage(&storage(old), &self.growth, site)?;
        let memory = self.history_observation(site, root, None, joining)?;
        let new = self.owner_from_metadata(site, &typ, memory, metadata::View::Complete, false)?;
        self.heap
            .root_mut(&root.binder())
            .unwrap()
            .at_mut(&path[..1])
            .unwrap()
            .children
            .insert(OwnerSlot::Contents, new);
        self.heap.shared.record_payload_join(root, joining);
        Ok(())
    }
}
