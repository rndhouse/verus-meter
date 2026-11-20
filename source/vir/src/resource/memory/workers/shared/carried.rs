//! A carried allocation owns private bytes and may link to fixed shared roots.
use super::*;

impl Analysis<'_> {
    /// Move privately owned backing into this visit's slot. A strong link moves
    /// one claim, while only the last claim moves the backing it names. This
    /// also handles diamonds without charging the common descendant twice.
    pub(super) fn pack_occurrence_backing(
        &mut self,
        span: &Span,
        actor: WorkerId,
        outer: RootId,
        mut backing: Owner,
        forest: &Expr,
    ) -> Result<Expr, VirErr> {
        self.pack_payload_job(span, actor, outer, &mut backing, forest)?;
        let mut fixed = BTreeMap::new();
        backing.visit_paths(&mut vec![], &mut |path, node| {
            if let Some(root) = node.shared.and_then(StrongLink::known)
                && self.transitions.owns_fixed_root(root)
            {
                fixed.insert(path.clone(), root);
            }
        });
        let direct = backing
            .children
            .get(&crate::resource::memory::heap::OwnerSlot::Contents)
            .and_then(|child| child.shared)
            .and_then(StrongLink::known);
        let mut pending = vec![(true, backing)];
        let mut open = BTreeMap::new();
        let mut extents = Vec::new();
        while let Some((outermost, mut owner)) = pending.pop() {
            if owner.references() != crate::resource::memory::elements::References::None {
                let links = self.heap.shared.captured_view(Some(&owner), span)?;
                for (root, count, child) in self.heap.shared.index_imports(&links, span)? {
                    if outermost && self.transitions.owns_fixed_root(root) {
                        self.publish_fixed_claims(actor, root, count, child, span)?;
                        continue;
                    }
                    // Matching loop nests only establishes the constructor scope.
                    // The moved strong links below establish exclusive ownership.
                    let same_loop_nest = self
                        .transitions
                        .shared_constructor(outer)
                        .zip(self.transitions.shared_constructor(root))
                        .is_some_and(|((_, a), (_, b))| {
                            !a.is_empty()
                                && a.iter().map(|(site, _)| site).eq(b.iter().map(|(site, _)| site))
                        });
                    if !same_loop_nest
                        || self.growth.occurrence_roots.values().any(|site| *site == root)
                        || self.growth.section_shared.contains(&root)
                    {
                        return Err(unsupported(
                            span,
                            "carrying a nested Arc outside its private allocation visit",
                        ));
                    }
                    if self.heap.shared.has_strong(root) {
                        open.insert(root, (count, child));
                    } else {
                        open.remove(&root);
                        pending.push((false, child));
                    }
                }
                // The actual handle counts above account for all fixed links.
                // Other ownership obligations still have to pass the leaf check.
                owner.visit_mut(&mut |node| node.shared = None);
            }
            let inputs = owner.inputs();
            if !inputs.is_empty()
                && self.current_worker.is_none()
                && owner.references() == crate::resource::memory::elements::References::None
            {
                self.transitions.carried_inputs.extend(inputs);
            } else {
                Self::check_occurrence_payload(span, &owner)?;
            }
            extents.push(self.transfer_occurrence_backing(span, owner)?);
        }
        self.publish_nested_peer(span, actor, outer, direct, open, forest)?;
        if self.growth.occurrence_links.get(&actor).is_some_and(|prior| prior != &fixed) {
            return Err(unsupported(span, "a worker family with varying nested shared ownership"));
        }
        self.growth.occurrence_links.insert(actor, fixed);
        Ok(extents.into_iter().reduce(|a, b| contracts::add(span, a, b)).expect("outer backing"))
    }

    pub(super) fn transfer_occurrence_backing(
        &mut self,
        span: &Span,
        backing: Owner,
    ) -> Result<Expr, VirErr> {
        use crate::resource::memory::footprint::MemoryKind;
        let charges = self.owner_charges(span, &backing);
        let upper = self.owner_upper(span, &backing);
        let kind = MemoryKind::host_heap();
        if charges.iter().any(|(k, v)| k != &kind && contracts::constant(v) != Some(0)) {
            return Err(unsupported(
                span,
                "transporting a shared allocation with multiple memory kinds",
            ));
        }
        let bytes = upper
            .get(&kind)
            .cloned()
            .ok_or_else(|| unsupported(span, "an occurrence without a heap extent"))?;
        let actual = charges.get(&kind).ok_or_else(|| {
            unsupported(span, "a shared occurrence without a charged heap allocation")
        })?;
        self.growth.before.entry(span.id).or_default().push(expr::check(
            span,
            crate::ast_util::mk_ineq(span, actual, &bytes, InequalityOp::Le),
            "cannot establish the transported shared backing extent",
        ));
        self.release_owner_storage(backing, span, false)?;
        Ok(bytes)
    }

    pub(super) fn restore_payload_links(
        &mut self,
        span: &Span,
        occurrence: &Occurrence,
        backing: &mut Owner,
    ) -> Result<(), VirErr> {
        // The selected record already proved membership in these families. A
        // common path therefore names the same fixed root for every alternative.
        if let Some(links) = occurrence
            .templates
            .iter()
            .filter_map(|actor| self.growth.occurrence_links.get(actor))
            .find(|links| !links.is_empty())
        {
            if !occurrence
                .templates
                .iter()
                .all(|actor| self.growth.occurrence_links.get(actor) == Some(links))
            {
                return Err(unsupported(
                    span,
                    "mixed worker results with different nested shared ownership",
                ));
            }
            self.require_indexed_claim_owner(span)?;
            for (path, root) in links.clone() {
                let mut node = &mut *backing;
                for slot in path {
                    node = node.children.entry(slot).or_default();
                }
                node.shared = self.restore_indexed_alias(span, root)?.shared;
            }
        }
        Ok(())
    }
}
