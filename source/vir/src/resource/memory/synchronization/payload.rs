//! Access through a native guard borrows the existing payload. A local mutex
//! keeps the same vector state, element forest and reservation across unlock.

use super::{
    Operation,
    local::{Interval, View},
};
use crate::{
    ast::*,
    messages::Span,
    resource::memory::{
        analysis::Analysis,
        contracts,
        heap::{Owner, OwnerSlot},
        model::unsupported,
        paths,
        vectors::Receiver,
    },
};

impl Analysis<'_> {
    /// A protected payload is opaque to Verus expressions between borrows.
    /// Freeze its actual initial logical length before moving it into the root.
    pub(in super::super) fn protect_vector_length(&mut self, value: &Expr, child: &mut Owner) {
        if let Some(state) = child.vector
            && child.geometry_known
            && let Some(initial) = &child.geometry
        {
            let length = self.allocation_snapshot(&value.span, initial.clone());
            self.growth.vectors[state].protected_length = Some(length.clone());
            child.geometry = Some(length);
        }
    }

    /// The native borrow names its existing acquisition on every reaching path.
    pub(in super::super) fn guard_access(&mut self, argument: &Expr) -> Result<bool, VirErr> {
        let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &argument.x
        else {
            return Ok(false);
        };
        if !matches!(
            attrs.resource_intrinsic,
            Some(ResourceIntrinsic::Synchronization(
                Operation::GuardBorrow | Operation::GuardBorrowMut
            ))
        ) {
            return Ok(false);
        }
        let [guard] = args.as_slice() else {
            return Err(unsupported(&argument.span, "this guard borrow signature"));
        };
        let Some(View::Payload(interval)) = self.synchronization_view(argument) else {
            return Err(unsupported(&argument.span, "a protected borrow without a checked guard"));
        };
        if !self.storage.holds_interval(interval) {
            return Err(unsupported(
                &argument.span,
                "a protected borrow outside its live acquisition",
            ));
        }
        let payload = paths::referent(&argument.typ);
        self.open_imported_payload(interval, payload, &argument.span)?;
        self.discard(guard)?;
        self.transitions.operation(
            &argument.span,
            super::super::transfer::checked::Operation::GuardBorrow {
                source: guard.clone(),
                interval,
            },
        );
        Ok(true)
    }

    pub(in super::super) fn local_payload(
        &self,
        interval: Interval,
        span: &Span,
    ) -> Result<paths::LocalPath, VirErr> {
        if !self.storage.holds_interval(interval) {
            return Err(unsupported(span, "a protected borrow outside its live acquisition"));
        }
        let (name, mut path) = self.mutex_root(interval.instance).ok_or_else(|| {
            unsupported(span, "a guard borrow without a unique local protected payload")
        })?;
        path.push(OwnerSlot::Contents);
        Ok((name, path))
    }

    /// A mutex reference or a strong alias names the same persistent descriptor.
    /// An imported worker view cannot read the publishing actor's private ledger.
    fn mutex_root(&self, instance: super::Instance) -> Option<paths::LocalPath> {
        let mut roots = Vec::new();
        for (name, root) in self.heap.owners.iter().chain(&self.heap.borrowed) {
            root.visit_paths(&mut Vec::new(), &mut |path, owner| {
                if owner.mutex_instance() == Some(instance) {
                    roots.push((name.clone(), path.clone()));
                }
            });
        }
        if let Some((root, name)) = self.heap.shared.protected_root(instance) {
            if self.growth.versioned_shared.contains_key(&root)
                || self.heap.workers.shares_root(root)
                || self.growth.section_shared.contains(&root)
                || self.growth.indexed_shared.contains_key(&root)
                || self.growth.occurrence_peers.contains_key(&root)
                || self.growth.peer_results.contains_key(&root)
            {
                return None;
            }
            roots.push((name, vec![OwnerSlot::Contents]));
        }
        let [location] = roots.as_slice() else { return None };
        Some(location.clone())
    }

    /// Bind a helper's ownership path through the actual mutex even when the
    /// argument is an immutable reference alias or a native Arc dereference.
    pub(in super::super) fn call_location(
        &self,
        arg: &Expr,
        typ: &Typ,
    ) -> Option<paths::LocalPath> {
        if let Some(View::ReadPayload(id)) = self.synchronization_view(arg) {
            if !crate::ast_util::types_equal(paths::referent(&arg.typ), paths::referent(typ)) {
                return None;
            }
            let (name, mut path) = self.rw_cell_path(id, &arg.span).ok()?;
            path.push(OwnerSlot::Contents);
            return Some((name, path));
        }
        if self.layouts.mutex_payload(paths::referent(typ)).is_some()
            && let Some(View::Mutex(instance)) = self.synchronization_view(arg)
        {
            return self.mutex_root(instance);
        }
        if self.layouts.writable_guard_payload(&arg.typ).is_some()
            && let Some(View::Guard(interval)) = self.synchronization_view(arg)
        {
            return self.mutex_root(interval.instance);
        }
        if let Some(View::Payload(interval)) = self.synchronization_view(arg) {
            return self.local_payload(interval, &arg.span).ok();
        }
        paths::expr(arg, typ)
    }

    pub(in super::super) fn protected_vector(
        &mut self,
        argument: &Expr,
        site: &Span,
    ) -> Result<Option<Receiver>, VirErr> {
        let typ = paths::referent(&argument.typ);
        let location = match self.synchronization_view(argument) {
            Some(View::Payload(interval)) => {
                self.open_imported_payload(interval, typ, site)?;
                self.local_payload(interval, &argument.span)?
            }
            Some(View::ReadPayload(id)) => {
                let (name, mut path) = self.rw_cell_path(id, site)?;
                path.push(OwnerSlot::Contents);
                (name, path)
            }
            _ => return Ok(None),
        };
        match &argument.x {
            ExprX::BorrowMut(place)
            | ExprX::TwoPhaseBorrowMut(place)
            | ExprX::ReadPlace(place, _) => {
                self.access(place, &place.typ)?;
            }
            _ => {
                self.discard(argument)?;
            }
        }
        let (state, counter) = self
            .heap
            .root(&location.0)
            .and_then(|owner| owner.at(&location.1))
            .and_then(|owner| owner.vector)
            .and_then(|id| Some((id, self.growth.vectors[id].protected_length.clone()?)))
            .filter(|_| self.layouts.vector(typ))
            .ok_or_else(|| {
                unsupported(&argument.span, "a protected vector without checked initial geometry")
            })?;
        Ok(Some(Receiver {
            state,
            typ: typ.clone(),
            location,
            length: self.allocation_snapshot(site, counter.clone()),
            protected: Some(counter),
        }))
    }

    /// Mutations use ordinary Vec accounting. The extra state is logical
    /// length only; it contributes no allocation or storage allowance.
    pub(in super::super) fn advance_protected_vector(
        &mut self,
        span: &Span,
        receiver: &Receiver,
        intrinsic: Option<ResourceIntrinsic>,
    ) {
        let Some(counter) = &receiver.protected else { return };
        let length = receiver.length.clone();
        let one = contracts::literal(span, 1);
        let next = match intrinsic {
            Some(ResourceIntrinsic::VecPush) => contracts::add(span, length, one),
            Some(ResourceIntrinsic::VecPop | ResourceIntrinsic::VecRemove) => contracts::maximum(
                span,
                contracts::literal(span, 0),
                contracts::subtract(span, length, one),
            ),
            _ => return,
        };
        self.growth
            .after
            .entry(span.id)
            .or_default()
            .push(crate::resource::memory::symbolic::assign(span, counter, next));
    }
}
