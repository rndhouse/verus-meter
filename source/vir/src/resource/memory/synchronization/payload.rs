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
        // Canonical owning roots are disjoint. Imported Arc backing requires
        // a shared mutation summary before this local view can be used there.
        let mut roots = Vec::new();
        for (name, root) in &self.heap.owners {
            root.visit_paths(&mut Vec::new(), &mut |path, owner| {
                if owner.mutex_instance() == Some(interval.instance) {
                    let mut path = path.clone();
                    path.push(OwnerSlot::Contents);
                    roots.push((name.clone(), path));
                }
            });
        }
        let [location] = roots.as_slice() else {
            return Err(unsupported(
                span,
                "a guard borrow without a unique local protected payload",
            ));
        };
        Ok(location.clone())
    }

    pub(in super::super) fn protected_vector(
        &mut self,
        argument: &Expr,
        site: &Span,
    ) -> Result<Option<Receiver>, VirErr> {
        let Some(View::Payload(interval)) = self.synchronization_view(argument) else {
            return Ok(None);
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
        let typ = paths::referent(&argument.typ);
        let location = self.local_payload(interval, &argument.span)?;
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
