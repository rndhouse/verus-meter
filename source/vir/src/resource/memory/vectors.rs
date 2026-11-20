//! Explicit vector reservations and storage for occupied element slots.

use super::analysis::Analysis;
use super::contracts;
use super::footprint::{Charge, MemoryKind};
use super::heap::Owner;
use super::model::unsupported;
use crate::ast::*;
use crate::ast_util::*;
use std::sync::Arc;

/// Logical vector length used by operation adapters before consuming or mutating it.
pub(super) fn length(span: &crate::messages::Span, types: Typs, vector: Expr) -> Expr {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Int(IntRange::USize)),
        ExprX::Call {
            target: CallTarget::Fun(
                CallTargetKind::Static,
                crate::fun!(CrateId::Vstd => "std_specs", "vec"; "spec_vec_len"),
                types,
                Arc::new(vec![]),
                CallTargetAttrs {
                    resource_intrinsic: None,
                    autospec: AutospecUsage::Final,
                    const_var: false,
                    assume_external_allowed: false,
                },
            ),
            args: Arc::new(vec![vector]),
            post_args: None,
            body: None,
        },
    )
}

impl Analysis<'_> {
    /// Removal invalidates insertion-count and append-only buffer bounds for
    /// both precise forests and opaque retained sums.
    pub(super) fn forget_collection_length(
        &mut self,
        name: &VarIdent,
        path: &[super::heap::OwnerSlot],
    ) {
        let owner = self
            .heap
            .root(name)
            .and_then(|owner| owner.at(path))
            .expect("validated vector argument");
        let state = &mut self.growth.vectors[owner.vector.expect("vector state")];
        state.append_only = false;
        state.sequence_length = None;
        if let Some(elements) = &owner.elements {
            for id in elements.states.values() {
                self.growth.elements[*id].forget_length();
            }
        }
    }

    pub(super) fn allocate_vector(
        &mut self,
        expr: &Expr,
    ) -> Result<Option<super::heap::Owner>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(None);
        };
        if !matches!(
            attrs.resource_intrinsic,
            Some(ResourceIntrinsic::VecNew | ResourceIntrinsic::VecWithCapacity)
        ) {
            return Ok(None);
        }
        let capacity = match (attrs.resource_intrinsic, args.as_slice()) {
            (Some(ResourceIntrinsic::VecNew), []) => contracts::literal(&expr.span, 0),
            (Some(ResourceIntrinsic::VecWithCapacity), [arg]) => {
                contracts::allocation_quantity(arg, &self.allocation_scalars())?
            }
            _ => return Err(unsupported(&expr.span, "this vector constructor")),
        };
        let checked_capacity = capacity.clone();
        let mut changing = false;
        crate::ast_visitor::expr_visitor_check(&capacity, &mut |_, expression| {
            if let ExprX::Var(name) = &expression.x {
                changing |= self.growth.loop_counters.contains(name);
            }
            Ok::<(), VirErr>(())
        })?;
        // A mutable counter's allocation extent belongs to this call, not to
        // the counter's next value after the iteration advances.
        let capacity =
            if changing { self.allocation_snapshot(&expr.span, capacity) } else { capacity };
        let snapshot = match &capacity.x {
            ExprX::Var(name) if changing => Some(name.clone()),
            _ => None,
        };
        let cost = contracts::multiply(
            &expr.span,
            contracts::literal(&expr.span, self.layouts.vector_element(&expr.typ, &expr.span)?),
            capacity.clone(),
        );
        let mut owner =
            Owner { capacity: Some(capacity), extent: Some(cost.clone()), ..Default::default() };
        owner.geometry = Some(contracts::literal(&expr.span, 0));
        if let Some(n) = contracts::constant(&cost) {
            self.storage.reserve(
                &expr.span,
                MemoryKind::host_heap(),
                n,
                "vector backing storage",
            )?;
            owner.bytes = n;
        } else {
            self.storage.reserve_dynamic(&expr.span, MemoryKind::host_heap(), cost.clone());
            owner.dynamic = Some(expr.span.id);
        }
        if self.layouts.owning_elements(&expr.typ) {
            owner.elements = Some(self.new_elements(&expr.span));
        }
        let allocation = super::accounting::Accounting::fresh_allocation();
        let state = self.growth.new_vector(
            &expr.span,
            owner.capacity.clone().unwrap(),
            Charge { kind: owner.kind.clone(), amount: cost },
            self.layouts.vector_element(&expr.typ, &expr.span)?,
            None,
            allocation,
        );
        self.growth.vectors[state].local_constructor = true;
        if let Some(id) = owner.dynamic {
            self.storage.release_dynamic(id);
        }
        self.storage.release(
            &expr.span,
            owner.kind.clone(),
            owner.bytes,
            "track vector allocation",
        );
        owner.bytes = 0;
        owner.dynamic = Some(allocation);
        owner.vector = Some(state);
        self.storage.set_allocation(
            self.growth.vectors[state].backing.id,
            owner.kind.clone(),
            self.growth.vectors[state].backing.bytes.clone(),
        );
        self.transitions.operation(
            &expr.span,
            super::transfer::checked::Operation::Vector {
                capacity: checked_capacity,
                snapshot,
                element: self.layouts.vector_element(&expr.typ, &expr.span)?,
            },
        );
        Ok(Some(owner))
    }

    /// Resolve a vector leaf through the same paths used by ownership summaries.
    pub(super) fn vector_receiver(&mut self, arg: &Expr) -> Result<(usize, Typ, Expr), VirErr> {
        if super::paths::vector_index(arg).is_some() {
            let mut typ = super::paths::referent(&arg.typ);
            while let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
                typ = inner;
            }
            let id = self.vector_argument(arg, typ, &[])?;
            self.discard(arg)?;
            return Ok((id, typ.clone(), super::projections::spec_value(arg)?));
        }
        let place = match &arg.x {
            ExprX::BorrowMut(p) | ExprX::TwoPhaseBorrowMut(p) | ExprX::ReadPlace(p, _) => p,
            _ => {
                return Err(unsupported(
                    &arg.span,
                    "vector operations through an aliased owner; borrow its slice instead",
                ));
            }
        };
        let mut typ = super::paths::referent(&place.typ);
        while let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            typ = inner;
        }
        if !self.layouts.vector(typ) {
            return Err(unsupported(&arg.span, "this vector receiver"));
        }
        let id = self.vector_argument(arg, typ, &[])?;
        self.access(place, if matches!(&*place.typ, TypX::MutRef(_)) { &place.typ } else { typ })?;
        let value =
            if super::paths::expr(arg, typ).is_some_and(|(_, path)| super::paths::indexed(&path)) {
                super::projections::spec_value(arg)?
            } else {
                place_to_spec_expr(place)
            };
        Ok((id, typ.clone(), value))
    }

    /// Resolve a formal child path relative to an actual argument's owner.
    pub(super) fn vector_argument(
        &self,
        arg: &Expr,
        typ: &Typ,
        child: &[super::heap::OwnerSlot],
    ) -> Result<usize, VirErr> {
        let (name, mut path) = super::paths::expr(arg, typ).ok_or_else(|| {
            unsupported(&arg.span, "vector operations outside a named owner or parameter")
        })?;
        path.extend_from_slice(child);
        self.heap
            .root(&name)
            .and_then(|owner| owner.at(&path))
            .and_then(|owner| owner.vector)
            .ok_or_else(|| {
                unsupported(
                    &arg.span,
                    "vector operations through an aliased owner; borrow its slice instead",
                )
            })
    }

    /// Snapshot the new backing before the receiver changes length and publish it
    /// after the operation, including when the vector lives in an enclosing scope.
    fn commit_vector_bytes(&mut self, span: &crate::messages::Span, id: usize, next: Expr) {
        let backing = &self.growth.vectors[id].backing;
        self.growth.updates.entry(span.id).or_default().push(super::symbolic::assign(
            span,
            &backing.next_bytes,
            next,
        ));
        self.growth.after.entry(span.id).or_default().push(super::symbolic::assign(
            span,
            &backing.bytes,
            backing.next_bytes.clone(),
        ));
    }

    fn add_vector_slot(
        &mut self,
        span: &crate::messages::Span,
        id: usize,
        len: Expr,
    ) -> Result<Expr, VirErr> {
        let state = &self.growth.vectors[id];
        let backing = &state.backing;
        let reservation = state.funded_slots(span);
        let next = super::growth::push_bytes(
            span,
            backing.bytes.clone(),
            reservation.clone(),
            len.clone(),
            state.element,
        );
        let extra = super::growth::push_bytes(
            span,
            contracts::literal(span, 0),
            reservation,
            len,
            state.element,
        );
        if let Some(entry) =
            self.growth.section_backings.get(&id).and_then(|entries| entries.last())
        {
            // Regrowing slots removed since entry can fit the entry charge.
            let charge = |bytes| super::growth::section_bytes(span, bytes, entry.clone());
            self.storage.set_allocation(backing.id, backing.kind.clone(), charge(next.clone()));
            self.storage.record_live(span)?;
            self.storage.set_allocation(
                backing.id,
                backing.kind.clone(),
                charge(backing.bytes.clone()),
            );
        } else {
            self.storage.replacement_peak(
                span,
                &Charge { kind: backing.kind.clone(), amount: extra.clone() },
            )?;
        }
        self.commit_vector_bytes(span, id, next);
        let state = &mut self.growth.vectors[id];
        state.backing.changed = true;
        state.pushes += 1;
        Ok(extra)
    }

    pub(super) fn remove_vector_slot(
        &mut self,
        span: &crate::messages::Span,
        id: usize,
        typ: &Typ,
        vector: Expr,
    ) {
        let TypX::Datatype(_, types, _) = &**typ else { unreachable!() };
        let len = length(span, types.clone(), vector);
        let state = &self.growth.vectors[id];
        if !state.backing.changed
            && !state.loop_backing
            && (state.local_constructor
                || contracts::constant(&state.backing.initial_bytes) == Some(0))
        {
            return;
        }
        let next = if state.local_constructor {
            // The post-pop extent is determined by the original reservation
            // and the surviving length. A pop can only reduce the entry charge.
            let remaining = contracts::subtract(span, len, contracts::literal(span, 1));
            let extent =
                super::growth::slots_bytes(span, state.minimum.clone(), remaining, state.element);
            contracts::minimum(span, state.backing.bytes.clone(), extent)
        } else {
            super::growth::pop_bytes(
                span,
                state.backing.bytes.clone(),
                state.funded_slots(span),
                len,
                state.element,
            )
        };
        self.commit_vector_bytes(span, id, next);
        self.growth.vectors[id].removals += 1;
    }

    pub(super) fn vector_expr(&mut self, expr: &Expr) -> Result<Option<u64>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, fun, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(None);
        };
        let index = *fun == crate::fun!(CrateId::Vstd => "std_specs", "vec"; "vec_index")
            || *fun == crate::fun!(CrateId::Vstd => "std_specs", "vec"; "vec_index_mut");
        if !index
            && !matches!(
                attrs.resource_intrinsic,
                Some(
                    ResourceIntrinsic::VecPush
                        | ResourceIntrinsic::VecPop
                        | ResourceIntrinsic::VecRemove
                        | ResourceIntrinsic::VecLen
                        | ResourceIntrinsic::VecAsSlice
                        | ResourceIntrinsic::VecAsMutSlice
                )
            )
        {
            return Ok(None);
        }
        let Some(receiver) = args.first() else {
            return Err(unsupported(&expr.span, "this vector operation"));
        };
        let focused = self.focus_arguments(args, &expr.span)?;
        let bytes = self.vector_operation(expr, args, receiver, index, attrs.resource_intrinsic)?;
        self.finish_projections(&expr.span, focused)?;
        Ok(Some(bytes))
    }

    fn vector_operation(
        &mut self,
        expr: &Expr,
        args: &Exprs,
        receiver: &Expr,
        index: bool,
        intrinsic: Option<ResourceIntrinsic>,
    ) -> Result<u64, VirErr> {
        let (state_id, typ, vector) = self.vector_receiver(receiver)?;
        let grow = !self.growth.vectors[state_id].reserved;
        let mut input = None;
        if self.layouts.owning_elements(&typ)
            && matches!(
                intrinsic,
                Some(ResourceIntrinsic::VecAsSlice | ResourceIntrinsic::VecAsMutSlice)
            )
        {
            return Err(unsupported(&expr.span, "borrowing slice views of owning vectors"));
        }
        let mut allocation = None;
        let mut carried_shared = None;
        if intrinsic == Some(ResourceIntrinsic::VecPush) {
            if args.len() != 2 {
                return Err(unsupported(&expr.span, "this vector push"));
            }
            let state = self.growth.vectors[state_id].clone();
            let capacity = state.capacity.clone();
            let TypX::Datatype(_, types, _) = &*typ else { unreachable!() };
            // Read the current logical length at the push, so ordinary branches,
            // preconditions and loop invariants can establish available room.
            let len = length(&expr.span, types.clone(), vector.clone());
            let element_length = len.clone();
            if state.append_only || state.local_constructor {
                self.growth.vectors[state_id].sequence_length = Some(len.clone());
            }
            let revision = self.growth.revision();
            self.initialize_expr(&args[1])?;
            if revision != self.growth.revision() {
                return Err(unsupported(
                    &args[1].span,
                    "vector allocation changes inside a push argument; bind the argument first",
                ));
            }
            let child = if self.layouts.owner(&args[1].typ) {
                Some(self.result_owner.take().ok_or_else(|| {
                    unsupported(&expr.span, "an inserted element without ownership")
                })?)
            } else {
                None
            };
            let room = mk_ineq(&expr.span, &len, &capacity, InequalityOp::Lt);
            if !grow {
                self.checks.push((expr.span.clone(), room));
                self.storage.record_live(&expr.span)?;
            } else {
                allocation = Some(self.add_vector_slot(&expr.span, state_id, len)?);
            }
            if let Some(mut child) = child {
                let (name, path) = super::paths::expr(receiver, &typ).unwrap();
                input = self.join_input(&expr.span, &(name.clone(), path.clone()), &mut child)?;
                let mut elements = self
                    .heap
                    .root_mut(&name)
                    .and_then(|owner| owner.at_mut(&path))
                    .and_then(|owner| owner.elements.take())
                    .ok_or_else(|| unsupported(&expr.span, "a collection without child state"))?;
                carried_shared = self.insert_child(
                    &expr.span,
                    &args[1].span,
                    &mut elements,
                    child,
                    element_length,
                )?;
                self.heap.root_mut(&name).unwrap().at_mut(&path).unwrap().elements = Some(elements);
                self.record_element_updates(&expr.span)?;
            }
        } else if matches!(
            intrinsic,
            Some(ResourceIntrinsic::VecPop | ResourceIntrinsic::VecRemove)
        ) && self.layouts.owning_elements(&typ)
        {
            // Ownership-producing paths use extraction. A receiver-only effect
            // retains the aggregate conservatively and invalidates length bounds.
            let (name, path) = super::paths::expr(receiver, &typ).unwrap();
            self.forget_collection_length(&name, &path);
        } else if intrinsic == Some(ResourceIntrinsic::VecRemove) {
            let [_, index] = args.as_slice() else {
                return Err(unsupported(&expr.span, "this vector removal"));
            };
            self.discard(index)?;
            let (name, path) = super::paths::expr(receiver, &typ).unwrap();
            self.forget_collection_length(&name, &path);
        } else if intrinsic == Some(ResourceIntrinsic::VecPop) {
            // Removing a scalar changes the sequence shape even though its
            // backing allocation is retained. Export that effect through leaf
            // helpers so an enclosing indexed loan observes the mutation.
            let (name, path) = super::paths::expr(receiver, &typ).unwrap();
            self.forget_collection_length(&name, &path);
        } else if index {
            if args.len() != 2 {
                return Err(unsupported(&expr.span, "this vector index"));
            }
            self.discard(&args[1])?;
        } else if args.len() != 1 {
            return Err(unsupported(&expr.span, "this vector operation"));
        }
        if matches!(intrinsic, Some(ResourceIntrinsic::VecPop | ResourceIntrinsic::VecRemove)) {
            self.remove_vector_slot(&expr.span, state_id, &typ, vector);
        }
        let location = super::paths::expr(receiver, &typ).expect("checked vector receiver");
        let receiver = super::transfer::checked::Place {
            source: receiver.clone(),
            typ: typ.clone(),
            location,
        };
        let operation = match intrinsic {
            Some(ResourceIntrinsic::VecPush) => Some(super::transfer::checked::Operation::Push {
                receiver,
                child: args[1].clone(),
                carried_shared,
                element: self.growth.vectors[state_id].element,
                grow,
                allocation,
                input,
            }),
            Some(ResourceIntrinsic::VecPop | ResourceIntrinsic::VecRemove) => {
                Some(super::transfer::checked::Operation::Remove {
                    input: None,
                    receiver,
                    index: args.get(1).cloned(),
                })
            }
            Some(ResourceIntrinsic::VecLen) => {
                Some(super::transfer::checked::Operation::Length { receiver })
            }
            _ => None,
        };
        if let Some(operation) = operation {
            self.transitions.operation(&expr.span, operation);
        }
        // Push accounts for additional slot storage above. A discarded pop result creates
        // no declared slot; a bound Option result uses its caller-provided destination.
        Ok(0)
    }
}
