//! Vector reservations and conservative replacement-buffer accounting.

use super::analysis::Analysis;
use super::contracts;
use super::footprint::MemoryKind;
use super::model::unsupported;
use crate::ast::*;
use crate::ast_util::*;
use std::sync::Arc;

impl Analysis<'_> {
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
                contracts::quantity(arg, &self.stable_scalars)?
            }
            _ => return Err(unsupported(&expr.span, "this vector constructor")),
        };
        let cost = contracts::multiply(
            &expr.span,
            contracts::literal(&expr.span, self.layouts.vector_element(&expr.typ, &expr.span)?),
            capacity.clone(),
        );
        let mut owner = super::heap::Owner { capacity: Some(capacity), ..Default::default() };
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
        let allocation = super::accounting::Accounting::fresh_allocation();
        let state = self.growth.new_vector(
            &expr.span,
            owner.capacity.clone().unwrap(),
            cost,
            self.layouts.vector_element(&expr.typ, &expr.span)?,
            None,
            allocation,
        );
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
            self.growth.vectors[state].allocation,
            owner.kind.clone(),
            self.growth.vectors[state].bytes.clone(),
        );
        Ok(Some(owner))
    }

    /// Resolve a direct owner or a reborrow of a named vector parameter. Local
    /// reference aliases need their own transfer model and remain unsupported.
    pub(super) fn vector_receiver(&mut self, arg: &Expr) -> Result<(VarIdent, Typ, Expr), VirErr> {
        let place = match &arg.x {
            ExprX::BorrowMut(p) | ExprX::TwoPhaseBorrowMut(p) | ExprX::ReadPlace(p, _) => p,
            _ => {
                return Err(unsupported(
                    &arg.span,
                    "vector operations through an aliased owner; borrow its slice instead",
                ));
            }
        };
        if let PlaceX::Temporary(value) = &place.x {
            if self.layouts.borrowed_vector(&place.typ).is_some() {
                return self.vector_receiver(value);
            }
        }
        let (name, typ) = match &place.x {
            PlaceX::Local(name) if self.layouts.vector(&place.typ) => (name, &place.typ),
            PlaceX::Local(name) if self.heap.borrowed.contains_key(name) => (
                name,
                self.layouts
                    .borrowed_vector(&place.typ)
                    .ok_or_else(|| unsupported(&arg.span, "this vector receiver"))?,
            ),
            PlaceX::DerefMut(base) => {
                let PlaceX::Local(name) = &base.x else {
                    return Err(unsupported(
                        &arg.span,
                        "vector reborrows outside a named parameter",
                    ));
                };
                if !self.heap.borrowed.contains_key(name) || !self.layouts.vector(&place.typ) {
                    return Err(unsupported(
                        &arg.span,
                        "vector reborrows outside a named parameter",
                    ));
                }
                (name, &place.typ)
            }
            _ => {
                return Err(unsupported(
                    &arg.span,
                    "vector operations outside a named owner or parameter",
                ));
            }
        };
        self.access(place, typ)?;
        let vector = place_to_spec_expr(place);
        Ok((name.clone(), typ.clone(), vector))
    }

    pub(super) fn vector_state(&self, name: &VarIdent) -> Option<usize> {
        self.heap
            .owners
            .get(name)
            .and_then(|o| o.vector)
            .or_else(|| self.heap.borrowed.get(name).copied())
    }

    pub(super) fn vector_capacity(&self, name: &VarIdent) -> Option<Expr> {
        self.vector_state(name).map(|id| self.growth.vectors[id].capacity.clone())
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
        let (name, typ, vector) = self.vector_receiver(receiver)?;
        if attrs.resource_intrinsic == Some(ResourceIntrinsic::VecPush) {
            if args.len() != 2 {
                return Err(unsupported(&expr.span, "this vector push"));
            }
            let state_id = self
                .vector_state(&name)
                .ok_or_else(|| unsupported(&expr.span, "untracked vector allocation"))?;
            let state = self.growth.vectors[state_id].clone();
            let capacity = state.capacity.clone();
            let TypX::Datatype(_, types, _) = &*typ else { unreachable!() };
            // Read the current logical length at the push, so ordinary branches,
            // preconditions and loop invariants can establish available room.
            let len = SpannedTyped::new(
                &expr.span,
                &Arc::new(TypX::Int(IntRange::USize)),
                ExprX::Call {
                    target: CallTarget::Fun(
                        CallTargetKind::Static,
                        crate::fun!(CrateId::Vstd => "std_specs", "vec"; "spec_vec_len"),
                        types.clone(),
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
            );
            let revision = self.growth.revision();
            self.initialize_expr(&args[1])?;
            if revision != self.growth.revision() {
                return Err(unsupported(
                    &args[1].span,
                    "vector allocation changes inside a push argument; bind the argument first",
                ));
            }
            let room = mk_ineq(&expr.span, &len, &capacity, InequalityOp::Lt);
            if state.reserved || self.growth.section_protected.contains(&state_id) {
                self.checks.push((expr.span.clone(), room));
                return Ok(Some(0));
            }
            let new_capacity =
                super::growth::grown_capacity(&expr.span, len.clone(), state.element);
            let new_bytes = contracts::multiply(
                &expr.span,
                contracts::literal(&expr.span, state.element),
                new_capacity.clone(),
            );
            let extra = super::growth::select(
                &expr.span,
                room.clone(),
                contracts::literal(&expr.span, 0),
                new_bytes,
            );
            // Reserve the replacement before releasing the old buffer. A lower
            // bound may underestimate real capacity, so this can overcount growth.
            let temporary = super::accounting::Accounting::fresh_allocation();
            self.storage.set_allocation(temporary, MemoryKind::host_heap(), extra.clone());
            self.storage.record_live(&expr.span)?;
            self.storage.release_dynamic(temporary);
            let retained = contracts::maximum(&expr.span, state.bytes.clone(), extra);
            let mut lower = contracts::maximum(
                &expr.span,
                capacity.clone(),
                contracts::add(&expr.span, len, contracts::literal(&expr.span, 1)),
            );
            if state.input.is_none() && state.element != 0 {
                // Equality of a sound lower and upper bound establishes exact
                // capacity, so local vectors can retain all their new spare room.
                let exact = mk_eq(
                    &expr.span,
                    &state.bytes,
                    &contracts::multiply(
                        &expr.span,
                        capacity.clone(),
                        contracts::literal(&expr.span, state.element),
                    ),
                );
                let exact_lower = super::growth::select(&expr.span, room, capacity, new_capacity);
                lower = super::growth::select(&expr.span, exact, exact_lower, lower);
            }
            self.growth.updates.entry(expr.span.id).or_default().extend([
                super::growth::assign(&expr.span, &state.next_capacity, lower),
                super::growth::assign(&expr.span, &state.next_bytes, retained),
            ]);
            self.growth.after.entry(expr.span.id).or_default().extend([
                super::growth::assign(&expr.span, &state.bytes, state.next_bytes.clone()),
                super::growth::assign(&expr.span, &state.capacity, state.next_capacity.clone()),
            ]);
            self.growth.vectors[state_id].changed = true;
            self.growth.vectors[state_id].pushes += 1;
        } else if index {
            if args.len() != 2 {
                return Err(unsupported(&expr.span, "this vector index"));
            }
            self.discard(&args[1])?;
        } else if args.len() != 1 {
            return Err(unsupported(&expr.span, "this vector operation"));
        }
        // Push accounts for replacement storage above. A discarded pop result creates
        // no declared slot; a bound Option result uses its caller-provided destination.
        Ok(Some(0))
    }
}
