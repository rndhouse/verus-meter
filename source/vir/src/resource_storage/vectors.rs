//! Fixed-capacity vectors: one reservation, with proof-checked non-growing pushes.

use super::analysis::Analysis;
use super::contracts;
use super::model::unsupported;
use crate::ast::*;
use crate::ast_util::*;
use std::sync::Arc;

impl Analysis<'_> {
    pub(super) fn initialize_vector(
        &mut self,
        name: &VarIdent,
        init: &Place,
        typ: &Typ,
    ) -> Result<(), VirErr> {
        if !types_equal(&init.typ, typ) {
            return Err(unsupported(&init.span, "this vector initializer coercion"));
        }
        let source = match &init.x {
            PlaceX::Temporary(expr) => match &expr.x {
                ExprX::Call {
                    target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
                    args,
                    post_args: None,
                    body: None,
                } if matches!(
                    attrs.resource_intrinsic,
                    Some(ResourceIntrinsic::VecNew | ResourceIntrinsic::VecWithCapacity)
                ) =>
                {
                    let capacity = match (attrs.resource_intrinsic, args.as_slice()) {
                        (Some(ResourceIntrinsic::VecNew), []) => contracts::literal(&expr.span, 0),
                        (Some(ResourceIntrinsic::VecWithCapacity), [arg]) => {
                            contracts::quantity(arg, &self.stable_scalars)?
                        }
                        _ => return Err(unsupported(&expr.span, "this vector constructor")),
                    };
                    let cost = contracts::multiply(
                        &expr.span,
                        contracts::literal(
                            &expr.span,
                            self.layouts.vector_element(typ, &expr.span)?,
                        ),
                        capacity.clone(),
                    );
                    let bytes = if let Some(n) = contracts::constant(&cost) {
                        self.storage.reserve(&expr.span, n, "vector backing storage")?;
                        n
                    } else {
                        // Keep a stable expression for this allocation until its
                        // owner drops; a move transfers the reservation identity.
                        self.storage.reserve_dynamic(&expr.span, cost);
                        self.heap.dynamic.insert(name.clone(), expr.span.id);
                        0
                    };
                    self.heap.owners.insert(name.clone(), bytes);
                    self.heap.capacities.insert(name.clone(), capacity);
                    return Ok(());
                }
                ExprX::ReadPlace(place, _) => place,
                _ => {
                    return Err(unsupported(
                        &expr.span,
                        "vector initializers other than new, with_capacity, or a local move",
                    ));
                }
            },
            _ => init,
        };
        let PlaceX::Local(old) = &source.x else {
            return Err(unsupported(&source.span, "vector ownership outside a named local"));
        };
        let bytes = self.move_owner(source)?;
        let capacity = self
            .heap
            .capacities
            .remove(old)
            .ok_or_else(|| unsupported(&source.span, "a vector without a reserved capacity"))?;
        if let Some(id) = self.heap.dynamic.remove(old) {
            self.heap.dynamic.insert(name.clone(), id);
        }
        self.heap.owners.insert(name.clone(), bytes);
        self.heap.capacities.insert(name.clone(), capacity);
        Ok(())
    }

    fn vector_receiver(&mut self, arg: &Expr) -> Result<(VarIdent, Typ), VirErr> {
        let place = match &arg.x {
            ExprX::BorrowMut(p) | ExprX::TwoPhaseBorrowMut(p) => p,
            ExprX::ReadPlace(p, kind) if matches!(kind.preliminary_kind, ReadKind::ImmutBor) => p,
            _ => {
                return Err(unsupported(
                    &arg.span,
                    "vector operations through an aliased owner; borrow its slice instead",
                ));
            }
        };
        let PlaceX::Local(name) = &place.x else {
            return Err(unsupported(&arg.span, "vector operations outside a named local owner"));
        };
        if !self.layouts.vector(&place.typ) {
            return Err(unsupported(&arg.span, "this vector receiver"));
        }
        self.access(place, &place.typ)?;
        Ok((name.clone(), place.typ.clone()))
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
        let (name, typ) = self.vector_receiver(receiver)?;
        if attrs.resource_intrinsic == Some(ResourceIntrinsic::VecPush) {
            if args.len() != 2 {
                return Err(unsupported(&expr.span, "this vector push"));
            }
            let capacity = self
                .heap
                .capacities
                .get(&name)
                .ok_or_else(|| unsupported(&expr.span, "a vector without a reserved capacity"))?
                .clone();
            let TypX::Datatype(_, types, _) = &*typ else { unreachable!() };
            // Read the current logical length at the push, so ordinary branches,
            // preconditions and loop invariants can establish available room.
            let vector = SpannedTyped::new(&expr.span, &typ, ExprX::Var(name));
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
            self.checks
                .push((expr.span.clone(), mk_ineq(&expr.span, &len, &capacity, InequalityOp::Lt)));
            self.initialize_expr(&args[1])?;
        } else if index {
            if args.len() != 2 {
                return Err(unsupported(&expr.span, "this vector index"));
            }
            self.discard(&args[1])?;
        } else if args.len() != 1 {
            return Err(unsupported(&expr.span, "this vector operation"));
        }
        // These operations use existing storage. A discarded pop result creates
        // no declared slot; binding Option values remains outside the subset.
        Ok(Some(0))
    }
}
