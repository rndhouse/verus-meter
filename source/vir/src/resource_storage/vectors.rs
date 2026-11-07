//! Fixed-capacity vectors: one reservation, with proof-checked non-growing pushes.

use super::analysis::Analysis;
use super::contracts;
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
            self.storage.reserve(&expr.span, n, "vector backing storage")?;
            owner.bytes = n;
        } else {
            self.storage.reserve_dynamic(&expr.span, cost);
            owner.dynamic = Some(expr.span.id);
        }
        Ok(Some(owner))
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
                .owners
                .get(&name)
                .and_then(|owner| owner.capacity.as_ref())
                .ok_or_else(|| {
                    unsupported(
                        &expr.span,
                        "push into an incoming vector without a capacity contract",
                    )
                })?
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
        // no declared slot; a bound Option result uses its caller-provided destination.
        Ok(Some(0))
    }
}
