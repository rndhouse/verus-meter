//! Native Result transport is justified by the checked worker, not by the
//! functional join specification alone. Ordinary Result values gain no witness.

use super::super::{
    analysis::Analysis, growth::Growth, heap::OwnerSlot, lifetime::Value, model::unsupported,
};
use crate::{ast::*, ast_util::*, messages::Span};
use std::sync::Arc;

/// This generated executable binding is introduced after mode checking. Its
/// sole read moves the original join result into the original source context;
/// it has no entry in the source read-kind inference table.
pub(crate) fn generated_join_move(place: &Place, kind: &UnfinalizedReadKind) -> bool {
    matches!(&place.x, PlaceX::Local(name)
        if name.0.as_str() == "$memory_join_result"
            && matches!(name.1, VarIdentDisambiguate::VirTemp(_)))
        && matches!(kind.preliminary_kind, ReadKind::Move(MoveExecToProofOkay::No))
}

/// Reviewed source-semantic rule: a completed panic-free worker joins with Ok.
/// All body/helper correctness obligations still run in Verus; allocation and
/// thread-creation failures are excluded by the documented execution domain.
/// A failed body proof invalidates the whole crate. The deferred global memory
/// diagnostic also prevents verification/export while the envelope is missing.
/// Keep the original call, including its functional result postcondition.
pub(in super::super) fn resolve_join(
    source: &Expr,
    call: Expr,
    growth: &Growth,
    fresh_span: &dyn Fn(&Span) -> Span,
) -> Result<Expr, VirErr> {
    let Some(joins) = growth.worker_joins.get(&source.span.id) else { return Ok(call) };
    // A conditional occurrence is safe only if every alternative retains its
    // checked body dependencies. An empty set cannot justify join success.
    if joins.is_empty()
        || joins.iter().any(|join| {
            join.families.is_empty()
                || join.families.iter().any(|actor| {
                    growth
                        .worker_executions
                        .get(actor)
                        .is_none_or(|execution| execution.actor != *actor)
                })
        })
        || !matches!(&source.x,
        ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), .. }
            if matches!(attrs.resource_intrinsic, Some(ResourceIntrinsic::Concurrency(op)) if op.joins()))
    {
        return Err(unsupported(
            &source.span,
            "join success attached to a different actor or operation",
        ));
    }
    let TypX::Datatype(datatype, _, _) = &*source.typ else {
        return Err(unsupported(&source.span, "join success without a Result value"));
    };
    let name = VarIdent(
        Arc::new("$memory_join_result".into()),
        VarIdentDisambiguate::VirTemp(super::super::accounting::Accounting::fresh_allocation()),
    );
    let place =
        || SpannedTyped::new(&fresh_span(&source.span), &source.typ, PlaceX::Local(name.clone()));
    let declaration = crate::def::Spanned::new(
        fresh_span(&source.span),
        StmtX::Decl {
            pattern: SpannedTyped::new(
                &fresh_span(&source.span),
                &source.typ,
                PatternX::Var(PatternBinding {
                    name: name.clone(),
                    by_ref: ByRef::No,
                    typ: source.typ.clone(),
                    user_mut: Some(false),
                    copy: false,
                    move_exec_to_proof_okay: MoveExecToProofOkay::No,
                }),
            ),
            mode: Some((Mode::Exec, DeclProph::Default)),
            init: Some(SpannedTyped::new(
                &fresh_span(&source.span),
                &source.typ,
                PlaceX::Temporary(call),
            )),
            els: None,
            assert_irrefutable: false,
        },
    );
    let value = SpannedTyped::new(&fresh_span(&source.span), &source.typ, ExprX::Var(name.clone()));
    let condition = SpannedTyped::new(
        &fresh_span(&source.span),
        &bool_typ(),
        ExprX::UnaryOpr(
            UnaryOpr::IsVariant { datatype: datatype.clone(), variant: Arc::new("Ok".into()) },
            value,
        ),
    );
    let proof = SpannedTyped::new(
        &fresh_span(&source.span),
        &unit_typ(),
        ExprX::AssertAssume { is_assume: true, expr: condition, msg: None },
    );
    let result = SpannedTyped::new(
        &fresh_span(&source.span),
        &source.typ,
        ExprX::ReadPlace(
            place(),
            UnfinalizedReadKind {
                preliminary_kind: ReadKind::Move(MoveExecToProofOkay::No),
                id: 0,
            },
        ),
    );
    Ok(mk_block(
        &fresh_span(&source.span),
        vec![declaration, crate::def::Spanned::new(fresh_span(&source.span), StmtX::Expr(proof))],
        Some(result),
    ))
}

impl Analysis<'_> {
    pub(in super::super) fn worker_result_match(
        &mut self,
        expr: &Expr,
        scrutinee: &Place,
        arms: &Arms,
        new_value: bool,
    ) -> Result<(), VirErr> {
        let (payload, _) = self
            .layouts
            .result_payloads(&scrutinee.typ)
            .ok_or_else(|| unsupported(&expr.span, "this primitive Result match"))?;
        let payload = payload.clone();
        let TypX::Datatype(datatype, _, _) = &*scrutinee.typ else { unreachable!() };
        let mut success = None;
        for arm in arms.iter() {
            if !matches!(arm.x.guard.x, ExprX::Const(Constant::Bool(true))) {
                return Err(unsupported(&arm.span, "guarded primitive Result matches"));
            }
            match &arm.x.pattern.x {
                PatternX::Constructor(name, variant, fields)
                    if name == datatype && fields.len() == 1 =>
                {
                    match variant.as_str() {
                        "Ok" if success.is_none() => success = Some((arm, &fields[0].a)),
                        "Err" => {}
                        _ => {
                            return Err(unsupported(
                                &arm.span,
                                "this primitive Result outcome pattern",
                            ));
                        }
                    }
                }
                _ => {
                    return Err(unsupported(
                        &arm.span,
                        "primitive Result matches require explicit Ok and Err outcomes",
                    ));
                }
            }
        }
        let (arm, pattern) = success
            .ok_or_else(|| unsupported(&expr.span, "Result match without its success payload"))?;
        let value = self.produce_place(scrutinee, &scrutinee.typ, false, &expr.span)?;
        let mut owner = self.result_owner.take().ok_or_else(|| {
            unsupported(&expr.span, "Result match without checked outcome ownership")
        })?;
        self.checked_result(&owner, &expr.span)?;
        self.transitions.operation(
            &expr.span,
            super::super::transfer::checked::Operation::JoinedMatch {
                source: scrutinee.clone(),
                pattern: pattern.clone(),
                body: arm.x.body.clone(),
                observed_scalar: self.observed_worker_scalar(&owner),
            },
        );
        let payload_owner = owner.children.remove(&OwnerSlot::Contents);
        owner.joined = None;
        self.release_owner(owner, &expr.span);
        self.release_value(value, &expr.span);
        let mut bindings = Vec::new();
        self.option_pattern(pattern, &payload, &mut bindings, payload_owner, None)?;
        for (name, bytes) in &bindings {
            let id = self.storage.reserve_value(
                &arm.x.body.span,
                super::super::footprint::MemoryKind::host_local(),
                *bytes,
            )?;
            self.slots.insert(
                name.clone(),
                Value { bytes: *bytes, ids: [id].into(), origins: [id].into(), ..Value::unit() },
            );
        }
        let exits = self.flow.exits.len();
        if new_value {
            let value = self.produce(&arm.x.body)?;
            if self.flow.reachable {
                self.produced = Some(value);
            }
        } else if super::super::model::unit(&arm.x.body.typ) {
            self.discard(&arm.x.body)?;
        } else {
            self.initialize_expr(&arm.x.body)?;
        }
        self.cleanup_scope(
            &arm.x.body.span,
            &bindings.into_iter().map(|(name, _)| (arm.span.clone(), name)).collect::<Vec<_>>(),
            exits,
        );
        Ok(())
    }

    pub(in super::super) fn extract_worker_result(
        &mut self,
        expr: &Expr,
    ) -> Result<Option<Value>, VirErr> {
        let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &expr.x else {
            return Ok(None);
        };
        if attrs.resource_intrinsic != Some(ResourceIntrinsic::ResultUnwrap) {
            return Ok(None);
        }
        let [source] = args.as_slice() else {
            return Err(unsupported(&expr.span, "this Result extraction"));
        };
        let (success, _) = self
            .layouts
            .result_payloads(&source.typ)
            .ok_or_else(|| unsupported(&expr.span, "extraction without a reviewed Result type"))?;
        if !types_equal(success, &expr.typ) {
            return Err(unsupported(&expr.span, "inconsistent Result extraction type"));
        }
        let value = self.produce(source)?;
        let mut owner = self.result_owner.take().ok_or_else(|| {
            unsupported(&expr.span, "Result extraction without checked outcome ownership")
        })?;
        self.checked_result(&owner, &expr.span)?;
        let observed_scalar = self.observed_worker_scalar(&owner);
        self.transitions.operation(
            &expr.span,
            super::super::transfer::checked::Operation::Unwrap {
                source: source.clone(),
                observed_scalar,
            },
        );
        let result = self.fresh_value(&expr.span, &expr.typ)?;
        self.result_owner = owner.children.remove(&OwnerSlot::Contents);
        owner.joined = None;
        self.release_owner(owner, &expr.span);
        self.release_value(value, &expr.span);
        Ok(Some(result))
    }

    fn observed_worker_scalar(&self, owner: &super::super::heap::Owner) -> bool {
        owner.joined.as_ref().unwrap().iter().all(|actor| {
            self.growth.worker_executions[actor].transfer.as_ref().is_some_and(|template| {
                matches!(template.result, super::super::transfer::Value::Scalar(_))
            })
        })
    }

    pub(in super::super) fn checked_result(
        &self,
        owner: &super::super::heap::Owner,
        span: &Span,
    ) -> Result<(), VirErr> {
        let actors = owner
            .joined
            .as_ref()
            .ok_or_else(|| unsupported(span, "Result success without a checked worker outcome"))?;
        if actors.is_empty()
            || actors.iter().any(|actor| !self.growth.worker_executions.contains_key(actor))
        {
            return Err(unsupported(span, "Result success for a foreign worker actor"));
        }
        Ok(())
    }

    pub(in super::super) fn worker_result_predicate(
        &mut self,
        expr: &Expr,
    ) -> Result<bool, VirErr> {
        let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &expr.x else {
            return Ok(false);
        };
        if !matches!(
            attrs.resource_intrinsic,
            Some(ResourceIntrinsic::ResultIsOk | ResourceIntrinsic::ResultIsErr)
        ) {
            return Ok(false);
        }
        let [source] = args.as_slice() else {
            return Err(unsupported(&expr.span, "this Result predicate"));
        };
        let typ = super::super::paths::referent(&source.typ);
        self.layouts
            .result_payloads(typ)
            .ok_or_else(|| unsupported(&expr.span, "this Result predicate type"))?;
        let (name, path) = super::super::paths::expr(source, typ)
            .ok_or_else(|| unsupported(&expr.span, "Result predicate without an owned outcome"))?;
        let owner =
            self.heap.root(&name).and_then(|owner| owner.at(&path)).ok_or_else(|| {
                unsupported(&expr.span, "Result predicate without a live outcome")
            })?;
        self.checked_result(owner, &expr.span)?;
        self.discard(source)?;
        Ok(true)
    }
}
