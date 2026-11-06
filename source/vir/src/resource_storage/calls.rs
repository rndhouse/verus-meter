//! Direct-call composition and compiler-identified resource intrinsics.

use super::analysis::Analysis;
use super::model::{eligible, slice, unit, unsupported};
use crate::ast::*;
use crate::messages::error;

impl Analysis<'_> {
    fn call(&mut self, expr: &Expr, target: &Fun, args: &Exprs) -> Result<u64, VirErr> {
        let callee = self.functions.get(target).ok_or_else(|| {
            unsupported(
                &expr.span,
                "calls outside this crate; imported storage summaries are not supported",
            )
        })?;
        let Some(&envelope) = self.budgets.get(target) else {
            return Err(unsupported(&expr.span, "calls without a current-model storage contract")
                .secondary_span(&callee.span));
        };
        eligible(callee)?;
        if args.len() != callee.x.params.len() || !unit(&expr.typ) {
            return Err(unsupported(&expr.span, "this call signature"));
        }
        // Unsupported selectors retain the envelope. Never re-read mutable
        // state or re-evaluate side effects in a generated pre-call assertion.
        let bound = super::contracts::instantiate(
            callee,
            args,
            &self.stable_scalars,
            self.budgets,
            self.functions,
            self.layouts,
            false,
        )
        .ok();
        let constant = bound.as_ref().and_then(super::contracts::constant);
        let budget = constant.unwrap_or(envelope);
        let caller_live = self.storage.live();
        let mut parameters = 0u64;
        for (arg, param) in args.iter().zip(callee.x.params.iter()) {
            if param.x.mode != Mode::Exec {
                continue;
            }
            if !crate::ast_util::types_equal(&arg.typ, &param.x.typ) {
                return Err(unsupported(&arg.span, "this call argument coercion"));
            }
            let bytes = self.layouts.size(&param.x.typ, &param.span)?;
            parameters = parameters
                .checked_add(bytes)
                .ok_or_else(|| unsupported(&expr.span, "parameter storage exceeding u64"))?;
            // Every argument initializes its parameter's storage. Earlier
            // parameters remain live during later argument evaluation.
            self.storage.reserve(&arg.span, bytes, "callee parameter slot")?;
            match &arg.x {
                ExprX::TwoPhaseBorrowMut(place) => {
                    self.borrow(place, &arg.typ)?;
                }
                _ => self.initialize_expr(arg)?,
            }
        }
        let additional = budget.checked_sub(parameters).ok_or_else(|| {
            error(&callee.span, "callee storage budget is smaller than its parameter storage")
        })?;
        // Parameters are already included in the callee's declared peak.
        if let Some(bound) = bound.filter(|_| constant.is_none()) {
            let cost = super::contracts::add(
                &expr.span,
                super::contracts::literal(&expr.span, caller_live),
                bound,
            );
            self.storage.reserve_call(&expr.span, additional, cost)?;
        } else {
            self.storage.reserve(
                &expr.span,
                additional,
                &format!("callee peak for {}", crate::ast_util::fun_as_friendly_rust_name(target)),
            )?;
        }
        self.storage.release(&expr.span, budget, "callee return");
        self.calls.push((target.clone(), expr.span.clone()));
        Ok(0)
    }

    pub(super) fn call_expr(&mut self, expr: &Expr) -> Result<u64, VirErr> {
        let operands;
        match &expr.x {
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
                args,
                post_args: None,
                body: None,
            } if attrs.resource_intrinsic == Some(ResourceIntrinsic::SliceLen)
                && args.len() == 1 =>
            {
                if !matches!(&*args[0].typ, TypX::Decorate(TypDecoration::Ref, None, inner) if slice(inner))
                {
                    return Err(unsupported(&expr.span, "length of this slice type"));
                }
                // Validate the receiver; length evaluation creates no source slot.
                operands = self.expr(&args[0])?;
            }
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
                args,
                post_args: None,
                body: None,
            } if attrs.resource_intrinsic == Some(ResourceIntrinsic::ArrayUnsize)
                && args.len() == 1 =>
            {
                // Shared unsizing may lower through a helper adapter that
                // borrows a temporary thin reference, producing &&[u32; N].
                // Admit only this exact, nonescaping adapter shape. Evaluate
                // the inner reference normally so borrowed backing temporaries
                // still fail. Compiler adapters do not create source storage.
                if let TypX::Decorate(TypDecoration::Ref, None, inner) = &*args[0].typ
                    && let TypX::Decorate(TypDecoration::Ref, None, array) = &**inner
                    && matches!(&**array, TypX::Primitive(Primitive::Array, _))
                    && matches!(&*expr.typ, TypX::Decorate(TypDecoration::Ref, None, to) if slice(to))
                    && let ExprX::ReadPlace(place, kind) = &args[0].x
                    && matches!(kind.preliminary_kind, ReadKind::ImmutBor)
                    && let PlaceX::Temporary(value) = &place.x
                    && crate::ast_util::types_equal(&value.typ, inner)
                {
                    self.layouts.size(array, &expr.span)?;
                    self.discard(value)?;
                    self.layouts.size(&expr.typ, &expr.span)?;
                    return Ok(0);
                }
                let (from, to) = match (&*args[0].typ, &*expr.typ) {
                    (TypX::MutRef(from), TypX::MutRef(to)) => (from, to),
                    (
                        TypX::Decorate(TypDecoration::Ref, None, from),
                        TypX::Decorate(TypDecoration::Ref, None, to),
                    ) => (from, to),
                    _ => return Err(unsupported(&expr.span, "this array-to-slice coercion")),
                };
                if !matches!(&**from, TypX::Primitive(Primitive::Array, _)) || !slice(to) {
                    return Err(unsupported(&expr.span, "this array-to-slice coercion"));
                }
                self.layouts.size(from, &expr.span)?;
                // Coercion uses the destination reference's storage. Backing
                // array storage stays with its original owner.
                operands = self.expr(&args[0])?;
            }
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, target, typs, impls, attrs),
                args,
                post_args: None,
                body: None,
            } if typs.is_empty() && impls.is_empty() && !attrs.const_var => {
                return self.call(expr, target, args);
            }
            _ => {
                return Err(unsupported(
                    &expr.span,
                    "calls with generic, dynamic, or unsupported targets",
                ));
            }
        }
        self.result(expr, operands)
    }
}
