//! Result destinations and Option control flow, without compiler temporary slots.
//!
//! A checked function budgets for its declared result. Calls share an existing
//! destination when available; otherwise the result remains live until consumed.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use super::model::{unit, unsupported};
use crate::ast::*;

impl Analysis<'_> {
    pub(super) fn value_into(&mut self, expr: &Expr) -> Result<bool, VirErr> {
        if self.option_operation(expr, true)?.is_some() {
            return Ok(true);
        }
        match &expr.x {
            ExprX::Block(stmts, tail) => {
                self.layouts.return_size(&expr.typ, &expr.span)?;
                self.block(expr, stmts, tail, !unit(&expr.typ))?;
            }
            ExprX::If(cond, yes, no) => {
                self.layouts.return_size(&expr.typ, &expr.span)?;
                self.conditional(expr, cond, yes, no.as_ref(), false)?;
            }
            ExprX::Match(scrutinee, arms, _) => self.option_match(expr, scrutinee, arms, false)?,
            _ => return Ok(false),
        }
        Ok(true)
    }

    pub(super) fn value_expr(&mut self, expr: &Expr) -> Result<Option<u64>, VirErr> {
        if let Some(result) = self.option_operation(expr, false)? {
            return Ok(Some(result));
        }
        if !unit(&expr.typ)
            && matches!(&expr.x, ExprX::Match(..) | ExprX::Block(..) | ExprX::If(..))
        {
            let value = self.produce(expr)?;
            return Ok(Some(self.expression_value(value, &expr.span)?));
        }
        Ok(None)
    }

    fn option_operation(&mut self, expr: &Expr, destination: bool) -> Result<Option<u64>, VirErr> {
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
            Some(
                ResourceIntrinsic::OptionIsSome
                    | ResourceIntrinsic::OptionIsNone
                    | ResourceIntrinsic::OptionUnwrap
            )
        ) {
            return Ok(None);
        }
        if args.len() != 1 {
            return Err(unsupported(&expr.span, "this Option operation"));
        }
        let typ = match &*args[0].typ {
            TypX::Decorate(TypDecoration::Ref, None, t) => t,
            _ => &args[0].typ,
        };
        self.layouts.option_payload(typ, &expr.span)?;
        self.layouts.size(typ, &expr.span)?;
        // Predicates and scalar extraction are intrinsic reads. An aggregate
        // extracted without a destination retains its own result storage.
        let bytes = if !destination && super::construction::aggregate(&expr.typ) {
            self.layouts.return_size(&expr.typ, &expr.span)?
        } else {
            0
        };
        self.storage.reserve(
            &expr.span,
            MemoryKind::host_local(),
            bytes,
            "Option payload result",
        )?;
        self.discard(&args[0])?;
        Ok(Some(bytes))
    }

    fn option_pattern(
        &mut self,
        pattern: &Pattern,
        typ: &Typ,
        slots: &mut Vec<(VarIdent, u64)>,
        mut owner: Option<super::heap::Owner>,
    ) -> Result<(), VirErr> {
        if !crate::ast_util::types_equal(&pattern.typ, typ) {
            return Err(unsupported(&pattern.span, "this Option pattern coercion"));
        }
        match &pattern.x {
            PatternX::Wildcard => {
                if let Some(owner) = owner {
                    self.release_owner(owner, &pattern.span);
                }
                Ok(())
            }
            PatternX::Var(binding) if matches!(binding.by_ref, ByRef::No) => {
                if self.var_modes.get(&binding.name) != Some(&Mode::Exec) {
                    return Err(unsupported(&pattern.span, "non-executable Option bindings"));
                }
                let bytes = self.layouts.return_size(&binding.typ, &pattern.span)?;
                slots.push((binding.name.clone(), bytes));
                if let Some(owner) = owner {
                    self.heap.owners.insert(binding.name.clone(), owner);
                }
                if binding.user_mut == Some(false) && super::contracts::scalar(&binding.typ) {
                    self.stable_scalars.insert(binding.name.clone());
                }
                Ok(())
            }
            PatternX::Constructor(name, variant, fields) if self.layouts.option(typ) => {
                let TypX::Datatype(actual, _, _) = &**typ else { unreachable!() };
                if name != actual {
                    return Err(unsupported(&pattern.span, "this Option pattern type"));
                }
                match (variant.as_str(), fields.as_slice()) {
                    ("None", []) => {
                        if let Some(owner) = owner {
                            self.release_owner(owner, &pattern.span);
                        }
                        Ok(())
                    }
                    ("Some", [field]) => {
                        let payload = self.layouts.option_payload(typ, &pattern.span)?.clone();
                        let child = owner.as_mut().and_then(|owner| {
                            owner.children.remove(&super::heap::OwnerSlot::Contents)
                        });
                        if let Some(owner) = owner {
                            self.release_owner(owner, &pattern.span);
                        }
                        self.option_pattern(&field.a, &payload, slots, child)
                    }
                    _ => Err(unsupported(&pattern.span, "this Option pattern")),
                }
            }
            _ => Err(unsupported(
                &pattern.span,
                "this Option pattern (use Some(value), None, or a wildcard)",
            )),
        }
    }

    pub(super) fn option_match(
        &mut self,
        expr: &Expr,
        scrutinee: &Place,
        arms: &Arms,
        new_value: bool,
    ) -> Result<(), VirErr> {
        if !self.layouts.option(&scrutinee.typ) {
            return Err(unsupported(&expr.span, "matches other than by-value Option matches"));
        }
        self.layouts.return_size(&expr.typ, &expr.span)?;
        if self.layouts.owner(&expr.typ) {
            return Err(unsupported(&expr.span, "conditional heap ownership results"));
        }
        let mut option_owner = None;
        let scratch = if let PlaceX::Temporary(value) = &scrutinee.x {
            let bytes = self.layouts.size(&scrutinee.typ, &scrutinee.span)?;
            self.storage.reserve(
                &value.span,
                MemoryKind::host_local(),
                bytes,
                "match input destination",
            )?;
            self.initialize_expr(value)?;
            option_owner = self.result_owner.take();
            bytes
        } else {
            self.access(scrutinee, &scrutinee.typ)?;
            if self.layouts.owner(&scrutinee.typ) {
                option_owner = Some(self.move_owner(scrutinee)?);
                let value = self.take_value(scrutinee)?;
                self.release_value(value, &expr.span);
            }
            0
        };
        let protection = self.heap.protect();
        let entry = self.branch_state();
        let mut joined = None;
        let mut result: Option<super::lifetime::Value> = None;
        for arm in arms.iter() {
            if !matches!(&arm.x.guard.x, ExprX::Const(Constant::Bool(true))) {
                return Err(unsupported(&arm.span, "Option match guards"));
            }
            self.restore_branch(&entry);
            let mut slots = Vec::new();
            self.option_pattern(&arm.x.pattern, &scrutinee.typ, &mut slots, option_owner.clone())?;
            // Bindings exist throughout the arm, including its guard/body.
            for (name, bytes) in &slots {
                let id = self.storage.reserve_value(
                    &arm.x.body.span,
                    MemoryKind::host_local(),
                    *bytes,
                )?;
                self.slots.insert(
                    name.clone(),
                    super::lifetime::Value {
                        bytes: *bytes,
                        ids: [id].into_iter().collect(),
                        origins: [id].into_iter().collect(),
                        parameter: None,
                    },
                );
            }
            if new_value {
                let value = self.produce(&arm.x.body)?;
                if let Some(result) = &mut result {
                    result.merge(&value);
                } else {
                    result = Some(value);
                }
            } else {
                self.initialize_expr(&arm.x.body)?;
            }
            for (name, _) in slots.iter().rev() {
                self.drop_owner(name, &arm.span)?;
                if let Some(value) = self.slots.remove(name) {
                    self.release_value(value, &arm.span);
                }
            }
            if let Some(joined) = &joined {
                self.join_branch(joined)?;
            }
            joined = Some(self.branch_state());
        }
        self.produced = result;
        self.storage.release(&expr.span, MemoryKind::host_local(), scratch, "match input consumed");
        self.heap.unprotect(protection);
        Ok(())
    }
}
