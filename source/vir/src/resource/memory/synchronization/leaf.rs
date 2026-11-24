//! Closed inline workspace of verified synchronization helpers. A caller may
//! supply the result destination. Arguments are evaluated before the call.
use super::local::Boundary;
use crate::ast::*;
use crate::resource::memory::{
    analysis::{Analysis, FunctionAnalysis},
    contracts,
    footprint::{MemoryKind, MemorySelection},
    model::unsupported,
    transfer::checked,
};
use serde::{Deserialize, Serialize};
use vir_macros::ToDebugSNode;

/// Evidence for the specific function carrying this attribute. An executable
/// body contributes a measured workspace. A proof body is erased. In both cases
/// importers receive the certificate only after whole-crate verification and
/// lifetime checking. Keeping the existing fields preserves the export encoding.
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize, ToDebugSNode)]
pub struct CheckedBody {
    /// Largest charge at a point without an overlap with the returned value.
    before_result: u64,
    /// Largest charge at a point where the returned value already occupies storage.
    with_result: Option<u64>,
}

impl CheckedBody {
    /// A local population proof has no executable storage. Its resolved trait
    /// method and successful verification establish the fact on import.
    pub fn erased_proof() -> Self {
        Self::default()
    }

    pub(in crate::resource::memory) fn from_body(
        function: &Function,
        checked: &FunctionAnalysis,
    ) -> Result<Self, VirErr> {
        let fail = || {
            unsupported(&function.span, "publishing a non-local synchronization helper footprint")
        };
        let summary = checked.summary.as_ref().ok_or_else(fail)?;
        if checked.incomplete.is_some()
            || summary.transfer_required
            || !checked.effects.calls.is_empty()
            || !checked.growth.worker_executions.is_empty()
        {
            return Err(unsupported(
                &function.span,
                "an imported synchronization helper with ownership, worker, or helper-call effects",
            ));
        }
        let mut leaf = Self::default();
        for p in &summary.profiles {
            let total = contracts::constant(&p.cost.total()).ok_or_else(|| {
                unsupported(
                    &function.span,
                    "an imported synchronization helper with an unresolved symbolic cost",
                )
            })?;
            let heap =
                p.cost.select(&function.span, &MemorySelection::kind(MemoryKind::host_heap()));
            let local =
                p.cost.select(&function.span, &MemorySelection::kind(MemoryKind::host_local()));
            if contracts::constant(&heap) != Some(0)
                || contracts::constant(&local) != Some(total)
                || !p.condition.held.is_empty()
                || !matches!(p.condition.boundary, Boundary::Live)
            {
                return Err(fail());
            }
            if p.result {
                leaf.with_result = Some(leaf.with_result.unwrap_or(0).max(total));
            } else {
                leaf.before_result = leaf.before_result.max(total);
            }
        }
        Ok(leaf)
    }
}

impl Analysis<'_> {
    pub(in crate::resource::memory) fn imported_leaf_call(
        &mut self,
        value: &Expr,
        destination: bool,
    ) -> Result<Option<u64>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, target, types, impls, attrs),
            args,
            post_args: None,
            body: None,
        } = &value.x
        else {
            return Ok(None);
        };
        if attrs.resource_intrinsic == Some(ResourceIntrinsic::InvariantCredit) && args.is_empty() {
            self.transitions
                .operation(&value.span, checked::Operation::Evaluate { args: args.clone() });
            return Ok(Some(0));
        }
        let Some(leaf) = self.layouts.imported_leaves.get(target).copied() else { return Ok(None) };
        let inline_result = contracts::scalar(&value.typ)
            || super::super::model::unit(&value.typ)
            || super::super::construction::aggregate(&value.typ) && !self.layouts.owner(&value.typ);
        // A measured atomic wrapper constructor is uniform in its erased
        // invariant, tracked state and predicate. Its returned location has
        // the same concrete primitive layout at every instantiation.
        let erased_constructor = self.layouts.atomic_location(&value.typ).is_some();
        if ((!types.is_empty() || !impls.is_empty()) && !erased_constructor) || !inline_result {
            return Err(unsupported(
                &value.span,
                "an imported synchronization helper without a concrete inline result",
            ));
        }
        let mut operands = Vec::new();
        for arg in args.iter() {
            if self.layouts.owner(&arg.typ) {
                return Err(unsupported(
                    &arg.span,
                    "an owning argument to an inline synchronization helper",
                ));
            }
            operands.push(self.produce(arg)?);
            if !self.flow.reachable {
                return Ok(Some(0));
            }
        }
        for operand in operands {
            self.release_value(operand, &value.span);
        }
        let result = self.layouts.size(&value.typ, &value.span)?;
        let from_callee = if let Some(bytes) = leaf.with_result {
            if destination {
                bytes.checked_sub(result).ok_or_else(|| {
                    unsupported(&value.span, "a callee result larger than its measured footprint")
                })?
            } else {
                bytes
            }
        } else {
            0
        };
        let bytes = leaf.before_result.max(from_callee);
        let kind = MemoryKind::host_local();
        self.storage.reserve(&value.span, kind.clone(), bytes, "verified helper body")?;
        self.storage.release(&value.span, kind, bytes, "verified helper body");
        // The profile already included its output wherever the two overlapped.
        // Only the returned aggregate continues occupying a slot at the caller.
        if !destination && super::super::construction::aggregate(&value.typ) {
            self.produced = Some(self.fresh_value(&value.span, &value.typ)?);
        }
        self.transitions
            .operation(&value.span, checked::Operation::Evaluate { args: args.clone() });
        Ok(Some(0))
    }
}
