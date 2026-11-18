//! Caller-relative worker collections at synchronous function boundaries.

use super::super::{
    analysis::Analysis, heap::Owner, layout::Layouts, lifetime::Value, model::unsupported,
};
use crate::{ast::*, messages::Span};

impl Layouts {
    /// Select a by-value handle vector which is also the helper's result type.
    /// Other execution parameters supply scalar controls such as a stopping count.
    pub(in super::super) fn worker_parameter(&self, function: &Function) -> Option<usize> {
        let result = &function.x.outer_ret.x.typ;
        let TypX::Datatype(_, args, _) = &**result else { return None };
        if !self.vector(result) || self.join_handle(args.first()?).is_none() {
            return None;
        }
        let mut owners = function.x.params.iter().enumerate().filter(|(_, param)| {
            param.x.mode == Mode::Exec && !super::super::contracts::scalar(&param.x.typ)
        });
        let (index, parameter) = owners.next()?;
        (owners.next().is_none() && crate::ast_util::types_equal(&parameter.x.typ, result))
            .then_some(index)
    }
}

/// The local ownership interface can be composed within this crate. Exporting
/// a concurrent bound still requires the closed caller's global proof.
pub(in super::super) fn parameter_domain_error(span: &Span) -> VirErr {
    unsupported(span, "worker population helpers before global lifetime and interference proofs")
}

impl Analysis<'_> {
    pub(in super::super) fn check_worker_parameter_result(
        &self,
        span: &Span,
    ) -> Result<(), VirErr> {
        let Some((_, vector)) = self.transitions.worker_parameter else { return Ok(()) };
        if self.result_owner.as_ref().and_then(|owner| owner.vector) != Some(vector)
            || !self.transitions.forwards_worker_vector(|target| {
                self.summaries.get(target).is_some_and(|s| s.worker_parameter().is_some())
            })
        {
            return Err(unsupported(
                span,
                "a worker population helper must transfer its input vector with checked handle removals",
            ));
        }
        Ok(())
    }

    /// A vstd join with two inline outcomes can be discarded in either case.
    /// The selected input lifetime ends at join. No success assumption or
    /// fabricated publication is available inside a polymorphic helper.
    pub(super) fn join_parameter_handle(
        &mut self,
        source: &Expr,
        argument: &Expr,
        handle: Value,
        owner: Owner,
    ) -> Result<Value, VirErr> {
        let Some((success, failure)) = self.layouts.result_payloads(&source.typ) else {
            return Err(unsupported(&source.span, "a parameter join without a native result"));
        };
        if self.transitions.worker_parameter.is_none()
            || !(super::super::contracts::scalar(success) || super::super::model::unit(success))
            || !super::super::model::unit(failure)
        {
            return Err(unsupported(
                &source.span,
                "a parameter join with owned or unknown outcome storage",
            ));
        }
        let result = self.fresh_value(&source.span, &source.typ)?;
        self.release_owner(owner, &source.span);
        self.release_value(handle, &source.span);
        self.result_owner = Some(Owner::default());
        self.transitions.operation(
            &source.span,
            super::super::transfer::checked::Operation::ParameterJoin { source: argument.clone() },
        );
        Ok(result)
    }
}
