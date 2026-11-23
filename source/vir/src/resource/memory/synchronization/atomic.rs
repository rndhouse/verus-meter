//! Source operands and result storage of permissioned atomic operations.
use super::AtomicOperation;
use crate::ast::*;
use crate::resource::memory::{
    analysis::Analysis, footprint::MemoryKind, model::unsupported, transfer::checked,
};

impl Analysis<'_> {
    pub(in crate::resource::memory) fn atomic_call(
        &mut self,
        value: &Expr,
        destination: bool,
    ) -> Result<Option<u64>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attr),
            args,
            post_args: None,
            body: None,
        } = &value.x
        else {
            return Ok(None);
        };
        let Some(ResourceIntrinsic::Atomic(op)) = attr.resource_intrinsic else { return Ok(None) };
        let arity = match op {
            AtomicOperation::New => 1,
            AtomicOperation::Load => 2,
            AtomicOperation::Store
            | AtomicOperation::FetchAddWrapping
            | AtomicOperation::FetchSubWrapping => 3,
            AtomicOperation::CompareExchange | AtomicOperation::CompareExchangeWeak => 4,
        };
        if args.len() != arity {
            return Err(unsupported(&value.span, "an atomic call with an unknown argument layout"));
        }
        let mut operands = Vec::new();
        let mut arguments = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            // The permission is a tracked wrapper. A block or helper producing
            // that wrapper could still execute code, so only skip erased syntax.
            if op != AtomicOperation::New && i == 1 {
                if !matches!(arg.x, ExprX::Ghost { alloc_wrapper: true, tracked: true, .. }) {
                    return Err(unsupported(&arg.span, "a computed atomic permission argument"));
                }
                continue;
            }
            operands.push(self.produce(arg)?);
            arguments.push(arg.clone());
        }
        let bytes = if !destination && matches!(&*value.typ, TypX::Datatype(_, _, _)) {
            self.layouts.return_size(&value.typ, &value.span)?
        } else {
            0
        };
        self.storage.reserve(&value.span, MemoryKind::host_local(), bytes, "atomic result")?;
        for operand in operands {
            self.release_value(operand, &value.span);
        }
        self.transitions.operation(
            &value.span,
            checked::Operation::Evaluate { args: std::sync::Arc::new(arguments) },
        );
        Ok(Some(bytes))
    }
}
