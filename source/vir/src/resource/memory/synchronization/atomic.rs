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
            target: CallTarget::Fun(CallTargetKind::Static, target, _, _, attr),
            args,
            post_args: None,
            body: None,
        } = &value.x
        else {
            return Ok(None);
        };
        match attr.resource_intrinsic {
            Some(ResourceIntrinsic::Atomic(op)) => {
                let arity = match op {
                    AtomicOperation::New => 1,
                    AtomicOperation::Load => 2,
                    AtomicOperation::Store
                    | AtomicOperation::FetchAddWrapping
                    | AtomicOperation::FetchSubWrapping => 3,
                    AtomicOperation::CompareExchange | AtomicOperation::CompareExchangeWeak => 4,
                };
                if args.len() != arity {
                    return Err(unsupported(
                        &value.span,
                        "an atomic call with an unknown argument layout",
                    ));
                }
            }
            _ if self.layouts.workspace.is_some()
                && self.layouts.workspace_primitives.contains(target) => {}
            _ => return Ok(None),
        }
        let mut operands = Vec::new();
        for arg in args.iter() {
            let value = if let ExprX::TwoPhaseBorrowMut(p) = &arg.x {
                self.borrow(p, &arg.typ)?;
                self.fresh_value(&arg.span, &arg.typ)?
            } else {
                self.produce(arg)?
            };
            operands.push(value);
            if !self.flow.reachable {
                return Ok(Some(0));
            }
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
        self.transitions
            .operation(&value.span, checked::Operation::Evaluate { args: args.clone() });
        Ok(Some(bytes))
    }
}
