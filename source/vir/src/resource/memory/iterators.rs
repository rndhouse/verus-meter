//! Explicit layouts and operation rules for finite scalar iterator state.
//!
//! Iterators have their own inline lifetime. Supported adapters retain that
//! state without owning allocations; unfamiliar and owning iterators reject.

use super::{analysis::Analysis, footprint::MemoryKind, model::unsupported};
use crate::ast::*;
use crate::messages::Span;

/// Compiler datatype identities, independent of aliases and source spellings.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Kind {
    /// A half-open native integer range, containing its two bounds.
    Range,
    /// A finite iterator visited from its last element to its first.
    Rev,
    /// An iterator with an additional remaining-item counter.
    Take,
    /// An iterator with an additional initial-skip counter.
    Skip,
    /// The native iterator plus Verus's erased snapshot, history, and index.
    Wrapper,
}

/// Match full compiler paths, including their distinguished standard crates.
/// Local types named Range or VerusForLoopWrapper cannot acquire these rules.
pub(super) fn kind(typ: &Typ) -> Option<Kind> {
    let TypX::Datatype(Dt::Path(path), _, _) = &**typ else { return None };
    let known = [
        (crate::path!(CrateId::Core => "ops", "range", "Range"), Kind::Range),
        (crate::path!(CrateId::Core => "iter", "adapters", "rev", "Rev"), Kind::Rev),
        (crate::path!(CrateId::Core => "iter", "adapters", "take", "Take"), Kind::Take),
        (crate::path!(CrateId::Core => "iter", "adapters", "skip", "Skip"), Kind::Skip),
        (crate::path!(CrateId::Vstd => "std_specs", "iter", "VerusForLoopWrapper"), Kind::Wrapper),
    ];
    known.into_iter().find_map(|(expected, kind)| (*path == expected).then_some(kind))
}

/// Model size excludes erased wrapper fields and includes every native adapter.
pub(super) fn size(typ: &Typ, span: &Span) -> Result<u64, VirErr> {
    let TypX::Datatype(_, args, _) = &**typ else { unreachable!() };
    let [inner] = args.as_slice() else {
        return Err(unsupported(span, "this iterator layout"));
    };
    let bytes = match kind(typ) {
        Some(Kind::Range) => super::model::integer_type_size(inner)
            .and_then(|bytes| bytes.checked_mul(2))
            .ok_or_else(|| unsupported(span, "ranges with non-native-integer elements"))?,
        Some(kind) => {
            let inner_kind = kind_of_source(inner, span)?;
            if inner_kind == Kind::Wrapper {
                return Err(unsupported(span, "adapters over for-loop wrappers"));
            }
            let base = size(inner, span)?;
            if matches!(kind, Kind::Take | Kind::Skip) {
                base.checked_add(super::model::WORD_BYTES)
                    .ok_or_else(|| unsupported(span, "iterator sizes exceeding u64"))?
            } else {
                base
            }
        }
        None => return Err(unsupported(span, "this iterator class")),
    };
    Ok(bytes)
}

fn kind_of_source(typ: &Typ, span: &Span) -> Result<Kind, VirErr> {
    kind(typ).ok_or_else(|| unsupported(span, "this iterator class or adapter"))
}

/// Macro arguments may have empty diagnostic-span blocks around their borrows.
/// Unwrap only these transparent forms while retaining ordinary evaluation.
pub(super) fn receiver(value: &Expr) -> Option<VarIdent> {
    if let ExprX::Block(statements, Some(tail)) = &value.x
        && statements.is_empty()
    {
        return receiver(tail);
    }
    let (name, path) = super::paths::expr(value, super::paths::referent(&value.typ))?;
    path.is_empty().then_some(name)
}

/// An accepted iterator operation, shared by accounting and symbolic evaluation.
#[derive(Clone)]
pub(super) enum Operation {
    /// The range's finite sequence of native integer values.
    Range {
        /// Named bounds in Rust's original field-initializer evaluation order.
        fields: Binders<Expr>,
    },
    /// A compiler-identified constructor, conversion, or adapter.
    Adapt {
        /// Compiler-identified conversion or adapter with its checked rule.
        kind: ResourceIntrinsic,
        /// Executable arguments, retained in their original evaluation order.
        args: Exprs,
    },
    /// One successful visit's advancement; exhaustion is checked by its loop.
    Advance {
        /// Exact native wrapper binding advanced by the checked operation.
        receiver: VarIdent,
    },
}

/// A finite affine sequence, separate from inline storage and heap ownership.
/// Adapter composition changes its selection without introducing allocations.
#[derive(Clone)]
pub(super) struct Sequence {
    /// First yielded integer before any successful advances.
    pub(super) first: Expr,
    /// Signed unit stride, reversed by the standard reverse adapter.
    pub(super) step: i128,
    /// Exact number of selected values, always nonnegative.
    pub(super) count: Expr,
    /// Successful advances already performed by the iterator wrapper.
    pub(super) position: Expr,
}

impl Analysis<'_> {
    /// Validate and charge a library operation instead of trusting its spelling
    /// or assuming a missing resource contract means it is free.
    pub(super) fn iterator_call(
        &mut self,
        expr: &Expr,
        destination: bool,
    ) -> Result<Option<u64>, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(_, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(None);
        };
        use ResourceIntrinsic::*;
        let Some(
            op @ (IteratorInto | IteratorWrap | IteratorNext | IteratorRev | IteratorTake
            | IteratorSkip),
        ) = attrs.resource_intrinsic
        else {
            return Ok(None);
        };
        let source = args.first().ok_or_else(|| unsupported(&expr.span, "this iterator call"))?;
        let source_type = super::paths::referent(&source.typ);
        let source_kind = kind_of_source(source_type, &expr.span)?;
        size(source_type, &expr.span)?;
        if op == IteratorNext {
            if source_kind != Kind::Wrapper || args.len() != 1 {
                return Err(unsupported(&expr.span, "this iterator advancement"));
            }
            let receiver = receiver(source)
                .ok_or_else(|| unsupported(&expr.span, "an indirect iterator receiver"))?;
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Iterator(Operation::Advance { receiver }),
            );
        } else {
            let expected = match op {
                IteratorInto => source_kind,
                IteratorWrap => Kind::Wrapper,
                IteratorRev => Kind::Rev,
                IteratorTake => Kind::Take,
                IteratorSkip => Kind::Skip,
                _ => unreachable!(),
            };
            if kind(&expr.typ) != Some(expected)
                || source_kind == Kind::Wrapper
                || args.len() != if matches!(op, IteratorTake | IteratorSkip) { 2 } else { 1 }
            {
                return Err(unsupported(&expr.span, "this iterator class or adapter"));
            }
            size(&expr.typ, &expr.span)?;
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Iterator(Operation::Adapt {
                    kind: op,
                    args: args.clone(),
                }),
            );
        }
        if !destination {
            let bytes = self.layouts.size(&expr.typ, &expr.span)?;
            self.storage.reserve(
                &expr.span,
                MemoryKind::host_local(),
                bytes,
                "iterator operation result",
            )?;
        }
        // Earlier arguments remain live while later arguments execute, including
        // calls with temporary heap storage. Release them only after evaluation.
        let mut values = Vec::new();
        for argument in args.iter() {
            values.push(self.produce(argument)?);
        }
        for (argument, value) in args.iter().zip(values) {
            self.release_value(value, &argument.span);
        }
        Ok(Some(0))
    }
}
