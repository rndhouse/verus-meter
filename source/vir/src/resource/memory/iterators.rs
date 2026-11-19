//! Explicit layouts and operation rules for finite iterator state.
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
    /// A standard shared slice iterator over storage owned elsewhere.
    Slice,
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
        (crate::path!(CrateId::Core => "slice", "iter", "Iter"), Kind::Slice),
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
        Some(Kind::Slice) => 2 * super::model::WORD_BYTES,
        Some(kind) => {
            let inner_kind = kind_of_source(inner, span)?;
            if inner_kind == Kind::Slice && kind != Kind::Wrapper {
                return Err(unsupported(span, "adapters over borrowed collection iterators"));
            }
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

/// Only the compiler-identified wrapper's transient next result may expose
/// a shared-reference Option to the memory checker.
pub(super) fn shared_next(value: &Expr) -> Option<&Typ> {
    let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } = &value.x else {
        return None;
    };
    let [source] = args.as_slice() else { return None };
    let source = super::paths::referent(&source.typ);
    if attrs.resource_intrinsic != Some(ResourceIntrinsic::IteratorNext)
        || kind(source) != Some(Kind::Wrapper)
    {
        return None;
    }
    let TypX::Datatype(_, types, _) = &**source else { return None };
    if kind(types.first()?) != Some(Kind::Slice) {
        return None;
    }
    let TypX::Datatype(_, types, _) = &*value.typ else { return None };
    let item = types.first()?;
    matches!(&**item, TypX::Decorate(TypDecoration::Ref, None, _)).then_some(item)
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
    /// Start a forward shared traversal of a collection.
    BorrowCollection {
        /// The source borrow is evaluated once, before the iterator begins.
        source: Expr,
        /// Vectors use their existing checked geometry; slices carry a length.
        vector: Option<super::transfer::checked::Place>,
    },
    /// One successful visit's advancement; exhaustion is checked by its loop.
    Advance {
        /// Exact native wrapper binding advanced by the checked operation.
        receiver: VarIdent,
    },
}

/// A finite traversal, separate from inline storage and heap ownership.
#[derive(Clone)]
pub(super) struct Sequence {
    /// How the next position determines the value yielded by the iterator.
    pub(super) items: Items,
    /// Exact number of selected values, always nonnegative.
    pub(super) count: Expr,
    /// Successful advances already performed by the iterator wrapper.
    pub(super) position: Expr,
}

/// The item value available to the memory trace.
#[derive(Clone)]
pub(super) enum Items {
    /// An integer range, with its initial value and signed unit stride.
    Range { first: Expr, step: i128 },
    /// References have inline storage, with their pointees remaining external
    /// to the iterator. Their executable values remain subject to Verus proof.
    Shared,
}

/// Observe a shared slice's length without evaluating an executable call.
pub(super) fn slice_length(span: &Span, value: Expr) -> Option<Expr> {
    let TypX::Decorate(TypDecoration::Ref, None, inner) = &*value.typ else { return None };
    if !super::model::slice(inner) {
        return None;
    }
    let slice = SpannedTyped::new(span, inner, value.x.clone());
    Some(SpannedTyped::new(
        span,
        &crate::ast_util::int_typ(),
        ExprX::Unary(UnaryOp::Length(ArrayKind::Slice), slice),
    ))
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
        if op == IteratorInto && kind(&expr.typ) == Some(Kind::Slice) {
            if args.len() != 1
                || !matches!(&*source.typ, TypX::Decorate(TypDecoration::Ref, None, _))
            {
                return Err(unsupported(&expr.span, "a non-shared slice iterator source"));
            }
            let source = match &source.x {
                ExprX::Block(statements, Some(tail)) if statements.is_empty() => tail,
                _ => source,
            };
            let vector = if self.layouts.vector(source_type) {
                self.layouts.vector_element(source_type, &source.span)?;
                let location = super::paths::expr(source, source_type).ok_or_else(|| {
                    unsupported(&source.span, "this borrowed vector iterator source")
                })?;
                Some(super::transfer::checked::Place {
                    source: source.clone(),
                    typ: source_type.clone(),
                    location,
                })
            } else {
                self.layouts.slice_element(source_type, &source.span)?;
                None
            };
            size(&expr.typ, &expr.span)?;
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Iterator(Operation::BorrowCollection {
                    source: source.clone(),
                    vector,
                }),
            );
        } else if op == IteratorNext {
            let source_kind = kind_of_source(source_type, &expr.span)?;
            size(source_type, &expr.span)?;
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
            let source_kind = kind_of_source(source_type, &expr.span)?;
            size(source_type, &expr.span)?;
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
