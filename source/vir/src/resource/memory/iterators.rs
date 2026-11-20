//! Explicit layouts and operation rules for finite iterator state.
//!
//! Iterators have their own inline lifetime. Supported adapters retain that
//! state without owning allocations. The consuming vector iterator retains
//! the backing allocation and every child it has yet to yield.

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
    /// A consuming vector iterator with the original backing allocation.
    Vector,
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
        (crate::path!(CrateId::Alloc => "vec", "into_iter", "IntoIter"), Kind::Vector),
        (crate::path!(CrateId::Core => "iter", "adapters", "rev", "Rev"), Kind::Rev),
        (crate::path!(CrateId::Core => "iter", "adapters", "take", "Take"), Kind::Take),
        (crate::path!(CrateId::Core => "iter", "adapters", "skip", "Skip"), Kind::Skip),
        (crate::path!(CrateId::Vstd => "std_specs", "iter", "VerusForLoopWrapper"), Kind::Wrapper),
    ];
    known.into_iter().find_map(|(expected, kind)| (*path == expected).then_some(kind))
}

/// Model size excludes erased wrapper fields and includes every native adapter.
pub(super) fn size(
    layouts: &super::layout::Layouts,
    typ: &Typ,
    span: &Span,
) -> Result<u64, VirErr> {
    let TypX::Datatype(_, args, _) = &**typ else { unreachable!() };
    if kind(typ) == Some(Kind::Vector) {
        let [_, allocator] = args.as_slice() else {
            return Err(unsupported(span, "this consuming vector iterator layout"));
        };
        if !layouts.standard_allocator(allocator) {
            return Err(unsupported(span, "a consuming iterator with a custom allocator"));
        }
        // Retain the backing pointer and capacity alongside the live range.
        return Ok(4 * super::model::WORD_BYTES);
    }
    let [inner] = args.as_slice() else {
        return Err(unsupported(span, "this iterator layout"));
    };
    let bytes = match kind(typ) {
        Some(Kind::Range) => super::model::integer_type_size(inner)
            .and_then(|bytes| bytes.checked_mul(2))
            .ok_or_else(|| unsupported(span, "ranges with non-native-integer elements"))?,
        Some(Kind::Slice) => verus_meter_model::SLICE_ITERATOR_BYTES,
        Some(kind) => {
            let inner_kind = kind_of_source(inner, span)?;
            if matches!(inner_kind, Kind::Slice | Kind::Vector) && kind != Kind::Wrapper {
                return Err(unsupported(span, "adapters over collection iterators"));
            }
            if inner_kind == Kind::Wrapper {
                return Err(unsupported(span, "adapters over for-loop wrappers"));
            }
            let base = size(layouts, inner, span)?;
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

/// Size the live body state of the simple binding form `for item in source`.
/// Validate the reference and element with the same layouts used in traversal.
pub(super) fn for_loop_size(
    layouts: &super::layout::Layouts,
    typ: &Typ,
    span: &Span,
) -> Result<u64, VirErr> {
    if let TypX::Decorate(TypDecoration::Ref, None, collection) = &**typ {
        let is_slice = super::model::slice(collection);
        if is_slice || layouts.vector(collection) {
            layouts.ref_size(typ, span)?;
            return Ok(verus_meter_model::borrowed_for_loop_bytes(is_slice));
        }
    }
    Err(crate::messages::error(span, "for_loop_size requires a shared slice or vector reference"))
}

/// A native consuming iterator or the Verus wrapper that moves it into a loop.
pub(super) fn owns_vector_storage(typ: &Typ) -> bool {
    match kind(typ) {
        Some(Kind::Vector) => true,
        Some(Kind::Wrapper) => {
            let TypX::Datatype(_, types, _) = &**typ else { unreachable!() };
            types.first().is_some_and(|inner| kind(inner) == Some(Kind::Vector))
        }
        _ => false,
    }
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
    /// Transfer a vector's reserved storage to an iterator.
    ConsumeVector { source: Expr },
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
    /// An inline item or shared reference whose value is checked by Verus.
    Collection,
    /// Remaining children in reverse visit order so the next child is the tail.
    Owned(super::transfer::Node),
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
            size(self.layouts, &expr.typ, &expr.span)?;
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Iterator(Operation::BorrowCollection {
                    source: source.clone(),
                    vector,
                }),
            );
        } else if op == IteratorInto && self.layouts.vector(&source.typ) {
            if args.len() != 1 || kind(&expr.typ) != Some(Kind::Vector) {
                return Err(unsupported(&expr.span, "this consuming vector iterator"));
            }
            self.layouts.vector_element(&source.typ, &source.span)?;
            size(self.layouts, &expr.typ, &expr.span)?;
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Iterator(Operation::ConsumeVector {
                    source: source.clone(),
                }),
            );
        } else if op == IteratorNext {
            let source_kind = kind_of_source(source_type, &expr.span)?;
            size(self.layouts, source_type, &expr.span)?;
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
            size(self.layouts, source_type, &expr.span)?;
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
            size(self.layouts, &expr.typ, &expr.span)?;
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
        if op == IteratorNext && self.layouts.owner(&expr.typ) {
            self.result_owner = Some(self.extract_iterator_element(expr, source)?);
        }
        if owns_vector_storage(&expr.typ) {
            let mut owner = self.result_owner.take().ok_or_else(|| {
                unsupported(&expr.span, "consuming iterator without backing ownership")
            })?;
            self.freeze_owner_geometry(source, &mut owner);
            if op == IteratorInto
                && kind(&expr.typ) == Some(Kind::Vector)
                && self.layouts.vector(&source.typ)
                && let Some(id) = owner.vector
            {
                // Iterator advancement never resizes the backing allocation.
                // Freeze its tracked charge while it is still the vector's,
                // then keep the same allocation identity through cleanup.
                if let Some(elements) = &mut owner.elements {
                    if !elements.precise
                        || elements.view != super::metadata::View::Complete
                        || !elements.inputs.is_empty()
                        || elements.references != super::elements::References::None
                    {
                        return Err(unsupported(
                            &expr.span,
                            "consuming iterator without a complete element forest",
                        ));
                    }
                    // Visited children leave gaps at their old indices. No
                    // vector length or dense source view describes this forest.
                    elements.source = None;
                    for id in elements.states.values() {
                        self.growth.elements[*id].forget_length();
                    }
                }
                let backing = self.growth.vectors[id].backing.clone();
                let frozen = self.allocation_snapshot(&expr.span, backing.bytes);
                self.storage.set_allocation(backing.id, backing.kind, frozen.clone());
                owner.vector = None;
                owner.extent = Some(frozen);
            }
            self.result_owner = Some(owner);
        }
        Ok(Some(0))
    }

    /// Separate the yielded child from still-unvisited elements. The index
    /// comes from the actual wrapper head and never selects a child on exhaustion.
    fn extract_iterator_element(
        &mut self,
        expr: &Expr,
        source: &Expr,
    ) -> Result<super::heap::Owner, VirErr> {
        use super::metadata::expr as meta;
        let span = &expr.span;
        let Some((position, length)) = self.growth.iterator_heads.get(&span.id).cloned() else {
            return Err(unsupported(
                span,
                "owning iterator advancement outside a checked for loop",
            ));
        };
        let receiver = receiver(source)
            .ok_or_else(|| unsupported(span, "an indirect owning iterator receiver"))?;
        let elements =
            self.heap.owners.get(&receiver).and_then(|owner| owner.elements.clone()).ok_or_else(
                || unsupported(span, "an owning iterator without its remaining elements"),
            )?;
        let present = crate::ast_util::mk_ineq(span, &position, &length, InequalityOp::Lt);
        let index = super::growth::select(span, present.clone(), position, meta::integer(span, -1));
        let index = self.allocation_snapshot(span, index);
        let path = meta::push(span, meta::path(span, []), index);
        let partition =
            super::metadata::operations::detach(span, elements.records.clone(), path.clone());
        let selected = self.metadata_local(
            span,
            "iterator_item",
            super::transfer::choice(
                span,
                present.clone(),
                partition.selected,
                meta::empty(span, meta::record_type()),
            ),
        );
        self.metadata_partition(span, elements.records.clone(), path);
        let remaining = super::transfer::choice(
            span,
            present.clone(),
            partition.remaining,
            elements.records.clone(),
        );
        self.growth.before.entry(span.id).or_default().push(meta::assign(
            span,
            &elements.records,
            remaining,
        ));
        self.set_element_records(span, &elements, false);
        let typ = self.layouts.option_payload(&expr.typ, span)?.clone();
        let item = self.owner_from_metadata(span, &typ, selected, elements.view, false)?;
        let tag =
            super::growth::select(span, present, meta::integer(span, 1), meta::integer(span, 0));
        let tag = self.allocation_snapshot(span, tag);
        Ok(super::heap::Owner {
            geometry: Some(tag),
            children: [(super::heap::OwnerSlot::Contents, item)].into(),
            ..Default::default()
        })
    }
}
