//! Concrete layouts. Structs are sums of executable fields, without ABI padding.

use super::model::{WORD_BYTES, integer_size, integer_type_size, slice, unsupported};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

/// Datatype and compiler closure identities occupy separate recursion domains.
#[derive(PartialEq, Eq, Hash)]
enum LayoutNode {
    Datatype(Dt),
    Closure(usize),
}

struct ClosureLayout {
    /// Copy in the original checked program is a sufficient, but not necessary,
    /// condition after proof-only captures disappear.
    source_copy: bool,
    fields: Vec<(Typ, super::concurrency::CaptureMode)>,
}

/// Storage within one allocation. Element storage includes inline fields/handles;
/// allocations owned by those elements require separate ownership accounting.
pub(super) enum AllocationLayout {
    /// One statically sized payload, in model bytes.
    Fixed(u64),
    /// Contiguous inline elements; the operation supplies length or capacity.
    Sequence { element: u64 },
}

pub(super) struct Layouts {
    datatypes: HashMap<Dt, Datatype>,
    global_allocator: Option<Dt>,
    vector: Option<Dt>,
    option: Option<Dt>,
    field_slots: HashMap<Ident, i128>,
    synchronization_types: super::synchronization::LibraryTypes,
    /// Only actual executable capture types contribute to closure storage.
    closures: std::collections::BTreeMap<usize, ClosureLayout>,
}

impl Layouts {
    /// Whether a node's logical cardinality participates in owning transfers.
    pub(super) fn cardinality(&self, typ: &Typ) -> bool {
        self.vector(typ)
            || self.option(typ)
            || matches!(&**typ,
            TypX::Decorate(TypDecoration::Box, _, inner) if matches!(&**inner, TypX::Primitive(Primitive::Slice, _)))
    }
    pub(super) fn new(
        datatypes: &[Datatype],
        global_allocator: Option<Dt>,
        vector: Option<Dt>,
        option: Option<Dt>,
    ) -> Self {
        let fields: std::collections::BTreeSet<_> = datatypes
            .iter()
            .flat_map(|d| d.x.variants.iter().flat_map(|v| v.fields.iter().map(|f| f.name.clone())))
            .collect();
        let field_slots =
            fields.into_iter().enumerate().map(|(i, name)| (name, -2 - i as i128)).collect();
        Self {
            datatypes: datatypes.iter().map(|d| (d.x.name.clone(), d.clone())).collect(),
            global_allocator,
            vector,
            option,
            field_slots,
            synchronization_types: HashMap::new(),
            closures: Default::default(),
        }
    }

    /// Install compiler-supplied identities instead of guessing by source names.
    pub(super) fn with_synchronization_types(
        mut self,
        types: &super::synchronization::LibraryTypes,
    ) -> Self {
        self.synchronization_types = types.clone();
        self
    }

    pub(super) fn metadata_slot(&self, slot: &super::heap::OwnerSlot) -> i128 {
        match slot {
            super::heap::OwnerSlot::Contents => -1,
            super::heap::OwnerSlot::Field(name) => self.field_slots[name],
            super::heap::OwnerSlot::Capture(index) => {
                -2 - self.field_slots.len() as i128 - *index as i128
            }
            super::heap::OwnerSlot::Element(_) => unreachable!("runtime indices are expressions"),
        }
    }

    /// Capture layouts arrive after Verus mode checking. No lifetime-check-only
    /// field may be substituted for this compiler-owned runtime information.
    pub(super) fn with_closures(mut self, evidence: &super::concurrency::Evidence) -> Self {
        self.closures = evidence
            .closures
            .iter()
            .map(|(id, closure)| {
                (
                    *id,
                    ClosureLayout {
                        source_copy: closure.copy,
                        fields: closure
                            .captures
                            .iter()
                            .map(|capture| (capture.typ.clone(), capture.mode))
                            .collect(),
                    },
                )
            })
            .collect();
        self
    }

    /// Rust implements Copy for a closure whose executable fields are all Copy.
    /// A tracked non-Copy capture can disappear during erasure; retaining the
    /// pre-erasure move decision would then lose a live source/argument copy.
    pub(super) fn copy_closure(&self, typ: &Typ) -> bool {
        fn copy(
            layouts: &Layouts,
            id: usize,
            visiting: &mut std::collections::BTreeSet<usize>,
        ) -> bool {
            let Some(layout) = layouts.closures.get(&id) else { return false };
            if layout.source_copy {
                return true;
            }
            if !visiting.insert(id) {
                return false;
            }
            let result = layout.fields.iter().all(|(typ, mode)| {
                *mode == super::concurrency::CaptureMode::Copy
                    || matches!(&**typ, TypX::AnonymousClosure(_, _, _, inner) if copy(layouts, *inner, visiting))
            });
            visiting.remove(&id);
            result
        }
        let TypX::AnonymousClosure(_, _, _, id) = &**typ else { return false };
        copy(self, *id, &mut Default::default())
    }

    pub(super) fn vector(&self, typ: &Typ) -> bool {
        matches!(&**typ, TypX::Datatype(name, _, _) if Some(name) == self.vector.as_ref())
    }

    pub(super) fn synchronization_parameter(
        &self,
        typ: &Typ,
    ) -> Option<super::synchronization::parameters::Parameter> {
        super::synchronization::parameters::parameter_type(typ, &self.synchronization_types)
    }

    pub(super) fn synchronization_result(&self, typ: &Typ) -> bool {
        super::synchronization::parameters::result_payload(typ, &self.synchronization_types)
            .is_some()
    }

    /// A borrowed native guard provides access to a separately owned mutex payload.
    pub(super) fn mutable_guard_payload<'t>(&self, typ: &'t Typ) -> Option<&'t Typ> {
        let TypX::MutRef(inner) = &**typ else { return None };
        let TypX::Datatype(name, args, _) = &**inner else { return None };
        (self.synchronization_types.get(name)
            == Some(&super::synchronization::LibraryType::MutexGuard))
        .then(|| args.first())
        .flatten()
    }

    pub(super) fn borrowed_owner<'t>(&self, typ: &'t Typ) -> Option<&'t Typ> {
        let inner = super::paths::referent(typ);
        (matches!(&**typ, TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, None, _))
            && (!super::synchronization::parameters::borrowed_view(
                typ,
                &self.synchronization_types,
            ) || self
                .mutex_payload(inner)
                .or_else(|| self.mutable_guard_payload(typ))
                .is_some_and(|payload| self.owner(payload)))
            && self.owner(inner))
        .then_some(inner)
    }

    /// Ownership templates for a mutable guard borrow describe the native
    /// mutex tree the guard grants access to. The guard's runtime layout and
    /// destructor remain independent of that tree.
    pub(super) fn borrowed_descriptor(&self, typ: &Typ) -> Option<Typ> {
        let inner = self.borrowed_owner(typ)?;
        if let Some(payload) = self.mutable_guard_payload(typ) {
            let mutex = self.synchronization_types.iter().find_map(|(name, kind)| {
                (*kind == super::synchronization::LibraryType::Mutex).then_some(name)
            })?;
            return Some(std::sync::Arc::new(TypX::Datatype(
                mutex.clone(),
                std::sync::Arc::new(vec![payload.clone()]),
                std::sync::Arc::default(),
            )));
        }
        Some(inner.clone())
    }

    /// Resolved handle payload and whether this is the native standard API.
    pub(super) fn join_handle<'t>(&self, typ: &'t Typ) -> Option<(&'t Typ, bool)> {
        use super::synchronization::LibraryType;
        let TypX::Datatype(name, args, _) = &**typ else { return None };
        let native = match self.synchronization_types.get(name)? {
            LibraryType::StdJoinHandle => true,
            LibraryType::VstdJoinHandle => false,
            _ => return None,
        };
        (args.len() == 1).then(|| (&args[0], native))
    }

    pub(super) fn option(&self, typ: &Typ) -> bool {
        matches!(&**typ, TypX::Datatype(name, _, _) if Some(name) == self.option.as_ref())
    }

    /// The native mutex stores its payload inline. Owning descendants remain
    /// under Contents when the mutex moves or enters a shared allocation.
    pub(super) fn mutex_payload<'t>(&self, typ: &'t Typ) -> Option<&'t Typ> {
        let TypX::Datatype(name, args, _) = &**typ else { return None };
        if self.synchronization_types.get(name) == Some(&super::synchronization::LibraryType::Mutex)
            && let [payload] = args.as_slice()
        {
            Some(payload)
        } else {
            None
        }
    }

    /// Guards and acquiring poison errors own the release effect, while the
    /// protected payload remains in the mutex's persistent allocation tree.
    pub(super) fn guard_owner(&self, typ: &Typ) -> bool {
        use super::synchronization::LibraryType;
        let TypX::Datatype(name, args, _) = &**typ else { return false };
        match self.synchronization_types.get(name) {
            Some(LibraryType::MutexGuard) => true,
            Some(LibraryType::PoisonError | LibraryType::TryLockError) => {
                args.first().is_some_and(|typ| self.guard_owner(typ))
            }
            _ => false,
        }
    }

    /// Only the compiler-identified standard Result carries primitive outcomes.
    pub(super) fn result_payloads<'t>(&self, typ: &'t Typ) -> Option<(&'t Typ, &'t Typ)> {
        let TypX::Datatype(name, args, _) = &**typ else { return None };
        (self.synchronization_types.get(name) == Some(&super::synchronization::LibraryType::Result)
            && args.len() == 2)
            .then(|| (&args[0], &args[1]))
    }

    pub(super) fn option_payload<'a>(&self, typ: &'a Typ, span: &Span) -> Result<&'a Typ, VirErr> {
        let TypX::Datatype(_, args, _) = &**typ else {
            return Err(unsupported(span, "this Option type"));
        };
        if !self.option(typ) || args.len() != 1 {
            return Err(unsupported(span, "this Option type"));
        }
        if matches!(&*args[0], TypX::MutRef(_))
            || matches!(&*args[0], TypX::Decorate(d, _, _) if !matches!(d, TypDecoration::Box | TypDecoration::Arc))
        {
            return Err(unsupported(span, "reference-valued Option payloads"));
        }
        Ok(&args[0])
    }

    pub(super) fn return_size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        if super::iterators::owns_vector_storage(typ) {
            return Err(unsupported(span, "returning a consuming iterator"));
        }
        if !self.owner(typ) && matches!(&**typ, TypX::Decorate(..) | TypX::MutRef(_)) {
            return Err(unsupported(span, "reference return values"));
        }
        self.size(typ, span)
    }

    pub(super) fn owner(&self, typ: &Typ) -> bool {
        self.owner_inner(typ, &mut HashSet::new())
    }

    fn owner_inner(&self, typ: &Typ, visiting: &mut HashSet<Dt>) -> bool {
        if self.guard_owner(typ)
            || self.mutex_payload(typ).is_some()
            || self.result_payloads(typ).is_some()
        {
            return true;
        }
        if self.join_handle(typ).is_some() || super::iterators::owns_vector_storage(typ) {
            return true;
        }
        if super::heap::boxed(typ)
            || self.vector(typ)
            || matches!(&**typ, TypX::Decorate(TypDecoration::Arc, _, _))
        {
            return true;
        }
        if let TypX::AnonymousClosure(_, _, _, id) = &**typ {
            return self.closures.contains_key(id) && !self.copy_closure(typ);
        }
        if self.option(typ) {
            let TypX::Datatype(_, args, _) = &**typ else { unreachable!() };
            return args.first().is_some_and(|typ| self.owner_inner(typ, visiting));
        }
        let TypX::Datatype(name, _, _) = &**typ else { return false };
        let Some(datatype) = self.datatypes.get(name) else { return false };
        if !datatype.x.is_struct || !visiting.insert(name.clone()) {
            return false;
        }
        let owns = datatype
            .x
            .variants
            .iter()
            .any(|v| v.fields.iter().any(|f| self.owner_inner(&f.a.0, visiting)));
        visiting.remove(name);
        owns
    }

    pub(super) fn vector_element(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        let TypX::Datatype(_, args, _) = &**typ else {
            return Err(unsupported(span, "this vector type"));
        };
        if !self.vector(typ) || args.len() != 2 || !self.standard_allocator(&args[1]) {
            return Err(unsupported(span, "vectors with custom allocator types"));
        }
        self.element_size(&args[0], span, &mut HashSet::new())
    }

    /// Runtime sequences expose element shape separately from fixed child paths.
    pub(super) fn owning_elements(&self, typ: &Typ) -> bool {
        if self.vector(typ) {
            let TypX::Datatype(_, args, _) = &**typ else { unreachable!() };
            args.first().is_some_and(|typ| self.owner(typ))
        } else if let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            matches!(&**inner, TypX::Primitive(Primitive::Slice, args) if args.first().is_some_and(|typ| self.owner(typ)))
        } else {
            false
        }
    }

    /// Detect identity-bearing ownership even when the local charge view is
    /// empty. Recursion revisits add no new field types to this reachability
    /// query; validating the executable layout remains the sizing pass's job.
    pub(super) fn contains_references(&self, typ: &Typ) -> bool {
        self.contains_identity(typ, false)
    }

    /// A plain memory forest cannot export a nested guard destructor, mutex
    /// identity, consuming iterator, or executable closure to another holder.
    pub(super) fn plain_protected_payload(&self, typ: &Typ) -> bool {
        !self.contains_identity(typ, true)
    }

    fn contains_identity(&self, typ: &Typ, protected: bool) -> bool {
        fn visit(
            layouts: &Layouts,
            typ: &Typ,
            protected: bool,
            visiting: &mut Vec<LayoutNode>,
        ) -> bool {
            if protected
                && (layouts.guard_owner(typ)
                    || layouts.mutex_payload(typ).is_some()
                    || super::iterators::owns_vector_storage(typ)
                    || matches!(&**typ, TypX::AnonymousClosure(..)))
            {
                return true;
            }
            if matches!(&**typ, TypX::Decorate(TypDecoration::Arc, _, _))
                || layouts.join_handle(typ).is_some()
                || layouts.result_payloads(typ).is_some()
            {
                return true;
            }
            // Generic containers can nest the same constructor at different
            // types. Inspect their actual arguments before the datatype-only
            // recursion guard (Vec<Vec<Arc<T>>> is not a recursive type).
            if let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
                return visit(layouts, inner, protected, visiting);
            }
            if let TypX::Datatype(_, args, _) | TypX::Primitive(_, args) = &**typ {
                for argument in args.iter() {
                    if visit(layouts, argument, protected, visiting) {
                        return true;
                    }
                }
            }
            if layouts.vector(typ) || layouts.option(typ) {
                return false;
            }
            let (key, children): (_, Vec<Typ>) = match &**typ {
                TypX::Datatype(name, _, _) => (
                    LayoutNode::Datatype(name.clone()),
                    layouts
                        .datatypes
                        .get(name)
                        .into_iter()
                        .flat_map(|datatype| datatype.x.variants.iter())
                        .flat_map(|variant| variant.fields.iter())
                        .filter(|field| field.a.1 == Mode::Exec)
                        .map(|field| field.a.0.clone())
                        .collect(),
                ),
                TypX::AnonymousClosure(_, _, _, id) => (
                    LayoutNode::Closure(*id),
                    layouts
                        .closures
                        .get(id)
                        .into_iter()
                        .flat_map(|layout| layout.fields.iter())
                        .map(|(typ, _)| typ.clone())
                        .collect(),
                ),
                _ => return false,
            };
            if visiting.contains(&key) {
                return false;
            }
            visiting.push(key);
            let mut found = false;
            for child in children {
                found |= visit(layouts, &child, protected, visiting);
            }
            visiting.pop();
            found
        }
        visit(self, typ, protected, &mut Vec::new())
    }

    fn element_size(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<LayoutNode>,
    ) -> Result<u64, VirErr> {
        if matches!(&**typ, TypX::MutRef(_))
            || matches!(&**typ, TypX::Decorate(d, _, _) if !matches!(d, TypDecoration::Box | TypDecoration::Arc))
        {
            return Err(unsupported(span, "reference-valued collection elements"));
        }
        self.size_inner(typ, span, visiting)
    }

    /// Child owners occupy inline storage already counted by the containing value.
    pub(super) fn owned_children(
        &self,
        typ: &Typ,
        span: &Span,
    ) -> Result<std::collections::BTreeMap<super::heap::OwnerSlot, Typ>, VirErr> {
        use super::heap::OwnerSlot;
        let mut children = std::collections::BTreeMap::new();
        if super::iterators::owns_vector_storage(typ) {
            return Ok(children);
        }
        if let Some((success, _)) = self.result_payloads(typ) {
            // Executable Result ownership requires a checked join-success
            // witness. Unknown outcomes are rejected at inputs/construction;
            // sizing alone never permits dropping an unmodeled Err payload.
            if self.owner(success) {
                children.insert(OwnerSlot::Contents, success.clone());
            }
            return Ok(children);
        }
        if self.guard_owner(typ) || self.join_handle(typ).is_some() {
            return Ok(children);
        }
        if let TypX::AnonymousClosure(_, _, _, id) = &**typ {
            let layout = self.closures.get(id).ok_or_else(|| {
                unsupported(span, "a closure without executable capture layout information")
            })?;
            for (index, (typ, _)) in layout.fields.iter().enumerate() {
                if self.owner(typ) {
                    children.insert(OwnerSlot::Capture(index), typ.clone());
                }
            }
            return Ok(children);
        }
        if matches!(&**typ, TypX::Decorate(TypDecoration::Arc, _, _)) {
            // Payload ownership is canonical in Heap::shared, not duplicated
            // beneath each strong handle's structural path.
            return Ok(children);
        }
        if let Some(payload) = self.mutex_payload(typ) {
            if self.owner(payload) {
                children.insert(OwnerSlot::Contents, payload.clone());
            }
        } else if self.option(typ) {
            let payload = self.option_payload(typ, span)?;
            if self.owner(payload) {
                children.insert(OwnerSlot::Contents, payload.clone());
            }
        } else if let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
            if self.owner(inner) {
                children.insert(OwnerSlot::Contents, inner.clone());
            }
        } else if self.owner(typ) && !self.vector(typ) {
            for field in self.struct_variant(typ, span)?.fields.iter() {
                if self.owner(&field.a.0) {
                    children.insert(OwnerSlot::Field(field.name.clone()), field.a.0.clone());
                }
            }
        }
        Ok(children)
    }

    pub(super) fn standard_allocator(&self, typ: &Typ) -> bool {
        match &**typ {
            TypX::Primitive(Primitive::Global, _) => true,
            TypX::Datatype(name, args, _) => {
                args.is_empty() && Some(name) == self.global_allocator.as_ref()
            }
            _ => false,
        }
    }

    /// Metadata checks shared by sizing, construction, and field projection.
    /// Field layout validation is performed by `size` before using the variant.
    pub(super) fn struct_variant(&self, typ: &Typ, span: &Span) -> Result<&Variant, VirErr> {
        let TypX::Datatype(name @ Dt::Path(_), args, _) = &**typ else {
            return Err(unsupported(span, "this struct type"));
        };
        let datatype = self
            .datatypes
            .get(name)
            .ok_or_else(|| unsupported(span, "struct layouts outside this crate"))?;
        let d = &datatype.x;
        if !d.is_struct || d.variants.len() != 1 {
            return Err(unsupported(span, "enum or union layouts"));
        }
        if d.destructor {
            return Err(unsupported(span, "structs with destructors"));
        }
        if !args.is_empty() || !d.typ_params.is_empty() || !d.typ_bounds.is_empty() {
            return Err(unsupported(span, "generic struct layouts"));
        }
        if d.proxy.is_some()
            || !matches!(d.transparency, DatatypeTransparency::WhenVisible(_))
            || d.mode != Mode::Exec
            || d.user_defined_invariant_fn.is_some()
        {
            return Err(unsupported(span, "opaque, proxy, ghost, or invariant-bearing structs"));
        }
        Ok(&d.variants[0])
    }

    pub(super) fn size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        self.size_inner(typ, span, &mut HashSet::new())
    }

    /// Select the existing inline layout for a reference, excluding borrowed data.
    pub(super) fn ref_size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        if !matches!(&**typ, TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, None, _)) {
            return Err(crate::messages::error(
                span,
                "ref_size requires a reference type or binding",
            ));
        }
        self.size(typ, span)
    }

    /// Select the existing inline layout for a non-reference value. Allocations
    /// behind owning handles remain separate charges in the accounting model.
    pub(super) fn value_size(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        if matches!(&**typ, TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, None, _)) {
            return Err(crate::messages::error(
                span,
                "value_size requires a non-reference type or binding; use ref_size for references",
            ));
        }
        self.size(typ, span)
    }

    /// A box owns a fixed value or a runtime-length sequence of supported values.
    /// Its handle and heap object are sized separately so moves do not duplicate
    /// the allocation and borrows keep backing storage charged to its owner.
    pub(super) fn box_layout(
        &self,
        typ: &Typ,
        span: &Span,
    ) -> Result<Option<AllocationLayout>, VirErr> {
        self.box_layout_inner(typ, span, &mut HashSet::new())
    }

    fn box_layout_inner(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<LayoutNode>,
    ) -> Result<Option<AllocationLayout>, VirErr> {
        let TypX::Decorate(TypDecoration::Box, allocator, inner) = &**typ else {
            return Ok(None);
        };
        if !allocator.as_ref().is_some_and(|a| match &*a.allocator_typ {
            TypX::Primitive(Primitive::Global, _) => true,
            TypX::Datatype(name, args, _) => {
                args.is_empty() && Some(name) == self.global_allocator.as_ref()
            }
            _ => false,
        }) {
            return Err(unsupported(span, "boxes with custom allocator types"));
        }
        if matches!(&**inner, TypX::MutRef(_))
            || matches!(&**inner, TypX::Decorate(d, _, _) if !matches!(d, TypDecoration::Box | TypDecoration::Arc))
        {
            return Err(unsupported(span, "reference-valued heap objects"));
        }
        Ok(Some(if slice(inner) {
            AllocationLayout::Sequence { element: self.slice_element_inner(inner, span, visiting)? }
        } else {
            AllocationLayout::Fixed(self.size_inner(inner, span, visiting)?)
        }))
    }

    pub(super) fn slice_element(&self, typ: &Typ, span: &Span) -> Result<u64, VirErr> {
        self.slice_element_inner(typ, span, &mut HashSet::new())
    }

    fn slice_element_inner(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<LayoutNode>,
    ) -> Result<u64, VirErr> {
        let TypX::Primitive(Primitive::Slice, args) = &**typ else {
            return Err(unsupported(span, "this slice type"));
        };
        if args.len() != 1 {
            return Err(unsupported(span, "this slice type"));
        }
        self.element_size(&args[0], span, visiting)
    }

    fn size_inner(
        &self,
        typ: &Typ,
        span: &Span,
        visiting: &mut HashSet<LayoutNode>,
    ) -> Result<u64, VirErr> {
        if let TypX::Datatype(name, args, _) = &**typ
            && let Some(kind) = self.synchronization_types.get(name)
        {
            use super::synchronization::LibraryType;
            let size = |index: usize, visiting: &mut HashSet<LayoutNode>| {
                let typ =
                    args.get(index).ok_or_else(|| unsupported(span, "this primitive layout"))?;
                self.size_inner(typ, span, visiting)
            };
            let bytes = match kind {
                LibraryType::Mutex => verus_meter_model::mutex_bytes(size(0, visiting)?),
                LibraryType::MutexGuard => {
                    size(0, visiting)?;
                    Some(verus_meter_model::reference_bytes(false))
                }
                LibraryType::PoisonError => Some(size(0, visiting)?),
                LibraryType::TryLockError => verus_meter_model::result_bytes(size(0, visiting)?, 0),
                LibraryType::Result => {
                    verus_meter_model::result_bytes(size(0, visiting)?, size(1, visiting)?)
                }
                LibraryType::StdJoinHandle | LibraryType::VstdJoinHandle => {
                    size(0, visiting)?;
                    Some(WORD_BYTES)
                }
            };
            return bytes.ok_or_else(|| unsupported(span, "primitive sizes exceeding u64"));
        }
        match &**typ {
            TypX::AnonymousClosure(_, _, _, id) => {
                let layout = self.closures.get(id).ok_or_else(|| {
                    unsupported(span, "a closure without executable capture layout information")
                })?;
                if !visiting.insert(LayoutNode::Closure(*id)) {
                    return Err(unsupported(span, "recursive executable closure layouts"));
                }
                let bytes = layout.fields.iter().try_fold(0u64, |bytes, (field, _)| {
                    bytes
                        .checked_add(self.size_inner(field, span, visiting)?)
                        .ok_or_else(|| unsupported(span, "closure storage exceeding u64"))
                })?;
                visiting.remove(&LayoutNode::Closure(*id));
                Ok(bytes)
            }
            TypX::Decorate(TypDecoration::Ghost | TypDecoration::Tracked, _, _) => Ok(0),
            TypX::Decorate(TypDecoration::Box, allocator, inner)
                if matches!(&**inner, TypX::Primitive(Primitive::ThreadPanicPayload, _)) =>
            {
                if !allocator.as_ref().is_some_and(|a| self.standard_allocator(&a.allocator_typ)) {
                    return Err(unsupported(span, "boxed trait objects with custom allocators"));
                }
                // Inline sizing is sufficient for the native join Result. The
                // allocation layout still rejects opaque pointees; this cannot
                // establish a bound on a panic payload or enable its recovery.
                Ok(2 * WORD_BYTES)
            }
            TypX::Decorate(TypDecoration::Arc, allocator, payload) => {
                if !allocator.as_ref().is_some_and(|a| self.standard_allocator(&a.allocator_typ)) {
                    return Err(unsupported(span, "shared owners with custom allocators"));
                }
                self.size_inner(payload, span, visiting)?;
                Ok(WORD_BYTES)
            }
            _ if super::iterators::kind(typ).is_some() => super::iterators::size(self, typ, span),
            _ if self.option(typ) => {
                let payload = self.option_payload(typ, span)?;
                self.size_inner(payload, span, visiting)?
                    .checked_add(1)
                    .ok_or_else(|| unsupported(span, "Option sizes exceeding u64"))
            }
            _ if self.vector(typ) => {
                let TypX::Datatype(_, args, _) = &**typ else { unreachable!() };
                if args.len() != 2 || !self.standard_allocator(&args[1]) {
                    return Err(unsupported(span, "vectors with custom allocator types"));
                }
                self.element_size(&args[0], span, visiting)?;
                Ok(3 * WORD_BYTES)
            }
            TypX::Decorate(TypDecoration::Box, _, _) => {
                match self.box_layout_inner(typ, span, visiting)?.unwrap() {
                    AllocationLayout::Fixed(_) => Ok(WORD_BYTES),
                    AllocationLayout::Sequence { .. } => Ok(2 * WORD_BYTES),
                }
            }
            TypX::Bool => Ok(verus_meter_model::BOOL_BYTES),
            TypX::Int(range) if integer_size(range).is_some() => Ok(integer_size(range).unwrap()),
            TypX::MutRef(inner) | TypX::Decorate(TypDecoration::Ref, None, inner) => {
                if slice(inner) {
                    self.slice_element(inner, span)?;
                    Ok(verus_meter_model::reference_bytes(true))
                } else if matches!(
                    &**inner,
                    TypX::MutRef(_) | TypX::Decorate(TypDecoration::Ref, ..)
                ) {
                    Err(unsupported(span, "nested references"))
                } else {
                    self.size_inner(inner, span, visiting)?;
                    Ok(verus_meter_model::reference_bytes(false))
                }
            }
            TypX::Datatype(Dt::Tuple(0), _, _) => Ok(0),
            TypX::Datatype(name @ Dt::Path(_), _, _) => {
                let variant = self.struct_variant(typ, span)?;
                if !visiting.insert(LayoutNode::Datatype(name.clone())) {
                    return Err(unsupported(span, "recursive struct layouts"));
                }
                let mut bytes = 0u64;
                for field in variant.fields.iter() {
                    let (typ, mode, _) = &field.a;
                    if *mode != Mode::Exec {
                        return Err(unsupported(span, "ghost or tracked struct fields"));
                    }
                    if matches!(&**typ, TypX::MutRef(_))
                        || matches!(&**typ, TypX::Decorate(d, _, _) if !matches!(d, TypDecoration::Box | TypDecoration::Arc))
                    {
                        return Err(unsupported(span, "reference or decorated struct fields"));
                    }
                    let field_bytes = self.size_inner(typ, span, visiting)?;
                    bytes = bytes
                        .checked_add(field_bytes)
                        .ok_or_else(|| unsupported(span, "struct sizes exceeding u64"))?;
                }
                visiting.remove(&LayoutNode::Datatype(name.clone()));
                Ok(bytes)
            }
            TypX::Primitive(Primitive::Array, args)
                if args.len() == 2 && integer_type_size(&args[0]).is_some() =>
            {
                let TypX::ConstInt(n) = &*args[1] else {
                    return Err(unsupported(span, "nonliteral array lengths"));
                };
                n.to_string()
                    .parse::<u64>()
                    .ok()
                    .and_then(|n| {
                        verus_meter_model::array_bytes(integer_type_size(&args[0]).unwrap(), n)
                    })
                    .ok_or_else(|| unsupported(span, "array sizes exceeding u64"))
            }
            _ => Err(unsupported(
                span,
                "this type (expected bool, a native integer, a fixed integer array, unit, a concrete struct, a local box, or a supported reference)",
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn repeated_container_types_preserve_nested_reference_presence() {
        let vector = Dt::Path(crate::fun!(CrateId::Internal => "layout_test"; "Vec").path.clone());
        let layouts = Layouts::new(&[], None, Some(vector.clone()), None);
        let allocator = Arc::new(TypX::Primitive(Primitive::Global, Arc::new(vec![])));
        let nested = |element: Typ| {
            let inner = Arc::new(TypX::Datatype(
                vector.clone(),
                Arc::new(vec![element, allocator.clone()]),
                Arc::new(vec![]),
            ));
            Arc::new(TypX::Datatype(
                vector.clone(),
                Arc::new(vec![inner, allocator.clone()]),
                Arc::new(vec![]),
            ))
        };
        let scalar = Arc::new(TypX::Int(IntRange::U(64)));
        let shared = Arc::new(TypX::Decorate(
            TypDecoration::Arc,
            Some(TypDecorationArg { allocator_typ: allocator.clone() }),
            scalar.clone(),
        ));
        assert!(layouts.contains_references(&nested(shared.clone())));
        assert!(!layouts.contains_references(&nested(scalar)));
        let erased = Arc::new(TypX::Decorate(TypDecoration::Tracked, None, shared));
        assert!(!layouts.contains_references(&nested(erased)));
    }
}
