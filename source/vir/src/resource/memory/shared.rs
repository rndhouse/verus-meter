//! Strong handles refer to one canonical allocation tree.
//!
//! Cloning an analysis snapshot is not an executable Arc clone. Moves keep the
//! same root link; only a reviewed strong-clone event increments ownership.
//! Owned backing belongs to a closed domain including its workers. Body views
//! count their captured handles while backing stays in the enclosing domain;
//! their local final release cannot establish global reclamation.

mod extraction;
pub(super) mod phases;

use super::{
    analysis::Analysis,
    elements::References,
    heap::{Owner, OwnerSlot},
    model::unsupported,
};
use crate::{ast::*, messages::Span};
use std::collections::{BTreeMap, BTreeSet};

/// Allocation identity, independent of source bindings and synchronization IDs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct RootId(u64);

impl RootId {
    /// A link at a fixed ownership path. Only the canonical backing owns bytes.
    pub(super) fn record(self, span: &Span, path: Expr) -> Expr {
        use super::metadata::expr;
        expr::operation(
            span,
            "shared_reference",
            vec![path, expr::path(span, [self.serial()])],
            expr::record_type(),
        )
    }

    pub(super) fn occurrence(self, span: &Span, coordinates: &[(u64, Expr)]) -> Expr {
        use super::metadata::expr;
        let mut identity = expr::path(span, [self.serial()]);
        for (site, ordinal) in coordinates {
            identity = expr::push(span, identity, expr::integer(span, i128::from(*site)));
            identity = expr::push(span, identity, ordinal.clone());
        }
        identity
    }

    /// Stable identity encoded in an ownership descriptor, not an allocation cost.
    pub(super) fn serial(self) -> i128 {
        i128::from(self.0)
    }
}

/// A strong handle either names a canonical allocation directly or carries the
/// choice observed at a particular join. A choice never names a new allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum StrongLink {
    Known(RootId),
    Selected(u64),
}

impl StrongLink {
    pub(super) fn known(self) -> Option<RootId> {
        match self {
            Self::Known(id) => Some(id),
            Self::Selected(_) => None,
        }
    }
}

#[derive(Clone)]
pub(super) struct SelectedAlias {
    /// Frozen canonical allocation identity of this executable join result.
    pub(super) identity: Expr,
    /// Every possible backing, independently checked against the record.
    pub(super) roots: BTreeSet<RootId>,
    /// A collecting actor destroys this alias locally. Its publisher releases
    /// the reservation with the captured vector when it joins this actor.
    pub(super) collector: Option<super::workers::WorkerId>,
    /// Local clones share the selected result's single backing reservation.
    handles: u64,
    /// Number lent to this worker. The publisher holds the reservation until join.
    imported: Option<u64>,
}

impl SelectedAlias {
    fn matches(&self, span: &Span, root: RootId) -> Expr {
        crate::ast_util::mk_eq(
            span,
            &self.identity,
            &super::metadata::expr::integer(span, root.serial()),
        )
    }

    /// All clones of one mixed result reserve its observed root exactly once.
    pub(super) fn reservation(&self, span: &Span, root: RootId) -> Expr {
        super::growth::select(
            span,
            self.matches(span, root),
            super::contracts::literal(span, 1),
            super::contracts::literal(span, 0),
        )
    }
}

/// Last releases established by collecting a fixed worker.
#[derive(Default)]
pub(super) struct WorkerReleases {
    /// Canonical allocation trees no longer held by a fixed handle.
    pub(super) backing: Vec<(RootId, Owner)>,
    /// Conditional backing reservations released by the last selected alias.
    pub(super) selections: Vec<SelectedAlias>,
}

pub(super) fn selected_record(span: &Span, identity: Expr) -> Expr {
    use super::metadata::expr;
    expr::operation(
        span,
        "shared_reference",
        vec![expr::path(span, []), expr::push(span, expr::path(span, []), identity)],
        expr::record_type(),
    )
}

#[derive(Clone)]
struct Root {
    /// Live strong handles in this accounting domain, not historical clones.
    /// An imported view counts only the handles transferred into that view.
    strong: u64,
    /// Backing belongs either to this closed domain or to its enclosing caller.
    /// Releasing the last handle in an imported view cannot decide whether the
    /// enclosing domain has another live alias or reclaim its allocation tree.
    storage: Backing,
}

#[derive(Clone)]
enum Backing {
    /// Control storage, inline payload and separately owned descendants, once.
    Owned(Box<Owner>),
    /// Initial handles obtained from executable capture ownership. Keep the
    /// entry observation after the last local release for checked phase/call
    /// composition; a zero local count is not a global final-release proof.
    Imported { entry: u64 },
}

/// Shared roots and backing owned by this domain. Imported roots carry only
/// handle observations. Inline handles remain in ordinary value/aggregate
/// storage; their owner nodes contain only a root link.
#[derive(Clone, Default)]
pub(super) struct SharedRoots {
    // Keep root traversal deterministic and avoid consuming a randomized hash
    // seed in sequential functions that never create a shared allocation.
    roots: BTreeMap<RootId, Root>,
    /// Canonical payloads still owned by indexed workers after the last fixed alias moved.
    pub(super) held_payloads: BTreeSet<RootId>,
    selections: BTreeMap<u64, SelectedAlias>,
}

/// Enumerate strong handles stored directly in this finite ownership tree.
fn visit_strong_handles(
    owner: &Owner,
    span: &Span,
    supported: References,
    mut visit: impl FnMut(StrongLink) -> Result<(), VirErr>,
) -> Result<(), VirErr> {
    let mut result = Ok(());
    owner.visit(&mut |node| {
        if result.is_err() {
            return;
        }
        if node.elements.as_ref().is_some_and(|elements| elements.references > supported) {
            result = Err(unsupported(
                span,
                "imported reference populations without checked occurrence descriptors",
            ));
        } else if let Some(id) = node.shared {
            result = visit(id);
        }
    });
    result
}

impl SharedRoots {
    pub(super) fn select_alias(
        &mut self,
        identity: Expr,
        roots: BTreeSet<RootId>,
        collector: Option<super::workers::WorkerId>,
    ) -> Owner {
        let id = super::accounting::Accounting::fresh_allocation();
        self.selections
            .insert(id, SelectedAlias { identity, roots, collector, handles: 1, imported: None });
        Owner { shared: Some(StrongLink::Selected(id)), ..Default::default() }
    }

    /// A new execution of the same join site may overwrite its proof local
    /// only after the previous visit's selected handles have been retired.
    pub(super) fn compatible_selections(&self, other: &Self) -> bool {
        self.held_payloads == other.held_payloads
            && self.selections.len() == other.selections.len()
            && self.selections.iter().all(|(id, selection)| {
                other.selections.get(id).is_some_and(|s| selection.handles == s.handles)
            })
    }

    pub(super) fn selection(&self, id: u64) -> &SelectedAlias {
        &self.selections[&id]
    }

    pub(super) fn release_selection(&mut self, id: u64) -> Option<SelectedAlias> {
        let selection = self.selections.get_mut(&id).expect("live selected Arc");
        selection.handles = selection.handles.checked_sub(1).expect("positive strong ownership");
        if selection.handles == 0 && selection.imported.is_none() {
            self.selections.remove(&id)
        } else {
            None
        }
    }

    /// A transferred join handle also transfers responsibility for its target's
    /// imported aliases. They remain reserved in the enclosing domain until the
    /// receiving worker returns its checked entry-to-exit relation.
    pub(super) fn include_captured_domain(
        &mut self,
        captured: &Self,
        enclosing: &Self,
        span: &Span,
    ) -> Result<(), VirErr> {
        for (id, input) in &captured.roots {
            if !matches!(input.storage, Backing::Imported { entry } if entry == input.strong) {
                return Err(unsupported(
                    span,
                    "captured worker without its original shared entry view",
                ));
            }
            self.import_handles(StrongLink::Known(*id), input.strong, enclosing, span)?;
        }
        for (id, input) in &captured.selections {
            if input.imported != Some(input.handles) {
                return Err(unsupported(
                    span,
                    "captured worker without its original selected aliases",
                ));
            }
            self.import_handles(StrongLink::Selected(*id), input.handles, enclosing, span)?;
        }
        Ok(())
    }

    /// Check the disjoint claims of outstanding fixed workers against the
    /// enclosing domain's live aliases. A captured join handle moves its whole
    /// claim into the recipient, so the caller supplies each claim once.
    pub(super) fn check_worker_imports<'a>(
        &self,
        imports: impl Iterator<Item = &'a Self>,
        span: &Span,
    ) -> Result<(), VirErr> {
        let mut claimed = Self::default();
        for view in imports {
            claimed.include_captured_domain(view, self, span)?;
        }
        Ok(())
    }

    pub(super) fn allocation_ids(&self) -> impl Iterator<Item = RootId> + '_ {
        self.roots.keys().chain(&self.held_payloads).copied()
    }

    /// Rebind newly owned backing without changing shared identity or counts.
    pub(super) fn map_owned(
        &mut self,
        mut map: impl FnMut(&mut Owner) -> Result<(), VirErr>,
    ) -> Result<(), VirErr> {
        for root in self.roots.values_mut() {
            if let Backing::Owned(owner) = &mut root.storage {
                map(owner)?;
            }
        }
        Ok(())
    }

    /// Canonical payloads in this domain. Imported handles retain their shape
    /// and byte facts in the publishing domain.
    pub(super) fn owned(&self) -> impl Iterator<Item = &Owner> {
        self.roots.values().filter_map(|root| match &root.storage {
            Backing::Owned(owner) => Some(owner.as_ref()),
            Backing::Imported { .. } => None,
        })
    }

    /// A peer may take over charged bytes only within the frame that owns its result.
    pub(super) fn owns_result_charge(
        &self,
        root: RootId,
        storage: &super::accounting::Accounting,
    ) -> bool {
        self.roots.get(&root).is_some_and(|root| match &root.storage {
            Backing::Owned(owner) => {
                owner.dynamic.is_some_and(|id| storage.contains_allocation(id))
            }
            Backing::Imported { .. } => false,
        })
    }

    /// Separate backing transferred out of this actor, excluding imported roots.
    /// This tree is an accounting transport descriptor, never a source value.
    pub(super) fn owned_backing(&self) -> Owner {
        Owner {
            children: self
                .owned()
                .cloned()
                .enumerate()
                .map(|(index, owner)| (OwnerSlot::Capture(index), owner))
                .collect(),
            ..Default::default()
        }
    }

    /// Account for each outgoing strong handle starting from the actual result.
    /// When all aliases of an owned root are accounted for, visit its payload
    /// once. Imported roots stop at the domain boundary. A cycle leaves counts
    /// outstanding even if counting every stored payload would balance them.
    /// This checks the graph without executing a destructor or releasing bytes.
    pub(super) fn check_result(
        &self,
        result: Option<&Owner>,
        supported: References,
        span: &Span,
    ) -> Result<(), VirErr> {
        if !self.held_payloads.is_empty() {
            return Err(unsupported(
                span,
                "indexed shared payloads surviving their accounting domain",
            ));
        }
        if self.selections.values().any(|s| s.imported.is_none()) {
            return Err(unsupported(
                span,
                "selected Arc handles surviving their accounting domain",
            ));
        }
        let mut remaining: BTreeMap<_, _> = self
            .roots
            .iter()
            .map(|(id, root)| (StrongLink::Known(*id), root.strong))
            .chain(
                self.selections
                    .iter()
                    .map(|(id, selection)| (StrongLink::Selected(*id), selection.handles)),
            )
            .collect();
        let mut pending: Vec<_> = result.into_iter().map(|owner| (owner, supported)).collect();
        while let Some((owner, supported)) = pending.pop() {
            visit_strong_handles(owner, span, supported, |id| {
                let count = remaining
                    .get_mut(&id)
                    .and_then(|count| {
                        *count = count.checked_sub(1)?;
                        Some(*count)
                    })
                    .ok_or_else(|| {
                        unsupported(
                            span,
                            "outgoing strong handle outside its live shared-root domain",
                        )
                    })?;
                if count == 0
                    && let StrongLink::Known(id) = id
                    && let Backing::Owned(backing) = &self.roots[&id].storage
                {
                    // Only the actual worker result receives an occurrence descriptor.
                    pending.push((backing.as_ref(), References::None));
                }
                Ok(())
            })?;
        }
        if remaining.values().any(|count| *count != 0) {
            return Err(unsupported(span, "worker completion with unaccounted strong handles"));
        }
        Ok(())
    }

    /// Apply a fixed worker's checked entry-to-exit ownership relation at join.
    /// Earlier releases stay in its independent phase history. Applying the
    /// relation here cannot establish the global reclamation time (TODO 03.3).
    pub(super) fn receive_worker(
        &mut self,
        outgoing: &Self,
        span: &Span,
    ) -> Result<WorkerReleases, VirErr> {
        let mut next = self.clone();
        let mut released = WorkerReleases::default();
        for (id, root) in &outgoing.roots {
            match &root.storage {
                Backing::Owned(_) => {
                    if next.roots.insert(*id, root.clone()).is_some() {
                        return Err(unsupported(
                            span,
                            "duplicate shared backing at worker collection",
                        ));
                    }
                }
                Backing::Imported { entry } => {
                    let target = next.roots.get_mut(id).ok_or_else(|| {
                        unsupported(span, "worker result outside its original shared-root domain")
                    })?;
                    target.strong = phases::Handles { entry: *entry, live: root.strong }
                        .in_domain(target.strong)
                        .ok_or_else(|| {
                            unsupported(span, "inconsistent worker strong-reference transfer")
                        })?;
                    if let Some(backing) = next.take_backing_without_fixed_handles(*id) {
                        released.backing.push((*id, backing));
                    }
                }
            }
        }
        for (id, output) in &outgoing.selections {
            let count = output
                .imported
                .ok_or_else(|| unsupported(span, "worker result without a selected Arc import"))?;
            let selection = next.selections.get_mut(id).ok_or_else(|| {
                unsupported(span, "worker result outside its selected Arc lifetime")
            })?;
            selection.handles = phases::Handles { entry: count, live: output.handles }
                .in_domain(selection.handles)
                .ok_or_else(|| unsupported(span, "inconsistent selected Arc transfer"))?;
            if selection.handles == 0 && selection.imported.is_none() {
                released.selections.push(next.selections.remove(id).unwrap());
            }
        }
        *self = next;
        Ok(released)
    }

    /// Move a worker's entry claims into its indexed publication. When the
    /// whole root moves, the indexed claims take over its backing charge.
    pub(super) fn index_imports(
        &mut self,
        entry: &Self,
        span: &Span,
    ) -> Result<Vec<(RootId, u64, Owner)>, VirErr> {
        if !entry.selections.is_empty() {
            return Err(unsupported(
                span,
                "indexed publications with selected Arc capture reservations",
            ));
        }
        let mut claims = Vec::new();
        for (id, imported) in &entry.roots {
            let supported = self.roots.get(id).is_some_and(|root| {
                root.strong >= imported.strong
                    && matches!(imported.storage, Backing::Imported { entry } if entry == imported.strong)
                    && matches!(&root.storage, Backing::Owned(_))
            });
            if !supported {
                return Err(unsupported(
                    span,
                    "indexed worker aliases outside their canonical owned backing",
                ));
            }
            let Backing::Owned(backing) = &self.roots[id].storage else { unreachable!() };
            claims.push((*id, imported.strong, (**backing).clone()));
        }
        for (id, count, _) in &claims {
            self.roots.get_mut(id).unwrap().strong -= count;
            self.take_backing_without_fixed_handles(*id);
        }
        Ok(claims)
    }

    pub(super) fn has_strong(&self, id: RootId) -> bool {
        self.roots.get(&id).is_some_and(|root| root.strong > 0)
    }

    /// Transfer one checked result link back to the finite owner tree. When
    /// the parent previously dropped its last handle, that same backing was
    /// charged conditionally to indexed workers, and now becomes fixed again.
    pub(super) fn receive_indexed(
        &mut self,
        id: RootId,
        backing: &Owner,
        span: &Span,
    ) -> Result<Owner, VirErr> {
        if let Some(root) = self.roots.get_mut(&id) {
            root.strong = root
                .strong
                .checked_add(1)
                .ok_or_else(|| unsupported(span, "strong handle counts exceeding u64"))?;
        } else {
            self.roots
                .insert(id, Root { strong: 1, storage: Backing::Owned(Box::new(backing.clone())) });
        }
        Ok(Owner { shared: Some(StrongLink::Known(id)), ..Default::default() })
    }

    pub(super) fn is_empty(&self) -> bool {
        self.held_payloads.is_empty()
            && self.selections.is_empty()
            && self.roots.values().all(|root| root.strong == 0)
    }

    pub(super) fn insert(&mut self, storage: Owner) -> Owner {
        let id = RootId(super::accounting::Accounting::fresh_allocation());
        assert!(
            self.roots
                .insert(id, Root { strong: 1, storage: Backing::Owned(Box::new(storage)) })
                .is_none()
        );
        Owner { shared: Some(StrongLink::Known(id)), ..Default::default() }
    }

    fn clone_strong(&mut self, link: StrongLink, span: &Span) -> Result<Owner, VirErr> {
        let id = match link {
            StrongLink::Known(id) => id,
            StrongLink::Selected(id) => {
                let selection = self.selections.get_mut(&id).ok_or_else(|| {
                    unsupported(span, "cloning an Arc outside its selected lifetime")
                })?;
                if selection.handles == 0 {
                    return Err(unsupported(
                        span,
                        "cloning a selected Arc after its last local handle ended",
                    ));
                }
                selection.handles = selection
                    .handles
                    .checked_add(1)
                    .ok_or_else(|| unsupported(span, "strong handle counts exceeding u64"))?;
                return Ok(Owner { shared: Some(link), ..Default::default() });
            }
        };
        let root = self.roots.get_mut(&id).ok_or_else(|| {
            unsupported(span, "cloning a shared root without live ownership provenance")
        })?;
        if root.strong == 0 {
            return Err(unsupported(
                span,
                "cloning a shared root after its last local handle ended",
            ));
        }
        root.strong = root
            .strong
            .checked_add(1)
            .ok_or_else(|| unsupported(span, "strong handle counts exceeding u64"))?;
        Ok(Owner { shared: Some(StrongLink::Known(id)), ..Default::default() })
    }

    /// Apply one executable strong-handle drop in this domain.
    pub(super) fn release(&mut self, id: RootId) -> Option<Owner> {
        let root = self.roots.get_mut(&id).expect("live strong handle retains its shared root");
        root.strong = root.strong.checked_sub(1).expect("positive strong ownership");
        self.take_backing_without_fixed_handles(id)
    }

    /// Detach owned backing when the last finite handle ends. Imported roots
    /// leave reclamation to their enclosing domain.
    fn take_backing_without_fixed_handles(&mut self, id: RootId) -> Option<Owner> {
        let root = &self.roots[&id];
        if root.strong == 0 && matches!(root.storage, Backing::Owned(_)) {
            let Backing::Owned(storage) = self.roots.remove(&id).unwrap().storage else {
                unreachable!()
            };
            Some(*storage)
        } else {
            None
        }
    }

    /// Derive a worker's entry references from its actual captured owner tree.
    /// This lends no backing charge and executes no clone/destructor. References
    /// inside an opaque runtime population require a checked population view.
    pub(super) fn captured_view(&self, owner: Option<&Owner>, span: &Span) -> Result<Self, VirErr> {
        let mut captured = Self::default();
        if let Some(owner) = owner {
            visit_strong_handles(owner, span, References::WorkerOccurrences, |link| {
                captured.import_handles(link, 1, self, span)
            })?;
            let mut reserved = Ok(());
            owner.visit(&mut |node| {
                if reserved.is_ok()
                    && let Some(super::workers::SelectedWorker::Recorded(occurrence)) =
                        &node.selected_worker
                    && let Some(id) = occurrence.result_reservation
                {
                    reserved = captured.import_handles(StrongLink::Selected(id), 1, self, span);
                }
            });
            reserved?;
        }
        Ok(captured)
    }

    /// Combine transfers of actual handles into one worker's entry view.
    fn import_handles(
        &mut self,
        link: StrongLink,
        count: u64,
        enclosing: &Self,
        span: &Span,
    ) -> Result<(), VirErr> {
        let total = |previous: u64, available: Option<u64>| {
            previous
                .checked_add(count)
                .filter(|n| available.is_some_and(|limit| *n <= limit))
                .ok_or_else(|| {
                    unsupported(span, "worker captures outside their live shared-root domain")
                })
        };
        match link {
            StrongLink::Known(id) => {
                let strong = total(
                    self.roots.get(&id).map_or(0, |r| r.strong),
                    enclosing.roots.get(&id).map(|r| r.strong),
                )?;
                self.roots
                    .insert(id, Root { strong, storage: Backing::Imported { entry: strong } });
            }
            StrongLink::Selected(id) => {
                let source = enclosing.selections.get(&id).ok_or_else(|| {
                    unsupported(span, "worker capture outside its selected Arc lifetime")
                })?;
                let count =
                    total(self.selections.get(&id).map_or(0, |s| s.handles), Some(source.handles))?;
                self.selections.insert(
                    id,
                    SelectedAlias { handles: count, imported: Some(count), ..source.clone() },
                );
            }
        }
        Ok(())
    }

    /// A control-flow merge cannot silently discard a surviving root or adopt
    /// one branch's reference count. Symbolic population joins need their own
    /// inductive relationship, supplied by worker/collection effects.
    pub(super) fn compatible(&self, other: &Self) -> bool {
        self.compatible_selections(other)
            && self.roots.len() == other.roots.len()
            && self.roots.iter().all(|(id, root)| {
                other.roots.get(id).is_some_and(|other| {
                    root.strong == other.strong
                        && match (&root.storage, &other.storage) {
                            (Backing::Owned(a), Backing::Owned(b)) => {
                                super::control::compatible(a, b)
                            }
                            (Backing::Imported { entry: a }, Backing::Imported { entry: b }) => {
                                a == b
                            }
                            _ => false,
                        }
                })
            })
    }
}

impl Analysis<'_> {
    pub(super) fn link_record(&self, span: &Span, link: StrongLink) -> Expr {
        match link {
            StrongLink::Known(root) => self.root_record(span, root),
            StrongLink::Selected(id) => {
                selected_record(span, self.heap.shared.selection(id).identity.clone())
            }
        }
    }

    pub(super) fn freeze_shared_identity(
        &mut self,
        span: &Span,
        identity: Expr,
        after: bool,
    ) -> Expr {
        use super::metadata::expr;
        let (frozen, decl) = expr::local(
            span,
            "shared_visit",
            identity.typ.clone(),
            expr::path(span, []),
            Mode::Spec,
        );
        self.growth.declarations.push(decl);
        let schedule = if after { &mut self.growth.after } else { &mut self.growth.before };
        schedule.entry(span.id).or_default().push(expr::assign(span, &frozen, identity));
        frozen
    }

    pub(super) fn root_record(&self, span: &Span, root: RootId) -> Expr {
        let path = super::metadata::expr::path(span, []);
        let Some(identity) = self.growth.shared_occurrences.get(&root) else {
            return root.record(span, path);
        };
        super::metadata::expr::operation(
            span,
            "shared_reference",
            vec![path, identity.clone()],
            super::metadata::expr::record_type(),
        )
    }

    /// A reviewed native dereference returns a view of existing backing. It
    /// neither clones a strong handle nor allocates or transfers the payload.
    pub(super) fn shared_borrow(&mut self, expr: &Expr) -> Result<bool, VirErr> {
        let ExprX::Call {
            target: CallTarget::Fun(_, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(false);
        };
        if attrs.resource_intrinsic
            != Some(ResourceIntrinsic::Concurrency(super::concurrency::Operation::ArcBorrow))
        {
            return Ok(false);
        }
        let [argument] = args.as_slice() else {
            return Err(unsupported(&expr.span, "this shared dereference signature"));
        };
        let TypX::Decorate(TypDecoration::Ref, None, receiver) = &*argument.typ else {
            return Err(unsupported(
                &expr.span,
                "a shared dereference without a borrowed receiver",
            ));
        };
        let TypX::Decorate(TypDecoration::Arc, _, payload) = &**receiver else {
            return Err(unsupported(&expr.span, "this shared dereference receiver type"));
        };
        let TypX::Decorate(TypDecoration::Ref, None, target) = &*expr.typ else {
            return Err(unsupported(&expr.span, "this shared dereference result type"));
        };
        if !crate::ast_util::types_equal(payload, target) {
            return Err(unsupported(&expr.span, "this shared dereference payload coercion"));
        }
        self.layouts.size(receiver, &expr.span)?;
        self.discard(argument)?;
        self.result_owner = None;
        Ok(true)
    }

    /// Construct or clone a strong owner into an already charged handle slot.
    pub(super) fn shared_owner(&mut self, expr: &Expr) -> Result<Option<Owner>, VirErr> {
        use super::concurrency::Operation;
        let ExprX::Call {
            target: CallTarget::Fun(_, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } = &expr.x
        else {
            return Ok(None);
        };
        let Some(ResourceIntrinsic::Concurrency(operation)) = attrs.resource_intrinsic else {
            return Ok(None);
        };
        if operation == Operation::ArcIntoInner {
            let [source] = args.as_slice() else {
                return Err(unsupported(&expr.span, "this Arc::into_inner signature"));
            };
            return self.take_shared_payload(expr, source).map(Some);
        }
        if !matches!(operation, Operation::ArcNew | Operation::ArcClone) {
            return Ok(None);
        }
        let TypX::Decorate(TypDecoration::Arc, _, payload) = &*expr.typ else {
            return Err(unsupported(&expr.span, "a strong-owner operation with an invalid result"));
        };
        self.layouts.size(&expr.typ, &expr.span)?;
        let [argument] = args.as_slice() else {
            return Err(unsupported(
                &expr.span,
                "a strong-owner operation with an invalid signature",
            ));
        };
        if operation == Operation::ArcNew {
            if !crate::ast_util::types_equal(payload, &argument.typ) {
                return Err(unsupported(&expr.span, "this shared payload initializer coercion"));
            }
            let bytes =
                verus_meter_model::arc_backing_bytes(self.layouts.size(payload, &expr.span)?)
                    .ok_or_else(|| {
                        unsupported(&expr.span, "shared backing storage exceeding u64")
                    })?;
            self.storage.reserve(
                &expr.span,
                super::footprint::MemoryKind::host_heap(),
                bytes,
                "shared backing and inline payload",
            )?;
            self.initialize_expr(argument)?;
            let mut storage = Owner {
                bytes,
                extent: Some(super::contracts::literal(&expr.span, bytes)),
                ..Default::default()
            };
            if self.layouts.owner(payload) {
                storage.children.insert(
                    OwnerSlot::Contents,
                    self.result_owner.take().ok_or_else(|| {
                        unsupported(&expr.span, "a shared payload without its owned descendants")
                    })?,
                );
            }
            let handle = self.heap.shared.insert(storage);
            let root = handle.shared.and_then(StrongLink::known).expect("new strong owner");
            let mut coordinates = self
                .current_worker
                .and_then(|actor| self.growth.worker_occurrences.get(&actor))
                .cloned()
                .unwrap_or_default();
            coordinates.extend(self.local_occurrences(&expr.span)?);
            if !coordinates.is_empty() {
                let identity = root.occurrence(&expr.span, &coordinates);
                let identity = self.freeze_shared_identity(&expr.span, identity, true);
                self.growth.shared_occurrences.insert(root, identity);
            }
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::StrongNew {
                    payload: argument.clone(),
                    root,
                    coordinates,
                },
            );
            return Ok(Some(handle));
        }
        let Some((name, path)) = super::paths::expr(argument, &expr.typ) else {
            let receiver = match &argument.x {
                ExprX::ReadPlace(place, kind)
                    if matches!(kind.preliminary_kind, ReadKind::ImmutBor) =>
                {
                    let PlaceX::Temporary(value) = &place.x else {
                        return Err(unsupported(&argument.span, "this shared clone receiver"));
                    };
                    value
                }
                _ => argument,
            };
            if !crate::ast_util::types_equal(&receiver.typ, &expr.typ) {
                return Err(unsupported(&argument.span, "this shared clone receiver coercion"));
            }
            let operation = self.concurrency.clone_operation(expr).ok_or_else(|| {
                unsupported(&expr.span, "a temporary clone receiver without native call evidence")
            })?;
            let operation = operation.span.id;
            let value = self.produce(receiver)?;
            let owner = self.result_owner.take().ok_or_else(|| {
                unsupported(&argument.span, "a temporary clone receiver without ownership")
            })?;
            let root = owner.shared.ok_or_else(|| {
                unsupported(&argument.span, "a temporary clone receiver without shared provenance")
            })?;
            let cloned = self.heap.shared.clone_strong(root, &expr.span)?;
            self.retain_temporary(
                operation,
                &argument.span,
                super::lifetime::Storage { typ: expr.typ.clone(), value, owner: Some(owner) },
            )?;
            return Ok(Some(cloned));
        };
        let root = self
            .heap
            .root(&name)
            .and_then(|owner| owner.at(&path))
            .and_then(|owner| owner.shared)
            .ok_or_else(|| {
                unsupported(&argument.span, "a shared clone without canonical root provenance")
            })?;
        // Evaluating a reference argument retains the source handle and all
        // its storage. It is never a move or a second payload allocation.
        if let ExprX::ReadPlace(place, _) = &argument.x {
            // Logical identity translation can retain the owning Arc type in
            // a consuming context such as drop(root.clone()). The native clone
            // still borrows its receiver; do not infer a move from that type.
            self.access(place, &expr.typ)?;
        } else {
            self.discard(argument)?;
        }
        let cloned = self.heap.shared.clone_strong(root, &expr.span)?;
        self.transitions.operation(
            &expr.span,
            super::transfer::checked::Operation::StrongClone {
                receiver: super::transfer::checked::Place {
                    source: argument.clone(),
                    typ: expr.typ.clone(),
                    location: (name, path),
                },
            },
        );
        Ok(Some(cloned))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::sync::Arc;

    #[test]
    fn outgoing_aliases_reach_nested_backing_once() {
        let mut roots = SharedRoots::default();
        let inner = roots.insert(Owner { bytes: 48, ..Default::default() });
        let alias = roots.clone_strong(inner.shared.unwrap(), &span()).unwrap();
        let outer = roots.insert(inner);
        let outer_alias = roots.clone_strong(outer.shared.unwrap(), &span()).unwrap();
        let result = Owner {
            children: [
                (OwnerSlot::Capture(0), alias),
                (OwnerSlot::Capture(1), outer),
                (OwnerSlot::Capture(2), outer_alias),
            ]
            .into(),
            ..Default::default()
        };
        roots.check_result(Some(&result), References::None, &span()).unwrap();
        let mut missing = result.clone();
        missing.children.remove(&OwnerSlot::Capture(0));
        assert!(roots.check_result(Some(&missing), References::None, &span()).is_err());
        // Checking an output must preserve its actual counts and storage.
        roots.check_result(Some(&result), References::None, &span()).unwrap();
    }

    #[test]
    fn balanced_cycles_cannot_be_exported_as_owned_backing() {
        let mut roots = SharedRoots::default();
        let first = roots.insert(Owner::default());
        let id = first.shared.unwrap().known().unwrap();
        let second = roots.insert(first);
        let Backing::Owned(payload) = &mut roots.roots.get_mut(&id).unwrap().storage else {
            unreachable!()
        };
        **payload = second;
        assert!(roots.check_result(None, References::None, &span()).is_err());
        // Even an additional actual result handle cannot discharge the cycle.
        let returned = roots.clone_strong(StrongLink::Known(id), &span()).unwrap();
        assert!(roots.check_result(Some(&returned), References::None, &span()).is_err());
    }

    #[test]
    fn simultaneous_workers_cannot_share_one_strong_handle_claim() {
        let mut enclosing = SharedRoots::default();
        let handle = enclosing.insert(Owner::default());
        let worker = enclosing.captured_view(Some(&handle), &span()).unwrap();
        assert!(enclosing.check_worker_imports([&worker, &worker].into_iter(), &span()).is_err());
        let second = enclosing.clone_strong(handle.shared.unwrap(), &span()).unwrap();
        let sibling = enclosing.captured_view(Some(&second), &span()).unwrap();
        enclosing.check_worker_imports([&worker, &sibling].into_iter(), &span()).unwrap();
    }

    #[test]
    fn captured_views_do_not_reclaim_the_enclosing_domains_backing() {
        let mut enclosing = SharedRoots::default();
        let first = enclosing.insert(Owner { bytes: 64, ..Default::default() });
        let id = first.shared.unwrap().known().unwrap();
        let second = enclosing.clone_strong(StrongLink::Known(id), &span()).unwrap();
        let captures = Owner {
            children: [(OwnerSlot::Capture(0), first), (OwnerSlot::Capture(1), second)].into(),
            ..Default::default()
        };
        let mut body = enclosing.captured_view(Some(&captures), &span()).unwrap();
        assert_eq!(body.roots[&id].strong, 2);
        assert!(matches!(body.roots[&id].storage, Backing::Imported { entry: 2 }));
        body.clone_strong(StrongLink::Known(id), &span()).unwrap();
        assert_eq!(enclosing.roots[&id].strong, 2);
        assert_eq!(body.clone().roots[&id].strong, 3);
        for _ in 0..3 {
            assert!(body.release(id).is_none());
        }
        assert!(body.is_empty());
        assert!(matches!(body.roots[&id].storage, Backing::Imported { entry: 2 }));
        assert!(body.clone_strong(StrongLink::Known(id), &span()).is_err());
        assert!(body.captured_view(Some(&captures), &span()).is_err());
        assert!(enclosing.release(id).is_none());
        assert_eq!(enclosing.release(id).unwrap().bytes, 64);
        assert!(enclosing.is_empty());
    }

    #[test]
    fn capture_import_cannot_turn_analysis_snapshots_into_extra_strong_handles() {
        let mut enclosing = SharedRoots::default();
        let handle = enclosing.insert(Owner { bytes: 64, ..Default::default() });
        assert!(SharedRoots::default().captured_view(Some(&handle), &span()).is_err());
        let copied_analysis = handle.clone();
        let duplicated = Owner {
            children: [(OwnerSlot::Capture(0), handle), (OwnerSlot::Capture(1), copied_analysis)]
                .into(),
            ..Default::default()
        };
        assert!(enclosing.captured_view(Some(&duplicated), &span()).is_err());
        assert!(enclosing.captured_view(None, &span()).unwrap().is_empty());
    }

    fn span() -> Span {
        Span {
            raw_span: std::sync::Arc::new(()),
            id: 1,
            data: std::sync::Arc::new([]),
            as_string: "shared owner test".into(),
        }
    }

    #[test]
    fn handles_share_one_owned_tree_and_only_final_release_returns_it() {
        let mut roots = SharedRoots::default();
        let mut payload = Owner { bytes: 48, ..Default::default() };
        payload.children.insert(OwnerSlot::Contents, Owner { bytes: 128, ..Default::default() });
        let first = roots.insert(payload);
        let id = first.shared.unwrap().known().unwrap();
        let second = roots.clone_strong(StrongLink::Known(id), &span()).unwrap();
        assert_eq!(first.shared, second.shared);
        assert_eq!(roots.roots.len(), 1);
        assert!(roots.release(id).is_none());
        let payload = roots.release(second.shared.unwrap().known().unwrap()).unwrap();
        assert_eq!(payload.bytes, 48);
        assert_eq!(payload.children[&OwnerSlot::Contents].bytes, 128);
        assert!(roots.is_empty());
    }

    #[test]
    fn snapshot_copy_does_not_create_a_runtime_strong_handle() {
        let mut roots = SharedRoots::default();
        let handle = roots.insert(Owner { bytes: 24, ..Default::default() });
        let mut branch = roots.clone();
        assert!(roots.compatible(&branch));
        assert!(roots.release(handle.shared.unwrap().known().unwrap()).is_some());
        assert!(!roots.compatible(&branch));
        assert!(branch.release(handle.shared.unwrap().known().unwrap()).is_some());
    }

    #[test]
    fn source_operations_charge_handles_separately_and_reclaim_backing_once() {
        use super::super::{accounting::Accounting, concurrency::Operation, layout::Layouts};
        for payload_kind in [None, Some(TypDecoration::Box), Some(TypDecoration::Arc)] {
            let layouts = Layouts::new(&[], None, None, None);
            let functions = HashMap::new();
            let summaries = HashMap::new();
            let budgets = HashMap::new();
            let concurrency = super::super::concurrency::Evidence::default();
            let site = span();
            let mut analysis = Analysis {
                worker_inputs: vec![],
                capture_views: Default::default(),
                evaluations: Default::default(),
                concurrency: &concurrency,
                current_worker: None,
                flow: Default::default(),
                transitions: Default::default(),
                slots: HashMap::new(),
                produced: None,
                summaries: &summaries,
                result_owner: None,
                budgets: &budgets,
                layouts: &layouts,
                functions: &functions,
                var_modes: HashMap::new(),
                storage: Accounting::new(&site, 1024),
                calls: Vec::new(),
                checkpoints: Vec::new(),
                stable_scalars: Default::default(),
                heap: Default::default(),
                obligations: Vec::new(),
                checks: Vec::new(),
                growth: Default::default(),
                input_paths: Vec::new(),
                bound: super::super::contracts::literal(&site, 1024),
            };
            let decorate = |decoration, payload| {
                Arc::new(TypX::Decorate(
                    decoration,
                    Some(TypDecorationArg {
                        allocator_typ: Arc::new(TypX::Primitive(
                            Primitive::Global,
                            Arc::new(vec![]),
                        )),
                    }),
                    payload,
                ))
            };
            let call = |result: &Typ, intrinsic, argument| {
                SpannedTyped::new(
                    &site,
                    result,
                    ExprX::Call {
                        target: CallTarget::Fun(
                            CallTargetKind::Static,
                            crate::fun!(CrateId::Alloc => "sync"; "arc_operation"),
                            Arc::new(vec![]),
                            Arc::new(vec![]),
                            CallTargetAttrs {
                                autospec: AutospecUsage::Final,
                                const_var: false,
                                assume_external_allowed: false,
                                resource_intrinsic: Some(intrinsic),
                            },
                        ),
                        args: Arc::new(vec![argument]),
                        post_args: None,
                        body: None,
                    },
                )
            };
            let scalar = Arc::new(TypX::Int(IntRange::U(64)));
            let literal = SpannedTyped::new(&site, &scalar, ExprX::Const(Constant::Int(7.into())));
            let (payload, initializer, retained) = match payload_kind {
                None => (scalar, literal, 32), // handle 8 + backing 16 + payload 8
                Some(kind) => {
                    let payload = decorate(kind, scalar);
                    let intrinsic = if kind == TypDecoration::Box {
                        ResourceIntrinsic::BoxNew
                    } else {
                        ResourceIntrinsic::Concurrency(Operation::ArcNew)
                    };
                    let initializer = call(&payload, intrinsic, literal);
                    // Box adds its u64 allocation; nested Arc adds control + u64.
                    let retained = if kind == TypDecoration::Box { 40 } else { 56 };
                    (payload, initializer, retained)
                }
            };
            let shared = decorate(TypDecoration::Arc, payload);
            let value = analysis
                .produce(&call(
                    &shared,
                    ResourceIntrinsic::Concurrency(Operation::ArcNew),
                    initializer,
                ))
                .unwrap();
            let owner = analysis.result_owner.take().unwrap();
            assert_eq!(analysis.storage.live(), retained);
            let name = VarIdent(Arc::new("root".into()), VarIdentDisambiguate::RustcId(1));
            analysis.var_modes.insert(name.clone(), Mode::Exec);
            analysis.slots.insert(name.clone(), value);
            analysis.heap.owners.insert(name.clone(), owner);
            let place = SpannedTyped::new(&site, &shared, PlaceX::Local(name.clone()));
            let reference = Arc::new(TypX::Decorate(TypDecoration::Ref, None, shared.clone()));
            let argument = SpannedTyped::new(
                &site,
                &reference,
                ExprX::ReadPlace(
                    place,
                    UnfinalizedReadKind { preliminary_kind: ReadKind::ImmutBor, id: 0 },
                ),
            );
            let copy = analysis
                .produce(&call(
                    &shared,
                    ResourceIntrinsic::Concurrency(Operation::ArcClone),
                    argument,
                ))
                .unwrap();
            let copy_owner = analysis.result_owner.take().unwrap();
            assert_eq!(analysis.storage.live(), retained + 8);
            // Moving an ownership descriptor into a symbolic byte forest is
            // not an executable strong drop. Until those forests carry root
            // identities, the operation must reject without freeing backing.
            assert!(analysis.release_owner_storage(copy_owner.clone(), &site, false).is_err());
            assert_eq!(analysis.storage.live(), retained + 8);
            let owner = analysis.heap.owners.remove(&name).unwrap();
            analysis.release_owner(owner, &site);
            let value = analysis.slots.remove(&name).unwrap();
            analysis.release_value(value, &site);
            assert_eq!(analysis.storage.live(), retained); // clone retains all backing
            analysis.release_owner(copy_owner, &site);
            analysis.release_value(copy, &site);
            assert_eq!(analysis.storage.live(), 0);
            assert_eq!(analysis.storage.peak().bytes, u128::from(retained + 8));
        }
    }
}
