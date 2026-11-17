//! Strong handles refer to one canonical allocation tree.
//!
//! Cloning an analysis snapshot is not an executable Arc clone. Moves keep the
//! same root link; only a reviewed strong-clone event increments ownership.
//! Owned backing belongs to a closed domain including its workers. Body views
//! count their captured handles while backing stays in the enclosing domain;
//! their local final release cannot establish global reclamation.

use super::{
    analysis::Analysis,
    heap::{Owner, OwnerSlot},
    model::unsupported,
};
use crate::{ast::*, messages::Span};
use std::collections::BTreeMap;

/// Allocation identity, independent of source bindings and synchronization IDs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct RootId(u64);

impl RootId {
    /// Stable identity encoded in an ownership descriptor, not an allocation cost.
    pub(super) fn serial(self) -> i128 {
        i128::from(self.0)
    }
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
}

impl SharedRoots {
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
            if !matches!(input.storage, Backing::Imported { .. }) {
                return Err(unsupported(
                    span,
                    "captured worker inputs with duplicate shared backing",
                ));
            }
            let count = self
                .roots
                .get(id)
                .map_or(0, |root| root.strong)
                .checked_add(input.strong)
                .ok_or_else(|| unsupported(span, "captured strong counts exceeding u64"))?;
            if enclosing.roots.get(id).is_none_or(|root| root.strong < count) {
                return Err(unsupported(
                    span,
                    "captured worker aliases outside their shared domain",
                ));
            }
            self.roots
                .insert(*id, Root { strong: count, storage: Backing::Imported { entry: count } });
        }
        Ok(())
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

    /// Separate backing transferred out of this actor, excluding imported roots.
    /// This tree is an accounting transport descriptor, never a source value.
    pub(super) fn owned_backing(&self) -> Owner {
        Owner {
            children: self
                .roots
                .values()
                .filter_map(|root| match &root.storage {
                    Backing::Owned(owner) => Some((**owner).clone()),
                    Backing::Imported { .. } => None,
                })
                .enumerate()
                .map(|(index, owner)| (OwnerSlot::Capture(index), owner))
                .collect(),
            ..Default::default()
        }
    }

    /// Every surviving handle must occur in the result or its newly owned
    /// backing. Lost local handles cannot be hidden by an outgoing byte total.
    pub(super) fn check_result(&self, result: Option<&Owner>, span: &Span) -> Result<(), VirErr> {
        let mut outgoing = self.owned_backing();
        if let Some(result) = result {
            outgoing.children.insert(OwnerSlot::Contents, result.clone());
        }
        let view = self.captured_view(Some(&outgoing), span)?;
        if self
            .roots
            .iter()
            .any(|(id, root)| view.roots.get(id).map_or(0, |root| root.strong) != root.strong)
        {
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
    ) -> Result<Vec<Owner>, VirErr> {
        let mut next = self.clone();
        let mut released = Vec::new();
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
                    target.strong = target
                        .strong
                        .checked_sub(*entry)
                        .and_then(|remaining| remaining.checked_add(root.strong))
                        .ok_or_else(|| {
                            unsupported(span, "inconsistent worker strong-reference transfer")
                        })?;
                    if target.strong == 0 && matches!(target.storage, Backing::Owned(_)) {
                        let Backing::Owned(backing) = next.roots.remove(id).unwrap().storage else {
                            unreachable!()
                        };
                        released.push(*backing);
                    }
                }
            }
        }
        *self = next;
        Ok(released)
    }

    pub(super) fn is_empty(&self) -> bool {
        self.roots.values().all(|root| root.strong == 0)
    }

    fn insert(&mut self, storage: Owner) -> Owner {
        let id = RootId(super::accounting::Accounting::fresh_allocation());
        assert!(
            self.roots
                .insert(id, Root { strong: 1, storage: Backing::Owned(Box::new(storage)) })
                .is_none()
        );
        Owner { shared: Some(id), ..Default::default() }
    }

    fn clone_strong(&mut self, id: RootId, span: &Span) -> Result<Owner, VirErr> {
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
        Ok(Owner { shared: Some(id), ..Default::default() })
    }

    /// Return an owned allocation tree exactly once at final destruction in
    /// this closed domain. An imported root exports its local release instead;
    /// the enclosing composition must establish global reclamation separately.
    pub(super) fn release(&mut self, id: RootId) -> Option<Owner> {
        let root = self.roots.get_mut(&id).expect("live strong handle retains its shared root");
        root.strong = root.strong.checked_sub(1).expect("positive strong ownership");
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
        let mut references = BTreeMap::<RootId, u64>::new();
        let mut opaque = false;
        if let Some(owner) = owner {
            owner.visit(&mut |owner| {
                opaque |= owner.elements.as_ref().is_some_and(|elements| elements.has_references);
                if let Some(id) = owner.shared {
                    let count = references.entry(id).or_default();
                    // A finite compiler-owned tree has at most usize::MAX
                    // nodes; symbolic populations must use their own binders.
                    *count = count.checked_add(1).expect("finite captured reference count");
                }
            });
        }
        if opaque {
            return Err(unsupported(
                span,
                "imported reference populations without checked occurrence descriptors",
            ));
        }
        let mut roots = BTreeMap::new();
        for (id, count) in references {
            if self.roots.get(&id).is_none_or(|root| root.strong < count) {
                return Err(unsupported(
                    span,
                    "worker captures outside their live shared-root domain",
                ));
            }
            roots.insert(id, Root { strong: count, storage: Backing::Imported { entry: count } });
        }
        Ok(Self { roots })
    }

    /// A control-flow merge cannot silently discard a surviving root or adopt
    /// one branch's reference count. Symbolic population joins need their own
    /// inductive relationship, supplied by worker/collection effects.
    pub(super) fn compatible(&self, other: &Self) -> bool {
        self.roots.len() == other.roots.len()
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
            return Ok(Some(self.heap.shared.insert(storage)));
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
        Ok(Some(self.heap.shared.clone_strong(root, &expr.span)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::sync::Arc;

    #[test]
    fn captured_views_do_not_reclaim_the_enclosing_domains_backing() {
        let mut enclosing = SharedRoots::default();
        let first = enclosing.insert(Owner { bytes: 64, ..Default::default() });
        let id = first.shared.unwrap();
        let second = enclosing.clone_strong(id, &span()).unwrap();
        let captures = Owner {
            children: [(OwnerSlot::Capture(0), first), (OwnerSlot::Capture(1), second)].into(),
            ..Default::default()
        };
        let mut body = enclosing.captured_view(Some(&captures), &span()).unwrap();
        assert_eq!(body.roots[&id].strong, 2);
        assert!(matches!(body.roots[&id].storage, Backing::Imported { entry: 2 }));
        body.clone_strong(id, &span()).unwrap();
        assert_eq!(enclosing.roots[&id].strong, 2);
        assert_eq!(body.clone().roots[&id].strong, 3);
        for _ in 0..3 {
            assert!(body.release(id).is_none());
        }
        assert!(body.is_empty());
        assert!(matches!(body.roots[&id].storage, Backing::Imported { entry: 2 }));
        assert!(body.clone_strong(id, &span()).is_err());
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
        let id = first.shared.unwrap();
        let second = roots.clone_strong(id, &span()).unwrap();
        assert_eq!(first.shared, second.shared);
        assert_eq!(roots.roots.len(), 1);
        assert!(roots.release(id).is_none());
        let payload = roots.release(second.shared.unwrap()).unwrap();
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
        assert!(roots.release(handle.shared.unwrap()).is_some());
        assert!(!roots.compatible(&branch));
        assert!(branch.release(handle.shared.unwrap()).is_some());
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
