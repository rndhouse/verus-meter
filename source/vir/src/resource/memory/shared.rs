//! Strong handles refer to one canonical allocation tree.
//!
//! Cloning an analysis snapshot is not an executable Arc clone. Moves keep the
//! same root link; only a reviewed strong-clone event increments ownership. This
//! registry belongs to the closed accounting domain, including its workers.

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

#[derive(Clone)]
struct Root {
    /// Live strong handles in this ownership state, not historical clone calls.
    strong: u64,
    /// Backing control storage, inline payload and separately owned descendants.
    storage: Owner,
}

/// Single storage descriptor per shared root. Inline handles remain in ordinary
/// value/aggregate storage; their owner nodes contain only a root link.
#[derive(Clone, Default)]
pub(super) struct SharedRoots {
    // Keep root traversal deterministic and avoid consuming a randomized hash
    // seed in sequential functions that never create a shared allocation.
    roots: BTreeMap<RootId, Root>,
}

impl SharedRoots {
    pub(super) fn is_empty(&self) -> bool {
        self.roots.is_empty()
    }

    fn insert(&mut self, storage: Owner) -> Owner {
        let id = RootId(super::accounting::Accounting::fresh_allocation());
        assert!(self.roots.insert(id, Root { strong: 1, storage }).is_none());
        Owner { shared: Some(id), ..Default::default() }
    }

    fn clone_strong(&mut self, id: RootId, span: &Span) -> Result<Owner, VirErr> {
        let root = self.roots.get_mut(&id).ok_or_else(|| {
            unsupported(span, "cloning a shared root without live ownership provenance")
        })?;
        root.strong = root
            .strong
            .checked_add(1)
            .ok_or_else(|| unsupported(span, "strong handle counts exceeding u64"))?;
        Ok(Owner { shared: Some(id), ..Default::default() })
    }

    /// Return the allocation tree exactly once, at the final strong destruction.
    /// The ordinary heap release path then destroys its owned descendants.
    pub(super) fn release(&mut self, id: RootId) -> Option<Owner> {
        let root = self.roots.get_mut(&id).expect("live strong handle retains its shared root");
        root.strong = root.strong.checked_sub(1).expect("positive strong ownership");
        (root.strong == 0).then(|| self.roots.remove(&id).unwrap().storage)
    }

    /// A control-flow merge cannot silently discard a surviving root or adopt
    /// one branch's reference count. Symbolic population joins need their own
    /// inductive relationship, supplied by worker/collection effects.
    pub(super) fn compatible(&self, other: &Self) -> bool {
        self.roots.len() == other.roots.len()
            && self.roots.iter().all(|(id, root)| {
                other.roots.get(id).is_some_and(|other| {
                    root.strong == other.strong
                        && super::control::compatible(&root.storage, &other.storage)
                })
            })
    }
}

impl Analysis<'_> {
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
        let (name, path) = super::paths::expr(argument, &expr.typ).ok_or_else(|| {
            unsupported(
                &argument.span,
                "a shared clone without a stable source owner; bind its source first",
            )
        })?;
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
        self.discard(argument)?;
        Ok(Some(self.heap.shared.clone_strong(root, &expr.span)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::sync::Arc;

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
