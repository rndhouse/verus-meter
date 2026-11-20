//! Local heap ownership, separate from lexical variable slots.
//!
//! Each ownership tree has one named root. Fixed children can move independently;
//! explicit drop and scope exit release only the remaining tree. Control-flow
//! regions protect persistent owners; checked loop branches join partitioned
//! input lifetimes while keeping their fixed ownership slots stable.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use super::model::unsupported;
use super::workers::SelectedWorker;
use crate::ast::*;
use crate::messages::Span;
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Clone, Default)]
pub(super) struct Heap {
    /// Owned native receivers stay live until rustc's actual destruction scope.
    pub(super) temporaries: Vec<super::temporaries::Temporary>,
    /// Executing workers and completed results survive their source handle slots.
    pub(super) workers: super::workers::Workers,
    /// Shared allocations live once in the closed domain, independently of
    /// which local, aggregate or worker currently retains each strong handle.
    pub(super) shared: super::shared::SharedRoots,
    /// Local roots in a stable order. Loop snapshots and invariants visit this
    /// map directly, so its iteration order becomes part of the solver input.
    pub(super) owners: BTreeMap<VarIdent, Owner>,
    /// Borrowed inputs use the same structural paths as owned inputs. Original
    /// allocations remain charged to the caller; additional slots are charged here.
    pub(super) borrowed: BTreeMap<VarIdent, Owner>,
    protected: HashSet<VarIdent>,
    /// Loops may partition ownership while retaining enclosing owner slots.
    /// Checked loop branches preserve it through explicit lifetime joins;
    /// optional matches and memory sections clear it until they exit.
    partitions: HashSet<VarIdent>,
    /// Disjoint replaced child paths of borrowed inputs, exported at calls.
    pub(super) replaced: HashSet<super::paths::LocalPath>,
}

/// Structural position of a child owner. Runtime collections use footprint sums;
/// indexed slots exist only while borrowing a child for one operation.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum OwnerSlot {
    Contents,
    Field(Ident),
    /// Executable closure field in the compiler's post-erasure capture order.
    Capture(usize),
    /// Operation-local borrowed projection; never exported in an ownership summary.
    Element(u64),
}

pub(super) type OwnerPath = Vec<OwnerSlot>;

/// Separately owned storage. A node may own an allocation and fixed child owners;
/// its inline storage belongs to the enclosing value or allocation layout.
#[derive(Clone)]
pub(super) struct Owner {
    /// A source mutex identity or a returned acquisition, transported with its owner.
    pub(super) synchronization: Option<super::synchronization::local::Owned>,
    /// A collection handle and the evidence its owner can use at join.
    pub(super) selected_worker: Option<SelectedWorker>,
    /// Native/vstd successful join payload, conditional on every possible body's
    /// normal-domain proofs. Ordinary Result values cannot invent this witness.
    pub(super) joined: Option<std::collections::BTreeSet<super::workers::WorkerId>>,
    /// The Some outcome established by consuming a proved unique Arc.
    pub(super) extracted_arc: Option<super::shared::RootId>,
    /// A join handle names storage kept in the domain's worker registry.
    pub(super) worker: Option<super::workers::FixedHandle>,
    /// Concrete closure definition; its owned fields occupy Capture child slots.
    pub(super) closure: Option<usize>,
    /// A strong handle links to canonical backing instead of owning a copy of it.
    pub(super) shared: Option<super::shared::StrongLink>,
    /// Whether descriptors include incoming allocations or only this frame's charges.
    pub(super) view: super::metadata::View,
    /// Current logical value, used to serialize collection geometry before a call.
    pub(super) source: Option<(Typ, Expr)>,
    /// Frozen logical count when an owner moves beneath an optional payload.
    pub(super) geometry: Option<Expr>,
    /// False for aggregate-only summaries that expose no logical child count.
    pub(super) geometry_known: bool,
    /// Separately owned allocations beneath fields or a box payload. Their inline
    /// handles are already included in the containing value/allocation layout.
    pub(super) children: BTreeMap<OwnerSlot, Owner>,
    /// Runtime child allocations, aggregated independently of element storage.
    pub(super) elements: Option<super::elements::Elements>,
    /// Memory kind charged for the owned allocation, independently of its handle.
    pub(super) kind: MemoryKind,
    /// Fixed portion of the live charge, released when this owner is consumed.
    pub(super) bytes: u64,
    /// Identity of any symbolic portion of the live charge.
    pub(super) dynamic: Option<u64>,
    /// Byte extent (or conservative bound) supplied by a constructor or summary.
    /// Incoming allocations use their caller's charge instead.
    pub(super) extent: Option<Expr>,
    /// Original vector reservation used when exporting an unchanged fresh result.
    pub(super) capacity: Option<Expr>,
    /// Vector proof-state identity, preserved when its handle moves.
    pub(super) vector: Option<usize>,
    /// Input provenance for this node; fixed children have independent IDs.
    pub(super) input: Option<usize>,
}

impl Default for Owner {
    fn default() -> Self {
        Self {
            synchronization: None,
            selected_worker: None,
            joined: None,
            extracted_arc: None,
            worker: None,
            closure: None,
            shared: None,
            view: Default::default(),
            source: None,
            geometry: None,
            geometry_known: true,
            children: BTreeMap::new(),
            elements: None,
            kind: MemoryKind::host_heap(),
            bytes: 0,
            dynamic: None,
            extent: None,
            capacity: None,
            vector: None,
            input: None,
        }
    }
}

impl Owner {
    /// Byte-free owner nodes and forests still carry strong/worker lifetimes.
    pub(super) fn references(&self) -> super::elements::References {
        use super::elements::References;
        if self.shared.is_some() || self.worker.is_some() || self.joined.is_some() {
            return References::Unclassified;
        }
        let own = match self.selected_worker {
            Some(SelectedWorker::Parameter) => return References::Unclassified,
            Some(SelectedWorker::Recorded(_)) => References::WorkerOccurrences,
            None => References::None,
        };
        self.children
            .values()
            .map(Self::references)
            .chain(self.elements.iter().map(|elements| elements.references))
            .fold(own, References::combine)
    }

    /// A fresh fixed wrapper does not make its incoming children fully charged.
    pub(super) fn complete(&self) -> bool {
        let mut complete = true;
        self.visit(&mut |node| {
            complete &= node.view == super::metadata::View::Complete
                && node
                    .elements
                    .as_ref()
                    .is_none_or(|elements| elements.view == super::metadata::View::Complete);
        });
        complete
    }

    /// Detach a fixed child without touching any allocation charge.
    pub(super) fn take_child(&mut self, path: &[OwnerSlot]) -> Option<Owner> {
        let (last, parent) = path.split_last()?;
        self.at_mut(parent)?.children.remove(last)
    }

    /// Install a child and return the displaced owner for explicit release.
    pub(super) fn replace_child(&mut self, path: &[OwnerSlot], child: Owner) -> Option<Owner> {
        let (last, parent) = path.split_last().expect("child path");
        self.at_mut(parent).expect("validated child parent").children.insert(last.clone(), child)
    }

    /// Split a tree into disjoint nodes for call provenance. Every allocation
    /// identity occurs once; reconstructing results consumes these nodes.
    pub(super) fn flatten(mut self, path: &mut OwnerPath, nodes: &mut BTreeMap<OwnerPath, Owner>) {
        for (slot, child) in std::mem::take(&mut self.children) {
            path.push(slot);
            child.flatten(path, nodes);
            path.pop();
        }
        nodes.insert(path.clone(), self);
    }

    pub(super) fn at(&self, path: &[OwnerSlot]) -> Option<&Owner> {
        let mut node = self;
        for slot in path {
            node = node.children.get(slot)?;
        }
        Some(node)
    }

    pub(super) fn at_mut(&mut self, path: &[OwnerSlot]) -> Option<&mut Owner> {
        let mut node = self;
        for slot in path {
            node = node.children.get_mut(slot)?;
        }
        Some(node)
    }

    pub(super) fn visit_paths(&self, path: &mut OwnerPath, f: &mut impl FnMut(&OwnerPath, &Self)) {
        f(path, self);
        for (slot, child) in &self.children {
            path.push(slot.clone());
            child.visit_paths(path, f);
            path.pop();
        }
    }

    pub(super) fn visit(&self, f: &mut impl FnMut(&Self)) {
        f(self);
        for child in self.children.values() {
            child.visit(f);
        }
    }

    pub(super) fn visit_mut(&mut self, f: &mut impl FnMut(&mut Self)) {
        f(self);
        for child in self.children.values_mut() {
            child.visit_mut(f);
        }
    }

    /// Every incoming allocation node whose lifetime follows this owner.
    pub(super) fn inputs(&self) -> HashSet<usize> {
        let mut inputs = HashSet::new();
        self.visit(&mut |node| {
            if let Some(input) = node.input {
                inputs.insert(input);
            }
            if let Some(elements) = &node.elements {
                inputs.extend(elements.inputs.iter().copied());
            }
        });
        inputs
    }
}

impl Heap {
    /// A terminating edge may consume protected owners because it cannot rejoin
    /// the region's continuing paths. Lexical cleanup retains ordinary charges.
    pub(super) fn exit_protection(&mut self) -> (HashSet<VarIdent>, HashSet<VarIdent>) {
        (std::mem::take(&mut self.protected), std::mem::take(&mut self.partitions))
    }
    pub(super) fn root(&self, name: &VarIdent) -> Option<&Owner> {
        self.owners.get(name).or_else(|| self.borrowed.get(name))
    }

    pub(super) fn root_mut(&mut self, name: &VarIdent) -> Option<&mut Owner> {
        if self.owners.contains_key(name) {
            self.owners.get_mut(name)
        } else {
            self.borrowed.get_mut(name)
        }
    }

    pub(super) fn element_states(&self) -> Vec<usize> {
        let mut ids = Vec::new();
        for owner in self.owners.values().chain(self.borrowed.values()) {
            owner.visit(&mut |node| {
                if let Some(elements) = &node.elements {
                    ids.extend(elements.states.values().copied());
                }
            });
        }
        ids
    }

    pub(super) fn vectors(&self) -> Vec<usize> {
        let mut ids = Vec::new();
        for owner in self.owners.values().chain(self.borrowed.values()) {
            owner.visit(&mut |node| {
                if let Some(id) = node.vector {
                    ids.push(id);
                }
            });
        }
        ids
    }

    pub(super) fn protect(&mut self) -> (HashSet<VarIdent>, HashSet<VarIdent>) {
        let old = (self.protected.clone(), std::mem::take(&mut self.partitions));
        self.protected.extend(self.owners.keys().cloned());
        self.protected.extend(self.borrowed.keys().cloned());
        old
    }

    /// A loop branch can partition its persistent roles and consume owners
    /// created by the current iteration. The join must agree on surviving slots;
    /// enclosing owners remain protected against whole moves or drops.
    pub(super) fn protect_branch(
        &mut self,
        in_loop: bool,
    ) -> (HashSet<VarIdent>, HashSet<VarIdent>) {
        let old = self.protect();
        if in_loop {
            self.protected = old.0.clone();
            self.partitions = old.1.clone();
        }
        old
    }

    pub(super) fn unprotect(&mut self, old: (HashSet<VarIdent>, HashSet<VarIdent>)) {
        (self.protected, self.partitions) = old;
    }

    pub(super) fn permit_loop_partitions(
        &mut self,
        outer: &HashSet<VarIdent>,
        partitions: &HashSet<VarIdent>,
    ) {
        // A directly nested loop may continue partitioning roles authorized by
        // its enclosing loop. Checked loop branches join these partitions;
        // optional matches and sections retain their own protection scope.
        self.partitions.extend(partitions.iter().cloned());
        self.partitions.extend(self.owners.keys().filter(|name| !outer.contains(*name)).cloned());
        self.partitions.extend(self.borrowed.keys().filter(|name| !outer.contains(*name)).cloned());
    }

    pub(super) fn check_partition(&self, name: &VarIdent, span: &Span) -> Result<(), VirErr> {
        if self.partitions.contains(name) { Ok(()) } else { self.check_transfer(name, span) }
    }

    pub(super) fn take(&mut self, name: &VarIdent, span: &Span) -> Result<Owner, VirErr> {
        self.check_transfer(name, span)?;
        self.owners
            .remove(name)
            .ok_or_else(|| unsupported(span, "a heap object without a live local owner"))
    }

    pub(super) fn is_replaced(&self, name: &VarIdent, path: &[OwnerSlot]) -> bool {
        self.replaced.iter().any(|(root, parent)| root == name && path.starts_with(parent))
    }

    pub(super) fn mark_replaced(&mut self, name: &VarIdent, path: &OwnerPath) {
        // Indexed borrows return their effects to the containing runtime sum.
        if super::paths::indexed(path) {
            return;
        }
        if self.borrowed.contains_key(name) && !self.is_replaced(name, path) {
            self.replaced.retain(|(root, child)| root != name || !child.starts_with(path));
            self.replaced.insert((name.clone(), path.clone()));
        }
    }

    pub(super) fn check_transfer(&self, name: &VarIdent, span: &Span) -> Result<(), VirErr> {
        if self.protected.contains(name) {
            return Err(unsupported(
                span,
                "moving or dropping an enclosing heap owner across a branch, loop, or memory section",
            ));
        }
        Ok(())
    }
}

pub(super) fn boxed(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Decorate(TypDecoration::Box, _, _))
}

fn intrinsic(expr: &Expr, kind: ResourceIntrinsic) -> Option<&Exprs> {
    match &expr.x {
        ExprX::Call {
            target: CallTarget::Fun(CallTargetKind::Static, _, _, _, attrs),
            args,
            post_args: None,
            body: None,
        } if attrs.resource_intrinsic == Some(kind) && args.len() == 1 => Some(args),
        _ => None,
    }
}

impl Analysis<'_> {
    pub(super) fn mark_input(&mut self, owner: &mut Owner, parameter: usize, path: &mut OwnerPath) {
        let id = self.input_paths.len();
        self.input_paths.push((parameter, path.clone()));
        self.transitions.input(parameter, path.clone());
        self.storage.add_input(id);
        owner.input = Some(id);
        for (slot, child) in &mut owner.children {
            path.push(slot.clone());
            self.mark_input(child, parameter, path);
            path.pop();
        }
    }

    /// Mirror the input's structure without charging its original allocations.
    /// Each node receives independent lifetime provenance; vector states count
    /// only additional slots funded here. The caller retains the entry charge.
    /// Runtime descendants use an initially empty local-charge forest: absence
    /// means no allocation was made here, not that the executable child is absent.
    pub(super) fn input_owner(
        &mut self,
        typ: &Typ,
        span: &Span,
        input_bytes: u64,
        name: &VarIdent,
        path: &mut OwnerPath,
        capacities: &HashMap<super::paths::LocalPath, Expr>,
        worker_parameter: bool,
    ) -> Result<Owner, VirErr> {
        if super::iterators::owns_vector_storage(typ) {
            return Err(unsupported(span, "taking a consuming iterator as a parameter"));
        }
        if matches!(&**typ, TypX::AnonymousClosure(..)) {
            return Err(unsupported(span, "closure inputs without a checked capture summary"));
        }
        if self.layouts.result_payloads(typ).is_some() {
            return Err(unsupported(
                span,
                "primitive Result inputs without checked outcome provenance",
            ));
        }
        if self.layouts.join_handle(typ).is_some() {
            return Err(unsupported(
                span,
                "worker inputs without a checked accounting-domain descriptor",
            ));
        }
        if matches!(&**typ, TypX::Decorate(TypDecoration::Arc, _, _)) {
            return Err(unsupported(span, "shared input roots without a checked alias descriptor"));
        }
        if !worker_parameter
            && self.layouts.owning_elements(typ)
            && self.layouts.contains_references(typ)
        {
            return Err(unsupported(
                span,
                "incoming reference populations without a checked accounting-domain descriptor",
            ));
        }
        let mut owner = Owner {
            view: super::metadata::View::Local,
            geometry_known: !self.layouts.cardinality(typ),
            ..Default::default()
        };
        if self.layouts.owning_elements(typ) {
            owner.elements = Some(self.new_elements(span));
            owner.elements.as_mut().unwrap().view = super::metadata::View::Local;
        }
        if self.layouts.vector(typ) {
            let capacity = capacities.get(&(name.clone(), path.clone()));
            let allocation = super::accounting::Accounting::fresh_allocation();
            let state = self.growth.new_vector(
                span,
                capacity.cloned().unwrap_or_else(|| super::contracts::literal(span, 0)),
                super::footprint::Charge {
                    kind: owner.kind.clone(),
                    amount: super::contracts::literal(span, 0),
                },
                self.layouts.vector_element(typ, span)?,
                Some(input_bytes),
                allocation,
            );
            self.growth.vectors[state].reserved = capacity.is_some();
            self.storage.set_allocation(
                allocation,
                owner.kind.clone(),
                self.growth.vectors[state].backing.bytes.clone(),
            );
            owner.vector = Some(state);
            owner.dynamic = Some(allocation);
        }
        for (slot, child) in self.layouts.owned_children(typ, span)? {
            path.push(slot.clone());
            owner.children.insert(
                slot,
                self.input_owner(&child, span, input_bytes, name, path, capacities, false)?,
            );
            path.pop();
        }
        Ok(owner)
    }

    fn allocate_box(&mut self, expr: &Expr) -> Result<Option<Owner>, VirErr> {
        let Some(args) = intrinsic(expr, ResourceIntrinsic::BoxNew) else {
            return Ok(None);
        };
        let layout = self
            .layouts
            .box_layout(&expr.typ, &expr.span)?
            .ok_or_else(|| unsupported(&expr.span, "this box constructor"))?;
        let super::layout::AllocationLayout::Fixed(bytes) = layout else {
            return Err(unsupported(&expr.span, "Box::new with an unsized payload"));
        };
        let TypX::Decorate(TypDecoration::Box, _, inner) = &*expr.typ else { unreachable!() };
        if !crate::ast_util::types_equal(inner, &args[0].typ) {
            return Err(unsupported(&args[0].span, "this box initializer coercion"));
        }
        self.storage.reserve(&expr.span, MemoryKind::host_heap(), bytes, "heap object")?;
        // Box::new is a model intrinsic: its argument initializes the heap object,
        // using the same destination rule as local and aggregate initializers.
        self.initialize_expr(&args[0])?;
        let mut owner = Owner {
            bytes,
            extent: Some(super::contracts::literal(&expr.span, bytes)),
            ..Owner::default()
        };
        if self.layouts.owner(inner) {
            let child = self
                .result_owner
                .take()
                .ok_or_else(|| unsupported(&expr.span, "a box payload without ownership"))?;
            owner.children.insert(OwnerSlot::Contents, child);
        }
        self.transitions.operation(
            &expr.span,
            super::transfer::checked::Operation::Box { payload: args[0].clone(), bytes },
        );
        Ok(Some(owner))
    }

    /// Evaluate into an existing handle destination and retain its allocation.
    pub(super) fn owner_expr(&mut self, expr: &Expr) -> Result<Owner, VirErr> {
        self.layouts.size(&expr.typ, &expr.span)?;
        if let Some(owner) = self.spawn_owner(expr)? {
            return Ok(owner);
        }
        if let Some(owner) = self.shared_owner(expr)? {
            return Ok(owner);
        }
        if let Some(owner) = self.extracted_owner(expr, false)? {
            return Ok(owner);
        }
        if let Some(owner) = self.synchronization_owner(expr)? {
            return Ok(owner);
        }
        if let Some(owner) = self.allocate_box(expr)? {
            return Ok(owner);
        }
        if let Some(owner) = self.allocate_vector(expr)? {
            return Ok(owner);
        }
        if let Some(owner) = self.boxed_slice_expr(expr)? {
            return Ok(owner);
        }
        match &expr.x {
            ExprX::Ctor(..) => {
                self.construction(expr, true)?;
                self.result_owner
                    .take()
                    .ok_or_else(|| unsupported(&expr.span, "a constructor without ownership"))
            }
            ExprX::ReadPlace(place, kind)
                if !matches!(kind.preliminary_kind, ReadKind::ImmutBor) =>
            {
                if let PlaceX::Temporary(value) = &place.x {
                    if !crate::ast_util::types_equal(&value.typ, &expr.typ) {
                        return Err(unsupported(
                            &expr.span,
                            "extracting an owner from a temporary container",
                        ));
                    }
                    self.owner_expr(value)
                } else {
                    self.move_owner_to(place, &expr.typ)
                }
            }
            ExprX::Block(stmts, tail) => {
                self.block(expr, stmts, tail, true)?;
                self.result_owner.take().ok_or_else(|| {
                    unsupported(&expr.span, "an owning block without an owned result")
                })
            }
            ExprX::Call { .. } => {
                self.call_expr(expr, true)?;
                self.result_owner
                    .take()
                    .ok_or_else(|| unsupported(&expr.span, "a call without an ownership summary"))
            }
            _ => Err(unsupported(
                &expr.span,
                "owning results other than constructors, local moves, blocks, or direct calls",
            )),
        }
    }

    pub(super) fn release_owner(&mut self, owner: Owner, span: &Span) {
        let mut proofs = Vec::new();
        let carrier_ended = self.ends_indexed_carrier(&owner);
        self.destroy_owner(owner, span, true, &mut proofs);
        if carrier_ended {
            self.finish_indexed_payloads(span, &mut proofs);
        }
        self.growth.before.entry(span.id).or_default().extend(proofs);
    }

    /// Lexical cleanup observes the state after evaluating the scope or exit
    /// operand. A declaration's span is not its eventual destruction site.
    pub(super) fn release_owner_after(&mut self, owner: Owner, span: &Span) {
        let mut proofs = Vec::new();
        let carrier_ended = self.ends_indexed_carrier(&owner);
        self.destroy_owner(owner, span, true, &mut proofs);
        if carrier_ended {
            self.finish_indexed_payloads(span, &mut proofs);
        }
        if !proofs.is_empty() {
            self.growth.after.entry(span.id).or_default().extend(proofs);
        }
    }

    /// Transfers into an aggregate release the old charge identities while
    /// keeping incoming allocation lifetimes attached to their new owner.
    pub(super) fn release_owner_storage(
        &mut self,
        mut owner: Owner,
        span: &Span,
        inputs: bool,
    ) -> Result<(), VirErr> {
        let mut shared = false;
        owner.visit(&mut |node| {
            shared |=
                matches!(node.synchronization, Some(super::synchronization::local::Owned::Guard(_)))
                    || matches!(node.selected_worker, Some(SelectedWorker::Parameter))
                    || node.shared.is_some()
                    || node.closure.is_some()
                    || node.worker.is_some()
        });
        if shared {
            // Forest records retain identity links, but the population consumer
            // must also preserve their multiplicity and canonical lifetimes.
            // Moving a charge into a sum cannot execute a strong destructor.
            return Err(unsupported(
                span,
                "shared handles, closures or workers in runtime ownership forests without an identity summary",
            ));
        }
        fn transported(owner: &mut Owner) {
            owner.selected_worker = None;
            if let Some(elements) = &mut owner.elements {
                elements.references = super::elements::References::None;
            }
            for child in owner.children.values_mut() {
                transported(child);
            }
        }
        transported(&mut owner);
        let mut proofs = Vec::new();
        self.destroy_owner(owner, span, inputs, &mut proofs);
        self.growth.before.entry(span.id).or_default().extend(proofs);
        Ok(())
    }

    /// After the last fixed handle ends, indexed workers may still own this
    /// allocation. At final destruction its input regions need their own scan
    /// because the shared target lies outside the handle's enclosing tree.
    pub(super) fn release_shared_backing(
        &mut self,
        root: super::shared::RootId,
        backing: Owner,
        span: &Span,
        proofs: &mut Vec<Stmt>,
    ) {
        self.peer_release_checks(root, &backing, span, proofs);
        if let Some(claims) = self.growth.indexed_shared.get(&root) {
            claims.retain_backing(
                root,
                &mut self.heap.shared.held_payloads,
                &mut self.storage,
                span,
                proofs,
            );
        } else {
            self.destroy_owner(backing, span, true, proofs);
        }
    }

    pub(super) fn destroy_owner(
        &mut self,
        owner: Owner,
        span: &Span,
        inputs: bool,
        proofs: &mut Vec<Stmt>,
    ) {
        if let Some(super::synchronization::local::Owned::Guard(interval)) = owner.synchronization {
            self.storage.release_interval(span, interval);
        }
        if owner.selected_worker.is_some() {
            self.heap.workers.detach_occurrence(span);
            return;
        }
        if let Some(worker) = owner.worker {
            assert!(
                owner.bytes == 0
                    && owner.children.is_empty()
                    && owner.dynamic.is_none()
                    && owner.shared.is_none()
                    && owner.closure.is_none()
                    && owner.input.is_none()
            );
            self.heap.workers.detach(worker.actor, span);
            return;
        }
        if let Some(root) = owner.shared {
            // A handle node owns only its link. Backing/payload destruction is
            // deferred while any other strong handle remains in the domain.
            assert!(
                owner.bytes == 0
                    && owner.dynamic.is_none()
                    && owner.children.is_empty()
                    && owner.elements.is_none()
                    && owner.input.is_none()
            );
            match root {
                super::shared::StrongLink::Known(id) => {
                    if let Some(backing) = self.heap.shared.release(id) {
                        self.release_shared_backing(id, backing, span, proofs);
                    }
                }
                super::shared::StrongLink::Selected(id) => {
                    if let Some(selection) = self.heap.shared.release_selection(id) {
                        self.release_selected_alias(span, selection, proofs);
                    }
                }
            }
            return;
        }
        if inputs {
            for input in owner.inputs() {
                self.storage.release_input(input);
            }
        }
        for child in owner.children.into_values() {
            self.destroy_owner(child, span, false, proofs);
        }
        if let Some(elements) = owner.elements {
            if elements.references == super::elements::References::IndexedAliases {
                self.release_selected_slots(span, &elements.records, proofs);
            } else if elements.references != super::elements::References::None {
                proofs.push(super::metadata::expr::check(
                    span,
                    super::metadata::expr::operation(
                        span,
                        "workers_empty",
                        vec![elements.records.clone()],
                        crate::ast_util::bool_typ(),
                    ),
                    "cannot discard outstanding worker handles",
                ));
            }
            for state in elements.states.into_values() {
                self.storage.release_dynamic(self.growth.elements[state].id);
            }
        }
        if let Some(id) = owner.dynamic {
            self.storage.release_dynamic(id);
        }
        self.storage.release(span, owner.kind, owner.bytes, "drop heap object");
    }

    pub(super) fn heap_expr(&mut self, expr: &Expr) -> Result<Option<u64>, VirErr> {
        if let Some(args) = intrinsic(expr, ResourceIntrinsic::HeapDrop) {
            // Expression decorations can retain an implicit Box dereference.
            // The instantiated parameter type distinguishes drop(box) from
            // drop(*box), which only consumes a copy of its contents.
            let ExprX::Call { target: CallTarget::Fun(_, _, types, _, _), .. } = &expr.x else {
                unreachable!()
            };
            if types.len() == 1
                && matches!(&*types[0], TypX::AnonymousClosure(..))
                && !self.layouts.owner(&types[0])
            {
                // Rust copies this closure into the drop argument. Its original
                // source value stays live until its own move or scope exit.
                let value = self.produce(&args[0])?;
                self.release_value(value, &expr.span);
                return Ok(Some(0));
            }
            if types.len() != 1 || !self.layouts.owner(&types[0]) {
                return Err(unsupported(
                    &expr.span,
                    "drop of anything other than a named local heap owner",
                ));
            }
            if matches!(&*types[0], TypX::Decorate(TypDecoration::Arc, _, _))
                && !matches!(&args[0].x, ExprX::ReadPlace(_, _))
            {
                // drop consumes this owned argument by value. Borrowed receiver
                // temporaries inside it keep their separate compiler scopes.
                let value = self.produce(&args[0])?;
                let owner = self.result_owner.take().ok_or_else(|| {
                    unsupported(&expr.span, "dropping a temporary without shared ownership")
                })?;
                // The operand may publish its ownership evidence at join. Its
                // destructor runs only after that operand has produced the Arc.
                self.release_owner_after(owner, &expr.span);
                self.release_value(value, &expr.span);
                self.transitions.operation(
                    &expr.span,
                    super::transfer::checked::Operation::Drop { source: args[0].clone() },
                );
                return Ok(Some(0));
            }
            let ExprX::ReadPlace(place, _) = &args[0].x else {
                return Err(unsupported(
                    &expr.span,
                    "drop of anything other than a named local heap owner",
                ));
            };
            self.access(place, &types[0])?;
            // A child handle remains part of its parent's inline storage. Drop
            // consumes its ownership without creating another handle slot.
            if matches!(place.x, PlaceX::Local(_))
                && crate::ast_util::types_equal(&types[0], &place.typ)
            {
                let value = self.take_value(place)?;
                self.release_value(value, &expr.span);
            }
            let owner = self.move_owner_to(place, &types[0])?;
            self.release_owner(owner, &expr.span);
            self.transitions.operation(
                &expr.span,
                super::transfer::checked::Operation::Drop { source: args[0].clone() },
            );
            return Ok(Some(0));
        }
        Ok(None)
    }
}
