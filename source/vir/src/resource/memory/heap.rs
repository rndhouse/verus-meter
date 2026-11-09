//! Local heap ownership, separate from lexical variable slots.
//!
//! Each ownership tree has one named root. Fixed children can move independently;
//! explicit drop and scope exit release only the remaining tree. Control-flow
//! regions protect enclosing owners until path-sensitive joins are supported.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use super::model::unsupported;
use crate::ast::*;
use crate::messages::Span;
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Clone, Default)]
pub(super) struct Heap {
    pub(super) owners: HashMap<VarIdent, Owner>,
    /// Borrowed inputs use the same structural paths as owned inputs. Original
    /// allocations remain charged to the caller; replacements are charged here.
    pub(super) borrowed: HashMap<VarIdent, Owner>,
    protected: HashSet<VarIdent>,
    /// Disjoint replaced child paths of borrowed inputs, exported at calls.
    pub(super) replaced: HashSet<super::paths::LocalPath>,
}

/// Structural position of a fixed child owner. Runtime collections use separate
/// footprint sums rather than adding a path for each element.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum OwnerSlot {
    Contents,
    Field(Ident),
}

pub(super) type OwnerPath = Vec<OwnerSlot>;

/// Separately owned storage. A node may own an allocation and fixed child owners;
/// its inline storage belongs to the enclosing value or allocation layout.
#[derive(Clone)]
pub(super) struct Owner {
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

    pub(super) fn protect(&mut self) -> HashSet<VarIdent> {
        let old = self.protected.clone();
        self.protected.extend(self.owners.keys().cloned());
        self.protected.extend(self.borrowed.keys().cloned());
        old
    }

    pub(super) fn unprotect(&mut self, old: HashSet<VarIdent>) {
        self.protected = old;
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
    /// only replacements made here. The caller retains every original charge.
    pub(super) fn input_owner(
        &mut self,
        typ: &Typ,
        span: &Span,
        input_bytes: u64,
        name: &VarIdent,
        path: &mut OwnerPath,
        capacities: &HashMap<super::paths::LocalPath, Expr>,
    ) -> Result<Owner, VirErr> {
        let mut owner = Owner::default();
        if self.layouts.owning_elements(typ) {
            owner.elements = Some(self.new_elements(span));
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
            owner
                .children
                .insert(slot, self.input_owner(&child, span, input_bytes, name, path, capacities)?);
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
        Ok(Some(owner))
    }

    /// Evaluate into an existing handle destination and retain its allocation.
    pub(super) fn owner_expr(&mut self, expr: &Expr) -> Result<Owner, VirErr> {
        self.layouts.size(&expr.typ, &expr.span)?;
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
        self.release_owner_storage(owner, span, true);
    }

    /// Transfers into an aggregate release the old charge identities while
    /// keeping incoming allocation lifetimes attached to their new owner.
    pub(super) fn release_owner_storage(&mut self, owner: Owner, span: &Span, inputs: bool) {
        if inputs {
            for input in owner.inputs() {
                self.storage.release_input(input);
            }
        }
        for child in owner.children.into_values() {
            self.release_owner_storage(child, span, false);
        }
        if let Some(elements) = owner.elements {
            for state in elements.states.into_values() {
                self.storage.release_dynamic(self.growth.elements[state].id);
            }
        }
        if let Some(id) = owner.dynamic {
            self.storage.release_dynamic(id);
        }
        self.storage.release(span, owner.kind, owner.bytes, "drop heap object");
    }

    pub(super) fn drop_owner(&mut self, name: &VarIdent, span: &Span) -> Result<(), VirErr> {
        if self.heap.owners.contains_key(name) {
            let owner = self.heap.take(name, span)?;
            self.release_owner(owner, span);
        }
        Ok(())
    }

    pub(super) fn heap_expr(&mut self, expr: &Expr) -> Result<Option<u64>, VirErr> {
        if let Some(args) = intrinsic(expr, ResourceIntrinsic::HeapDrop) {
            // Expression decorations can retain an implicit Box dereference.
            // The instantiated parameter type distinguishes drop(box) from
            // drop(*box), which only consumes a copy of its contents.
            let ExprX::Call { target: CallTarget::Fun(_, _, types, _, _), .. } = &expr.x else {
                unreachable!()
            };
            if types.len() != 1 || !self.layouts.owner(&types[0]) {
                return Err(unsupported(
                    &expr.span,
                    "drop of anything other than a named local heap owner",
                ));
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
            return Ok(Some(0));
        }
        Ok(None)
    }
}
