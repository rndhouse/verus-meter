//! Local heap ownership, separate from lexical variable slots.
//!
//! Each ownership tree has one named root. A move transfers the whole tree;
//! explicit drop and scope exit release it. Control-flow regions protect owners
//! from outside the region until path-sensitive ownership joins are supported.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use super::model::unsupported;
use crate::ast::*;
use crate::messages::Span;
use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Clone, Default)]
pub(super) struct Heap {
    pub(super) owners: HashMap<VarIdent, Owner>,
    // Borrowed inputs refer to vector proof state. Their original allocation
    // remains charged to the caller; replacement buffers are charged locally.
    pub(super) borrowed: HashMap<VarIdent, usize>,
    protected: HashSet<VarIdent>,
}

/// Structural position of a child owner. Runtime collections need a separate
/// aggregate representation; this tree describes only statically named children.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
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
    /// Input provenance for an entire subtree supplied by the caller.
    pub(super) input: Option<usize>,
}

impl Default for Owner {
    fn default() -> Self {
        Self {
            children: BTreeMap::new(),
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
    pub(super) fn visit(&self, f: &mut impl FnMut(&Self)) {
        f(self);
        for child in self.children.values() {
            child.visit(f);
        }
    }

    /// Every incoming allocation subtree whose lifetime follows this owner.
    pub(super) fn inputs(&self) -> HashSet<usize> {
        let mut inputs = HashSet::new();
        self.visit(&mut |node| {
            if let Some(input) = node.input {
                inputs.insert(input);
            }
        });
        inputs
    }
}

impl Heap {
    pub(super) fn protect(&mut self) -> HashSet<VarIdent> {
        let old = self.protected.clone();
        self.protected.extend(self.owners.keys().cloned());
        old
    }

    pub(super) fn unprotect(&mut self, old: HashSet<VarIdent>) {
        self.protected = old;
    }

    pub(super) fn take(&mut self, name: &VarIdent, span: &Span) -> Result<Owner, VirErr> {
        if self.protected.contains(name) {
            return Err(unsupported(
                span,
                "moving or dropping an enclosing heap owner across a branch, loop, or memory section",
            ));
        }
        self.owners
            .remove(name)
            .ok_or_else(|| unsupported(span, "a heap object without a live local owner"))
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
                if !crate::ast_util::types_equal(&place.typ, &expr.typ) {
                    return Err(unsupported(
                        &expr.span,
                        "moving an owning subvalue out of a container",
                    ));
                }
                if let PlaceX::Temporary(value) = &place.x {
                    self.owner_expr(value)
                } else {
                    self.move_owner(place)
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

    pub(super) fn move_owner(&mut self, place: &Place) -> Result<Owner, VirErr> {
        let PlaceX::Local(name) = &place.x else {
            return Err(unsupported(&place.span, "heap ownership outside a named local"));
        };
        if !self.layouts.owner(&place.typ) {
            return Err(unsupported(&place.span, "this heap move"));
        }
        self.access(place, &place.typ)?;
        let owner = self.heap.take(name, &place.span)?;
        self.storage
            .event(&place.span, "transfer heap ownership without copying the object".into());
        Ok(owner)
    }

    pub(super) fn release_owner(&mut self, owner: Owner, span: &Span) {
        for child in owner.children.into_values() {
            self.release_owner(child, span);
        }
        if let Some(input) = owner.input {
            self.storage.release_input(input);
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
            if !crate::ast_util::types_equal(&types[0], &place.typ) {
                return Err(unsupported(&expr.span, "this heap drop coercion"));
            }
            let value = self.take_value(place)?;
            let owner = self.move_owner(place)?;
            self.release_value(value, &expr.span);
            self.release_owner(owner, &expr.span);
            return Ok(Some(0));
        }
        Ok(None)
    }
}
