//! Local heap ownership, separate from lexical variable slots.
//!
//! Each allocation has exactly one named owner. A move transfers that charge;
//! explicit drop and scope exit release it. Control-flow regions protect owners
//! from outside the region until path-sensitive ownership joins are supported.

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use super::model::unsupported;
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
pub(super) struct Heap {
    pub(super) owners: HashMap<VarIdent, Owner>,
    protected: HashSet<VarIdent>,
}

/// The allocation follows its owner; lexical handle slots are accounted separately.
#[derive(Clone)]
pub(super) struct Owner {
    pub(super) kind: MemoryKind,
    pub(super) bytes: u64,
    pub(super) dynamic: Option<u64>,
    pub(super) capacity: Option<Expr>,
    // The lifetime summary tells callers when this input allocation is released.
    pub(super) input: Option<usize>,
}

impl Default for Owner {
    fn default() -> Self {
        Self { kind: MemoryKind::host_heap(), bytes: 0, dynamic: None, capacity: None, input: None }
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
    fn allocate_box(&mut self, expr: &Expr) -> Result<Option<u64>, VirErr> {
        let Some(args) = intrinsic(expr, ResourceIntrinsic::BoxNew) else {
            return Ok(None);
        };
        let bytes = self
            .layouts
            .box_contents(&expr.typ, &expr.span)?
            .ok_or_else(|| unsupported(&expr.span, "this box constructor"))?;
        let TypX::Decorate(TypDecoration::Box, _, inner) = &*expr.typ else { unreachable!() };
        if !crate::ast_util::types_equal(inner, &args[0].typ) {
            return Err(unsupported(&args[0].span, "this box initializer coercion"));
        }
        self.storage.reserve(&expr.span, MemoryKind::host_heap(), bytes, "heap object")?;
        // Box::new is a model intrinsic: its argument initializes the heap object,
        // using the same destination rule as local and aggregate initializers.
        self.initialize_expr(&args[0])?;
        Ok(Some(bytes))
    }

    /// Evaluate into an existing handle destination and retain its allocation.
    pub(super) fn owner_expr(&mut self, expr: &Expr) -> Result<Owner, VirErr> {
        self.layouts.size(&expr.typ, &expr.span)?;
        if let Some(bytes) = self.allocate_box(expr)? {
            return Ok(Owner { bytes, ..Owner::default() });
        }
        if let Some(owner) = self.allocate_vector(expr)? {
            return Ok(owner);
        }
        match &expr.x {
            ExprX::ReadPlace(place, kind)
                if !matches!(kind.preliminary_kind, ReadKind::ImmutBor) =>
            {
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
