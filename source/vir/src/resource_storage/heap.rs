//! Local heap ownership, separate from lexical variable slots.
//!
//! Each allocation has exactly one named owner. A move transfers that charge;
//! explicit drop and scope exit release it. Control-flow regions protect owners
//! from outside the region until path-sensitive ownership joins are supported.

use super::analysis::Analysis;
use super::model::{WORD_BYTES, unsupported};
use crate::ast::*;
use crate::messages::Span;
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub(super) struct Heap {
    pub(super) owners: HashMap<VarIdent, u64>,
    protected: HashSet<VarIdent>,
    pub(super) capacities: HashMap<VarIdent, Expr>,
    pub(super) dynamic: HashMap<VarIdent, u64>,
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

    pub(super) fn take(&mut self, name: &VarIdent, span: &Span) -> Result<u64, VirErr> {
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
        self.storage.reserve(&expr.span, bytes, "heap object")?;
        // Box::new is a model intrinsic: its argument initializes the heap object,
        // using the same destination rule as local and aggregate initializers.
        self.initialize_expr(&args[0])?;
        Ok(Some(bytes))
    }

    pub(super) fn initialize_box(
        &mut self,
        name: &VarIdent,
        init: &Place,
        typ: &Typ,
    ) -> Result<(), VirErr> {
        if !crate::ast_util::types_equal(&init.typ, typ) {
            return Err(unsupported(&init.span, "this box initializer coercion"));
        }
        let bytes = match &init.x {
            PlaceX::Temporary(expr) => {
                if let Some(bytes) = self.allocate_box(expr)? {
                    bytes
                } else if let ExprX::ReadPlace(place, _) = &expr.x {
                    self.move_owner(place)?
                } else {
                    return Err(unsupported(
                        &expr.span,
                        "box initializers other than Box::new or a local move",
                    ));
                }
            }
            _ => self.move_owner(init)?,
        };
        self.heap.owners.insert(name.clone(), bytes);
        Ok(())
    }

    pub(super) fn move_owner(&mut self, place: &Place) -> Result<u64, VirErr> {
        let PlaceX::Local(name) = &place.x else {
            return Err(unsupported(&place.span, "heap ownership outside a named local"));
        };
        if !self.layouts.owner(&place.typ) {
            return Err(unsupported(&place.span, "this heap move"));
        }
        self.access(place, &place.typ)?;
        let bytes = self.heap.take(name, &place.span)?;
        self.storage
            .event(&place.span, "transfer heap ownership without copying the object".into());
        Ok(bytes)
    }

    pub(super) fn drop_owner(&mut self, name: &VarIdent, span: &Span) -> Result<(), VirErr> {
        if self.heap.owners.contains_key(name) {
            let bytes = self.heap.take(name, span)?;
            if let Some(id) = self.heap.dynamic.remove(name) {
                self.storage.release_dynamic(id);
            }
            self.heap.capacities.remove(name);
            self.storage.release(span, bytes, "drop heap object");
        }
        Ok(())
    }

    pub(super) fn heap_expr(&mut self, expr: &Expr) -> Result<Option<u64>, VirErr> {
        if intrinsic(expr, ResourceIntrinsic::BoxNew).is_some() {
            self.storage.reserve(&expr.span, WORD_BYTES, "standalone box handle")?;
            let bytes = self.allocate_box(expr)?.unwrap();
            return Ok(Some(
                bytes
                    .checked_add(WORD_BYTES)
                    .ok_or_else(|| unsupported(&expr.span, "storage totals exceeding u64"))?,
            ));
        }
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
            let bytes = self.move_owner(place)?;
            if let PlaceX::Local(name) = &place.x {
                if let Some(id) = self.heap.dynamic.remove(name) {
                    self.storage.release_dynamic(id);
                }
                self.heap.capacities.remove(name);
            }
            self.storage.release(&expr.span, bytes, "explicit drop of heap object");
            return Ok(Some(0));
        }
        Ok(None)
    }
}
