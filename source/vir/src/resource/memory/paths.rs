//! Locate fixed child owners in executable places and specification projections.
//!
//! References preserve the owner's path; each implicit Box dereference adds a
//! contents slot. Runtime indexing and local reference aliases are not paths in
//! this model. Consumers must validate the place and find a live tracked root.

use super::heap::{OwnerPath, OwnerSlot};
use crate::ast::*;
use crate::ast_util::types_equal;

/// Local root and the child relative to that root.
pub(super) type LocalPath = (VarIdent, OwnerPath);
/// Formal parameter index and child path exported to a checked caller.
pub(super) type InputPath = (usize, OwnerPath);

pub(super) fn referent(mut typ: &Typ) -> &Typ {
    while let TypX::MutRef(inner) | TypX::Decorate(TypDecoration::Ref, None, inner) = &**typ {
        typ = inner;
    }
    typ
}

/// Follow only the implicit dereferences needed to reach the requested type.
fn project(mut location: LocalPath, from: &Typ, target: &Typ) -> Option<LocalPath> {
    let mut typ = referent(from);
    let target = referent(target);
    while !types_equal(typ, target) {
        let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ else { return None };
        location.1.push(OwnerSlot::Contents);
        typ = inner;
    }
    Some(location)
}

fn field_base(typ: &Typ) -> &Typ {
    let mut typ = referent(typ);
    while let TypX::Decorate(TypDecoration::Box, _, inner) = &**typ {
        typ = inner;
    }
    typ
}

pub(super) fn place(place: &Place, target: &Typ) -> Option<LocalPath> {
    let location = match &place.x {
        PlaceX::Local(name) => (name.clone(), vec![]),
        PlaceX::DerefMut(base) => self::place(base, &place.typ)?,
        PlaceX::Field(op, base) => {
            let mut location = self::place(base, field_base(&base.typ))?;
            location.1.push(OwnerSlot::Field(op.field.clone()));
            location
        }
        PlaceX::Temporary(value) => expr(value, &place.typ)?,
        _ => return None,
    };
    project(location, &place.typ, target)
}

pub(super) fn expr(value: &Expr, target: &Typ) -> Option<LocalPath> {
    match &value.x {
        ExprX::Old(base) | ExprX::Unary(UnaryOp::MutRefCurrent, base) => expr(base, target),
        ExprX::ReadPlace(p, _) | ExprX::BorrowMut(p) | ExprX::TwoPhaseBorrowMut(p) => {
            place(p, target)
        }
        ExprX::Var(name) | ExprX::VarAt(name, _) => {
            project((name.clone(), vec![]), &value.typ, target)
        }
        ExprX::UnaryOpr(UnaryOpr::Field(op), base) => {
            let mut location = expr(base, field_base(&base.typ))?;
            location.1.push(OwnerSlot::Field(op.field.clone()));
            project(location, &value.typ, target)
        }
        _ => None,
    }
}

/// Collect vector leaf types once per input, using the same paths as live owners.
pub(super) fn vectors(
    layouts: &super::layout::Layouts,
    typ: &Typ,
    span: &crate::messages::Span,
) -> Result<std::collections::BTreeMap<OwnerPath, Typ>, VirErr> {
    fn walk(
        layouts: &super::layout::Layouts,
        typ: &Typ,
        span: &crate::messages::Span,
        path: &mut OwnerPath,
        result: &mut std::collections::BTreeMap<OwnerPath, Typ>,
    ) -> Result<(), VirErr> {
        if layouts.vector(typ) {
            result.insert(path.clone(), typ.clone());
        }
        for (slot, child) in layouts.owned_children(typ, span)? {
            path.push(slot);
            walk(layouts, &child, span, path, result)?;
            path.pop();
        }
        Ok(())
    }
    let mut result = std::collections::BTreeMap::new();
    // Validate layouts first, including the recursion guard.
    layouts.size(typ, span)?;
    walk(layouts, referent(typ), span, &mut vec![], &mut result)?;
    Ok(result)
}
