//! Locate structural owners and operation-local indexed borrows.
//!
//! References preserve the owner's path; each implicit Box dereference adds a
//! contents slot. Indexed paths identify operation-local borrowed projections,
//! materialized by `projections`; they are never persistent element identities.
//! Consumers must validate the place and find a live tracked root.

use super::heap::{OwnerPath, OwnerSlot};
use crate::ast::*;
use crate::ast_util::types_equal;

/// Local root and the child relative to that root.
pub(super) type LocalPath = (VarIdent, OwnerPath);
/// Formal parameter index and child path exported to a checked caller.
pub(super) type InputPath = (usize, OwnerPath);

pub(super) fn indexed(path: &[OwnerSlot]) -> bool {
    path.iter().any(|slot| matches!(slot, OwnerSlot::Element(_)))
}

/// Compiler-recognized indexing adapters, shared by paths and operation handling.
pub(super) fn vector_index(value: &Expr) -> Option<&Exprs> {
    let ExprX::Call {
        target: CallTarget::Fun(CallTargetKind::Static, fun, _, _, _),
        args,
        post_args: None,
        body: None,
    } = &value.x
    else {
        return None;
    };
    ((*fun == crate::fun!(CrateId::Vstd => "std_specs", "vec"; "vec_index")
        || *fun == crate::fun!(CrateId::Vstd => "std_specs", "vec"; "vec_index_mut"))
        && args.len() == 2)
        .then_some(args)
}

/// Index lowering can erase implicit Box dereferences from the result type.
/// The adapter's element argument retains the complete owning shape.
pub(super) fn indexed_type(value: &Expr) -> Option<&Typ> {
    vector_index(value)?;
    let ExprX::Call { target: CallTarget::Fun(_, _, types, _, _), .. } = &value.x else {
        unreachable!()
    };
    types.first()
}

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
        PlaceX::Index(base, _, _, BoundsCheck::Error) => {
            let mut location = self::place(base, &base.typ)?;
            location.1.push(OwnerSlot::Element(place.span.id));
            location
        }
        _ => return None,
    };
    project(location, &place.typ, target)
}

pub(super) fn expr(value: &Expr, target: &Typ) -> Option<LocalPath> {
    if let Some(args) = vector_index(value) {
        let mut location = expr(&args[0], &args[0].typ)?;
        location.1.push(OwnerSlot::Element(value.span.id));
        return project(location, indexed_type(value)?, target);
    }
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
