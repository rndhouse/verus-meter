//! Identity of the whole guard on a successful return. All reaching returns
//! must agree on its origin before a caller may substitute its own argument.
use super::{Bindings, Issuer, Role, Witness};
use crate::ast::*;
use crate::resource::memory::analysis::Analysis;

/// Empty is the identity for merging alternatives: a failed attempt supplies
/// no witness. An unrecognized success, or two different witnesses, loses
/// the relationship even when the Rust types and capacities are identical.
#[derive(Clone, Copy, Default)]
pub(super) enum Origin {
    #[default]
    Empty,
    Owned(Witness),
    Issued(Issuer),
    Unknown,
}

impl Origin {
    pub(super) fn issuer(self, bindings: &Bindings) -> Option<Issuer> {
        match self {
            Self::Issued(i) => Some(i),
            Self::Owned(w) => bindings.definitions.get(&w)?.issuer,
            _ => None,
        }
    }

    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Empty, x) | (x, Self::Empty) => x,
            (Self::Owned(a), Self::Owned(b)) if a == b => self,
            (Self::Issued(a), Self::Issued(b)) if a == b => self,
            _ => Self::Unknown,
        }
    }
}

impl Bindings {
    fn returned_input(&self, proof: &Role) -> Option<usize> {
        let Origin::Owned(id @ Witness::Input(i)) = self.returned else { return None };
        (self.definitions.get(&id)?.proof == *proof).then_some(i)
    }
}

impl Analysis<'_> {
    pub(super) fn holder_result_proof(&self, ty: &Typ) -> Option<Role> {
        let payload = match &**ty {
            TypX::Datatype(_, args, _) if self.layouts.option(ty) => args.first()?,
            _ => ty,
        };
        self.layouts.holder_proof(payload)
    }

    pub(super) fn holder_place_origin(&self, place: &Place, proof: &Role) -> Origin {
        match &place.x {
            PlaceX::Local(name) => {
                let bindings = &self.transitions.holders;
                if self.layouts.option(&place.typ) {
                    bindings.options.get(name).copied().unwrap_or(Origin::Unknown)
                } else {
                    bindings.named(name, proof).map_or(Origin::Unknown, Origin::Owned)
                }
            }
            PlaceX::Temporary(value) => self.holder_origin(value, proof),
            _ => Origin::Unknown,
        }
    }

    fn holder_origin(&self, expr: &Expr, proof: &Role) -> Origin {
        match &expr.x {
            ExprX::ReadPlace(place, kind)
                if matches!(kind.preliminary_kind, ReadKind::Move(_))
                    && crate::ast_util::types_equal(&place.typ, &expr.typ) =>
            {
                self.holder_place_origin(place, proof)
            }
            ExprX::Ctor(_, variant, fields, None) if self.layouts.option(&expr.typ) => {
                match (variant.as_str(), fields.as_slice()) {
                    ("None", []) => Origin::Empty,
                    ("Some", [f]) => self.holder_origin(&f.a, proof),
                    _ => Origin::Unknown,
                }
            }
            ExprX::Block(_, Some(tail)) => self.holder_origin(tail, proof),
            ExprX::If(_, yes, Some(no)) => {
                self.holder_origin(yes, proof).join(self.holder_origin(no, proof))
            }
            ExprX::Match(_, arms, _) => arms.iter().fold(Origin::Empty, |origin, arm| {
                origin.join(self.holder_origin(&arm.x.body, proof))
            }),
            // The exit handler independently records its actual operand. This
            // expression cannot also supply a value to the continuing path.
            ExprX::Return(_) => Origin::Empty,
            ExprX::NeverToAny(inner) => self.holder_origin(inner, proof),
            ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, fun, _, _, _),
                args,
                post_args: None,
                body: None,
            } => {
                let bindings = self
                    .summaries
                    .get(fun)
                    .and_then(|s| s.effects.as_ref())
                    .map(|body| &body.ownership.holders);
                let issuer = self.layouts.issuer_parameters.get(fun).copied().or_else(|| {
                    match bindings?.returned.issuer(bindings?)? {
                        Issuer::Input(i) => Some(i),
                        _ => None,
                    }
                });
                if let Some(issuer) =
                    issuer.and_then(|i| args.get(i)).and_then(|e| self.issuer_expr(e))
                {
                    return Origin::Issued(issuer);
                }
                let source = self
                    .summaries
                    .get(fun)
                    .and_then(|s| s.effects.as_ref())
                    .and_then(|body| body.ownership.holders.returned_input(proof))
                    .and_then(|index| args.get(index));
                source.map_or(Origin::Unknown, |arg| self.holder_origin(arg, proof))
            }
            _ => Origin::Unknown,
        }
    }

    /// Called for each reachable explicit return and once for normal fallthrough.
    pub(in crate::resource::memory) fn record_holder_return(&mut self, result: &Expr) {
        if self.layouts.holder_proofs.is_empty() {
            return;
        }
        if let Some(proof) = self.holder_result_proof(&result.typ) {
            let origin = self.holder_origin(result, &proof);
            let returned = &mut self.transitions.holders.returned;
            *returned = returned.join(origin);
        }
    }
}
