//! Instance and capacity are the two pure protocol projections of the same
//! executable receiver. Equal roots justify comparing the projections. Distinct
//! roots give no disequality, since two inputs can alias.
use super::{Binding, Bindings, Witness};
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, layout::Layouts, paths, places, shared::RootId};
use std::collections::BTreeMap;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::resource::memory) enum Issuer {
    /// Immutable formal of the enclosing resource contract.
    Input(usize),
    /// One immutable binding outside repeated visits in this execution domain.
    Fixed(u64),
    /// Canonical backing of a single Arc construction, including captured clones.
    Shared(RootId),
}

/// What the acquisition proved about the actual executable receiver.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::resource::memory) struct Issued {
    pub(in crate::resource::memory) instance: Issuer,
    /// The issued predicate equates capacities. The role_of predicate only equates identities.
    pub(in crate::resource::memory) common_limit: bool,
}

/// Only whole capture fields carry these projections into the new actor.
#[derive(Clone, Copy)]
pub(in crate::resource::memory) enum Captured {
    Receiver(Issuer),
    Holder(Issued),
}

impl Layouts {
    pub(in crate::resource::memory) fn protocol_receiver(&self, typ: &Typ) -> bool {
        matches!(&**paths::referent(typ), TypX::Datatype(dt, _, _) if self.issuer_types.contains(dt))
            && !matches!(&**typ, TypX::MutRef(_))
    }
}

impl Bindings {
    pub(in crate::resource::memory) fn issuer(&self, id: Witness) -> Option<Issuer> {
        Some(self.definitions.get(&id)?.issuer?.instance)
    }

    /// The proof is instantiated at both actual witness types. A matching
    /// concrete issuer and equal type arguments are necessary even when a
    /// nominal theorem is shared by all instantiations.
    pub(in crate::resource::memory) fn excludes(
        &self,
        left: Witness,
        other: &Bindings,
        right: Witness,
    ) -> bool {
        self.population_role(left)
            .zip(other.population_role(right))
            .is_some_and(|(a, b)| a.excludes(&b))
    }

    pub(in crate::resource::memory) fn import_receiver(&mut self, name: &VarIdent, issuer: Issuer) {
        self.receivers.insert(name.clone(), issuer);
    }
}

impl Analysis<'_> {
    pub(in crate::resource::memory) fn bind_writer_holder(
        &mut self,
        handle: &Pattern,
        source: &Place,
    ) -> Option<(Witness, VarIdent)> {
        let (w, name) = self.bind_holder(handle, None, None)?;
        if let PlaceX::Temporary(value) = &source.x
            && let ExprX::Call {
                target: CallTarget::Fun(CallTargetKind::Static, fun, _, _, _),
                args,
                post_args: None,
                body: None,
            } = &value.x
            && let Some(issuer) = self
                .layouts
                .writer_issuers
                .get(fun)
                .and_then(|i| args.get(*i))
                .and_then(|a| self.issuer_expr(a))
        {
            self.transitions.holders.definitions.get_mut(&w)?.issuer =
                Some(Issued { instance: issuer, common_limit: false })
        }
        Some((w, name))
    }

    /// Import only the phases during which the callee owned this witness. Its
    /// local binder cannot be used to open an enclosing lexical scope.
    pub(in crate::resource::memory) fn call_holders(
        &mut self,
        call: &Expr,
        args: &[Expr],
        body: Option<&crate::resource::memory::summary::BodyEffects>,
    ) -> BTreeMap<Witness, Witness> {
        let mut mapped = self.transitions.holders.forwarded(body, args);
        let Some(body) = body else { return mapped };
        for (&remote, binding) in &body.ownership.holders.definitions {
            let Some(Issued { instance: Issuer::Input(i), common_limit }) = binding.issuer else {
                continue;
            };
            if !binding.visit.as_ref().is_some_and(|visit| visit.single_visit()) {
                continue;
            }
            let Some(issuer) = args.get(i).and_then(|e| self.issuer_expr(e)) else { continue };
            let Ok(coordinates) = self.local_occurrences(&call.span) else { continue };
            let visit = self.source_visit(call.span.id, coordinates);
            let actual =
                Witness::Call(crate::resource::memory::accounting::Accounting::fresh_allocation());
            self.transitions.holders.definitions.insert(
                actual,
                Binding {
                    name: None,
                    issuer: Some(Issued { instance: issuer, common_limit }),
                    proof: binding.proof.clone(),
                    visit: Some(visit),
                },
            );
            mapped.insert(remote, actual);
        }
        mapped
    }

    pub(super) fn issuer_place(&self, place: &Place) -> Option<Issuer> {
        match &place.x {
            PlaceX::Local(name) => self.transitions.holders.receivers.get(name).copied(),
            PlaceX::Temporary(e) if places::arc_borrow_adapter(&e.typ, &place.typ) => {
                let (name, path) = paths::expr(e, &e.typ)?;
                if !path.is_empty() {
                    return None;
                }
                let id = self.heap.root(&name)?.shared?.known()?;
                self.heap.shared.fixed_issuer(id).then_some(Issuer::Shared(id))
            }
            PlaceX::Temporary(e) if crate::ast_util::types_equal(&place.typ, &e.typ) => {
                self.issuer_expr(e)
            }
            _ => None,
        }
    }

    pub(super) fn issuer_expr(&self, expr: &Expr) -> Option<Issuer> {
        match &expr.x {
            ExprX::ReadPlace(p, _) => self.issuer_place(p),
            ExprX::Var(name) => self.transitions.holders.receivers.get(name).copied(),
            _ => None,
        }
    }

    pub(in crate::resource::memory) fn capture_protocol(&self, place: &Place) -> Option<Captured> {
        let PlaceX::Local(name) = &place.x else { return None };
        if self.layouts.protocol_receiver(&place.typ) {
            return self.issuer_place(place).map(Captured::Receiver);
        }
        let proof = self.layouts.holder_proof(&place.typ)?;
        let bindings = &self.transitions.holders;
        bindings.definitions.get(&bindings.named(name, &proof)?)?.issuer.map(Captured::Holder)
    }
}
