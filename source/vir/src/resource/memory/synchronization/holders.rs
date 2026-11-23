//! Relate source allocation observations to intact, owned protocol witnesses.
//! Each binder identifies an executable value in its actor and visit. Applying
//! a population bound additionally requires its theorem and instance identity.

use super::super::{accounting::Accounting, layout::Layouts};
use crate::{
    ast::*,
    ast_visitor::{AstVisitor, NoScoper, Walk},
    messages::Span,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

/// A binder is meaningful only within its checked actor and execution visit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(in super::super) enum Witness {
    Input(usize),
    Local(crate::messages::AstId),
    /// Field of the worker's actual closure environment, frozen at construction.
    Capture(super::super::closures::observations::EnvironmentId, usize),
}

struct Binding {
    name: VarIdent,
    proof: Fun,
    /// Present for locals, whose births must be instantiated at each visit.
    visit: Option<super::super::workers::SourceVisit<crate::messages::AstId>>,
}

#[derive(Default)]
pub(in super::super) struct Bindings {
    definitions: BTreeMap<Witness, Binding>,
    /// Only the checked entry of the function or selected match arm opens these scopes.
    entries: BTreeMap<crate::messages::AstId, (Expr, BTreeSet<Witness>)>,
}

impl Layouts {
    fn holder_proof(&self, ty: &Typ) -> Option<&Fun> {
        let TypX::Datatype(dt, args, _) = &**ty else { return None };
        if !args.is_empty() {
            return None;
        }
        self.holder_proofs.get(dt)
    }
}

impl Bindings {
    pub(in super::super) fn bind(function: &Function, layouts: &Layouts) -> Self {
        let mut bindings = Self::default();
        let Some(body) = &function.x.body else { return bindings };
        for (index, param) in function.x.params.iter().enumerate() {
            if param.x.mode == Mode::Exec
                && !param.x.user_mut
                && let Some(proof) = layouts.holder_proof(&param.x.typ)
            {
                let id = Witness::Input(index);
                bindings.definitions.insert(
                    id,
                    Binding { name: param.x.name.clone(), proof: proof.clone(), visit: None },
                );
                bindings.at_entry(body, id);
            }
        }
        bindings
    }

    fn at_entry(&mut self, block: &Expr, id: Witness) {
        self.entries
            .entry(block.span.id)
            .or_insert_with(|| (block.clone(), BTreeSet::new()))
            .1
            .insert(id);
    }

    pub(in super::super) fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    pub(in super::super) fn valid_for(
        &self,
        id: Witness,
        actor: Option<super::super::workers::WorkerId>,
    ) -> bool {
        self.definitions.get(&id).is_some_and(|binding| match (id, &binding.visit) {
            (Witness::Local(site), Some(visit)) => site == visit.site && visit.valid_for(actor),
            (Witness::Input(_), None) => actor.is_none(),
            (Witness::Capture(_, _), Some(visit)) => actor.is_some() && visit.valid_for(actor),
            _ => false,
        })
    }

    /// Rust and Verus must accept a whole move before a callee can own the
    /// argument. Substitute its actual named binding, even if the caller and
    /// callee place the same protocol type in different argument positions.
    pub(in super::super) fn forwarded(
        &self,
        callee: Option<&super::super::summary::BodyEffects>,
        args: &[Expr],
    ) -> BTreeMap<Witness, Witness> {
        let mut actuals = BTreeMap::new();
        let Some(callee) = callee else { return actuals };
        for (id, binding) in &callee.ownership.holders.definitions {
            let Witness::Input(i) = id else { continue };
            let ExprX::ReadPlace(place, kind) = &args[*i].x else { continue };
            let PlaceX::Local(name) = &place.x else { continue };
            if !matches!(kind.preliminary_kind, ReadKind::Move(_)) {
                continue;
            }
            if let Some((actual, _)) =
                self.definitions.iter().find(|(_, b)| b.name == *name && b.proof == binding.proof)
            {
                actuals.insert(*id, *actual);
            }
        }
        actuals
    }

    pub(in super::super) fn enter(&self, block: &Expr) -> Scope {
        let mut scope = Scope::default();
        if let Some((entry, ids)) = self.entries.get(&block.span.id)
            && Arc::ptr_eq(block, entry)
        {
            for id in ids {
                scope.0.push((*id, self.definitions[id].name.clone()));
            }
        }
        scope
    }
}

impl super::super::analysis::Analysis<'_> {
    /// A moved closure field supplies the identity of a candidate. Its first
    /// whole move into a checked callee establishes intactness. Runtime capture
    /// layout alone cannot prove that the tracked fields are still available.
    pub(in super::super) fn bind_holder_capture(
        &mut self,
        name: &VarIdent,
        capture: &super::super::concurrency::Capture,
        environment: super::super::closures::observations::EnvironmentId,
        index: usize,
        site: crate::messages::AstId,
    ) {
        if capture.mode != super::super::concurrency::CaptureMode::Move
            || !capture.projection.is_empty()
            || !crate::ast_util::types_equal(&capture.source_typ, &capture.typ)
        {
            return;
        }
        let Some(proof) = self.layouts.holder_proof(&capture.typ) else { return };
        let visit = self.source_visit(site, vec![]);
        self.transitions.holders.definitions.insert(
            Witness::Capture(environment, index),
            Binding { name: name.clone(), proof: proof.clone(), visit: Some(visit) },
        );
    }

    /// Called only after the source binding was initialized by accounting. A
    /// missing loop coordinate loses precision without changing byte accounting.
    pub(in super::super) fn bind_holder(
        &mut self,
        pattern: &Pattern,
        arm: Option<&Expr>,
    ) -> Option<(Witness, VarIdent)> {
        let PatternX::Var(b) = &pattern.x else { return None };
        if b.user_mut != Some(false)
            || !matches!(b.by_ref, ByRef::No)
            || self.var_modes.get(&b.name) != Some(&Mode::Exec)
        {
            return None;
        }
        let proof = self.layouts.holder_proof(&b.typ)?.clone();
        // Never associate a borrowed iteration item or an uninitialized scratch slot.
        if self.growth.implicit_collection_loop_slots.contains(&b.name)
            || self.growth.iterator_item_slots.contains(&b.name)
        {
            return None;
        }
        let site = pattern.span.id;
        let visit = self.source_visit(site, self.local_occurrences(&pattern.span).ok()?);
        let id = Witness::Local(site);
        let bindings = &mut self.transitions.holders;
        bindings
            .definitions
            .insert(id, Binding { name: b.name.clone(), proof, visit: Some(visit) });
        if let Some(arm) = arm {
            bindings.at_entry(arm, id);
        }
        Some((id, b.name.clone()))
    }
}

/// An untouched owned binding stays intact while unrelated statements execute.
/// Stop before its first possible use, including an erased or partial move.
/// Outer frame witnesses are never installed in a spawned body's ledger.
#[derive(Default)]
pub(in super::super) struct Scope(Vec<(Witness, VarIdent)>);

impl AstVisitor<Walk, std::convert::Infallible, NoScoper> for Scope {
    fn visit_expr(&mut self, expr: &Expr) -> Result<(), std::convert::Infallible> {
        match &expr.x {
            // Borrowing the whole value through a shared reference keeps the
            // owner intact. The reference itself never becomes another witness.
            ExprX::ReadPlace(place, kind)
                if matches!(place.x, PlaceX::Local(_))
                    && matches!(kind.preliminary_kind, ReadKind::ImmutBor)
                    && matches!(&*expr.typ, TypX::Decorate(TypDecoration::Ref, None, ty)
                    if crate::ast_util::types_equal(ty, &place.typ)) =>
            {
                return Ok(());
            }
            ExprX::Var(name) | ExprX::VarAt(name, _) => self.0.retain(|(_, n)| n != name),
            // Closure construction can move an implicit capture. Control exits
            // may start cleanup within the statement.
            ExprX::NonSpecClosure { .. } | ExprX::Return(_) | ExprX::BreakOrContinue { .. } => {
                self.0.clear()
            }
            _ => {}
        }
        if self.0.is_empty() { Ok(()) } else { self.visit_expr_rec(expr) }
    }

    fn visit_place(&mut self, place: &Place) -> Result<(), std::convert::Infallible> {
        if let PlaceX::Local(name) = &place.x {
            self.0.retain(|(_, n)| n != name);
        }
        self.visit_place_rec(place)
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), std::convert::Infallible> {
        self.visit_stmt_rec(stmt)
    }

    fn visit_pattern(&mut self, _pattern: &Pattern) -> Result<(), std::convert::Infallible> {
        Ok(())
    }
    fn visit_typ(&mut self, _typ: &Typ) -> Result<(), std::convert::Infallible> {
        Ok(())
    }
}

impl Scope {
    pub(in super::super) fn initialized(&mut self, holder: Option<(Witness, VarIdent)>) {
        self.0.extend(holder);
    }

    pub(in super::super) fn before_statement(
        &mut self,
        stmt: &Stmt,
        before_implicit_cleanup: bool,
        storage: &mut Accounting,
    ) -> Result<usize, VirErr> {
        let start = storage.points().len();
        if !self.0.is_empty() {
            let previous = self.0.len();
            if before_implicit_cleanup {
                self.0.clear();
            } else {
                self.visit_stmt(stmt).unwrap();
            }
            if self.0.len() != previous {
                // Release itself need not allocate. Observe all surviving storage
                // before evaluating the statement that may consume this witness.
                // A statement wrapping an expression has its own AST id, but
                // its expression is the executable attachment site for a byte proof.
                let span = match &stmt.x {
                    StmtX::Expr(e) => &e.span,
                    StmtX::Decl { .. } => &stmt.span,
                };
                storage.record_live(span)?;
            }
        }
        Ok(start)
    }

    pub(in super::super) fn mark(&self, start: usize, storage: &mut Accounting) {
        if !self.0.is_empty() {
            storage.mark_holders(start, &self.0.iter().map(|(i, _)| *i).collect::<Vec<_>>());
        }
    }

    /// A tail may transfer a value to the caller. End local coverage at the
    /// actual tail expression, where the current byte terms are still in scope.
    pub(in super::super) fn finish(
        &self,
        span: &Span,
        storage: &mut Accounting,
    ) -> Result<(), VirErr> {
        if !self.0.is_empty() {
            storage.record_live(span)?;
        }
        Ok(())
    }
}
