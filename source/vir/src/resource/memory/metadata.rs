//! Transferable allocation forests for runtime children. Charged byte upper
//! bounds and reserved-slot lower bounds have independent meanings.

pub(super) mod expr;
pub(super) mod operations;
mod owners;
pub(super) mod profiles;
pub(super) mod reservations;

use super::analysis::Analysis;
use super::footprint::MemoryKind;
use crate::ast::*;
use crate::messages::Span;

/// Prove descriptor classification in a local proof scope. Keeping these
/// structural rewrites out of budget queries avoids unbounded matching on
/// composed forests when the requested budget is too small.
pub(super) fn runtime_shape_proof(span: &Span, records: Expr) -> Stmt {
    let group = crate::fun!(CrateId::Vstd => "std_specs", "memory"; "group_runtime_shape");
    let proofs = vec![crate::def::Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::Fuel(group, 1, true),
        )),
    )];
    let runtime = expr::operation(span, "runtime", vec![records.clone()], expr::memory_type());
    crate::def::Spanned::new(
        span.clone(),
        StmtX::Expr(SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::AssertBy {
                vars: std::sync::Arc::new(vec![]),
                require: crate::ast_util::mk_bool(span, true),
                ensure: crate::ast_util::mk_eq(span, &runtime, &records),
                proof: crate::ast_util::mk_block(span, proofs, None),
            },
        )),
    )
}

/// Which allocations a forest accounts for. The caller keeps incoming storage
/// live throughout a helper call; its body tracks only allocations added there.
/// A local view is exact for those charges, but is not a complete physical
/// forest and cannot justify exact-capacity inference. Complete transfers use
/// the checked ownership template at the caller.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum View {
    /// All modeled allocations owned by the value, including caller storage.
    #[default]
    Complete,
    /// Only charges introduced by this function; caller storage stays external.
    Local,
}

impl Analysis<'_> {
    /// Freeze before the payload expression moves its source. Caller-only
    /// aggregate geometry remains unknown rather than becoming a zero count.
    pub(super) fn freeze_owner_geometry(&mut self, value: &Expr, owner: &mut super::heap::Owner) {
        let span = &value.span;
        if let Some((typ, _)) = &owner.source {
            if self.layouts.cardinality(typ) {
                if super::projections::spec_value(value).is_ok() {
                    owner.geometry =
                        Some(self.allocation_snapshot(span, self.owner_length(span, owner)));
                    owner.geometry_known = true;
                } else {
                    // Evaluation may establish this source after the snapshot
                    // site. Retain its bytes and decline the logical count.
                    owner.geometry = None;
                    owner.geometry_known = false;
                }
            }
        }
        owner.source = None;
        for child in owner.children.values_mut() {
            self.freeze_owner_geometry(value, child);
        }
    }

    pub(super) fn prove_element_frame(
        &mut self,
        span: &Span,
        elements: &super::elements::Elements,
        original: Expr,
        parent: Expr,
        child: Expr,
    ) {
        self.growth.after.entry(span.id).or_default().push(expr::lemma(
            span,
            "runtime_presence",
            vec![original.clone(), child.clone(), parent.clone()],
        ));
        if self.growth.loop_depth == 0 {
            return;
        }
        let name = VarIdent(
            std::sync::Arc::new("$memory_framed_index".into()),
            VarIdentDisambiguate::VirTemp(super::accounting::Accounting::fresh_allocation()),
        );
        let index = SpannedTyped::new(span, &crate::ast_util::int_typ(), ExprX::Var(name.clone()));
        let path = expr::push(span, expr::path(span, []), index.clone());
        let selected = expr::subtree(span, elements.records.clone(), path.clone());
        let expected = SpannedTyped::new(
            span,
            &expr::memory_type(),
            ExprX::If(
                crate::ast_util::mk_eq(span, &parent, &path),
                child.clone(),
                Some(expr::subtree(span, original.clone(), path)),
            ),
        );
        let ensure = SpannedTyped::new(
            span,
            &crate::ast_util::bool_typ(),
            ExprX::WithTriggers {
                triggers: std::sync::Arc::new(vec![std::sync::Arc::new(vec![selected.clone()])]),
                body: crate::ast_util::mk_eq(span, &selected, &expected),
            },
        );
        let proof = crate::ast_util::mk_block(
            span,
            vec![expr::lemma(span, "runtime_frame", vec![original, child, parent, index])],
            None,
        );
        let assertion = SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::AssertBy {
                vars: std::sync::Arc::new(vec![std::sync::Arc::new(VarBinderX {
                    name,
                    a: crate::ast_util::int_typ(),
                })]),
                require: crate::ast_util::mk_bool(span, true),
                ensure,
                proof,
            },
        );
        self.growth
            .after
            .entry(span.id)
            .or_default()
            .push(crate::def::Spanned::new(span.clone(), StmtX::Expr(assertion)));
    }

    pub(super) fn loop_snapshot(&mut self, span: &Span, value: &Expr) -> Expr {
        let ExprX::Var(name) = &value.x else {
            return self.allocation_snapshot(span, value.clone());
        };
        if self.stable_scalars.contains(name)
            && self.slots.contains_key(name)
            && super::contracts::scalar(&value.typ)
        {
            return value.clone();
        }
        if let Some(snapshot) =
            self.growth.loop_entry.get(&span.id).and_then(|values| values.get(name))
        {
            return snapshot.clone();
        }
        let (snapshot, declaration) =
            expr::local(span, "loop_entry", value.typ.clone(), value.clone(), Mode::Spec);
        let StmtX::Decl { pattern, mode, els, assert_irrefutable, .. } = &declaration.x else {
            unreachable!()
        };
        let declaration = crate::def::Spanned::new(
            span.clone(),
            StmtX::Decl {
                pattern: pattern.clone(),
                mode: *mode,
                init: None,
                els: els.clone(),
                assert_irrefutable: *assert_irrefutable,
            },
        );
        self.growth.declarations.push(declaration);
        self.growth.before.entry(span.id).or_default().push(expr::assign(
            span,
            &snapshot,
            value.clone(),
        ));
        self.growth.loop_entry.entry(span.id).or_default().insert(name.clone(), snapshot.clone());
        snapshot
    }

    /// Isolated loop queries need the entry bounds themselves, not just names
    /// for entry values. Freeze the already checked resource and user invariants
    /// together; these remain ordinary entry/back-edge proof obligations.
    pub(super) fn freeze_loop_facts(
        &mut self,
        span: &Span,
        facts: Vec<Expr>,
    ) -> Result<Vec<Expr>, VirErr> {
        let mut result = Vec::new();
        for fact in facts {
            let mut has_old = false;
            crate::ast_visitor::expr_visitor_check(&fact, &mut |_, value| {
                has_old |= matches!(value.x, ExprX::Old(_));
                Ok::<(), VirErr>(())
            })?;
            if has_old {
                continue;
            }
            result.push(crate::ast_visitor::map_expr_visitor_env(
                &fact,
                &mut air::scope_map::ScopeMap::new(),
                self,
                &|analysis, scope, value| {
                    if let ExprX::Var(name) = &value.x {
                        if !scope.contains_key(name) {
                            return Ok(analysis.loop_snapshot(span, value));
                        }
                    }
                    Ok(value.clone())
                },
                &|_, _, statement| Ok(vec![statement.clone()]),
                &|_, typ| Ok(typ.clone()),
                &|analysis, scope, place| {
                    if let PlaceX::Local(name) = &place.x {
                        if !scope.contains_key(name) {
                            let value = SpannedTyped::new(
                                &place.span,
                                &place.typ,
                                ExprX::Var(name.clone()),
                            );
                            let snapshot = analysis.loop_snapshot(span, &value);
                            let ExprX::Var(name) = &snapshot.x else { unreachable!() };
                            return Ok(SpannedTyped::new(
                                &place.span,
                                &place.typ,
                                PlaceX::Local(name.clone()),
                            ));
                        }
                    }
                    Ok(place.clone())
                },
                &|_, _, pattern| Ok(pattern.clone()),
            )?);
        }
        Ok(result)
    }

    pub(super) fn metadata_local(&mut self, span: &Span, name: &str, initial: Expr) -> Expr {
        if self.growth.metadata_scopes.insert(span.id) {
            let mut groups = vec![
                crate::fun!(CrateId::Vstd => "seq"; "group_seq_axioms"),
                crate::fun!(CrateId::Vstd => "std_specs", "memory"; "group_metadata_algebra"),
            ];
            if self.growth.loop_depth > 0 {
                groups.push(crate::fun!(CrateId::Vstd => "std_specs", "memory"; "group_metadata_loop_algebra"));
            }
            for group in groups {
                let activation = SpannedTyped::new(
                    span,
                    &crate::ast_util::unit_typ(),
                    ExprX::Fuel(group, 1, true),
                );
                self.growth
                    .before
                    .entry(span.id)
                    .or_default()
                    .push(crate::def::Spanned::new(span.clone(), StmtX::Expr(activation)));
            }
        }
        let empty = if matches!(&*initial.typ, TypX::Int(_)) {
            expr::integer(span, 0)
        } else {
            expr::empty(span, expr::record_type())
        };
        let (value, declaration) = expr::local(span, name, initial.typ.clone(), empty, Mode::Spec);
        self.growth.declarations.push(declaration);
        self.growth.before.entry(span.id).or_default().push(expr::assign(span, &value, initial));
        value
    }

    pub(super) fn enable_loop_metadata(&mut self, span: &Span) {
        let activation = SpannedTyped::new(
            span,
            &crate::ast_util::unit_typ(),
            ExprX::Fuel(
                crate::fun!(CrateId::Vstd => "std_specs", "memory"; "group_metadata_loop_algebra"),
                1,
                true,
            ),
        );
        self.growth
            .before
            .entry(span.id)
            .or_default()
            .push(crate::def::Spanned::new(span.clone(), StmtX::Expr(activation)));
    }

    pub(super) fn metadata_cost(&self, span: &Span, records: Expr, kind: &MemoryKind) -> Expr {
        // Current built-in adapters all allocate host heap storage. Keep this
        // boundary explicit rather than silently reclassifying other domains.
        assert_eq!(*kind, MemoryKind::host_heap());
        expr::cost(span, records, expr::integer(span, 0))
    }

    pub(super) fn metadata_partition(&mut self, span: &Span, records: Expr, path: Expr) {
        self.growth.before.entry(span.id).or_default().push(expr::lemma(
            span,
            "inspect",
            vec![records.clone(), path.clone()],
        ));
        self.growth.before.entry(span.id).or_default().push(expr::lemma(
            span,
            "cost_partition",
            vec![records, path, expr::integer(span, 0)],
        ));
    }

    pub(super) fn prepare_element_loop(&mut self, span: &Span, body: &Expr) -> Result<(), VirErr> {
        let mut opaque = false;
        let mut transfers = false;
        crate::ast_visitor::expr_visitor_check(body, &mut |_, expression| {
            if let ExprX::Call { target: CallTarget::Fun(_, fun, _, _, _), .. } = &expression.x {
                if let Some(summary) = self.summaries.get(fun) {
                    transfers |= summary.transfer.is_some();
                    let effects = !summary.allocations.collections.is_empty()
                        || !summary.allocations.children.is_empty()
                        || !summary.vectors.removals.is_empty();
                    opaque |= effects
                        && summary.transfer.as_ref().is_none_or(|template| template.appends);
                }
            }
            Ok::<(), VirErr>(())
        })?;
        if opaque {
            return Err(super::model::unsupported(
                span,
                "loop-carried helper effects without precise allocation metadata",
            ));
        }
        if !transfers {
            return Ok(());
        }
        self.growth.transfer_loops.insert(span.id);
        for owner in self.heap.owners.values().chain(self.heap.borrowed.values()) {
            owner.visit(&mut |node| {
                if let Some(elements) = &node.elements {
                    if elements.precise {
                        self.growth
                            .before
                            .entry(span.id)
                            .or_default()
                            .push(runtime_shape_proof(span, elements.records.clone()));
                        self.growth
                            .after
                            .entry(body.span.id)
                            .or_default()
                            .push(runtime_shape_proof(&body.span, elements.records.clone()));
                    }
                }
            });
        }
        Ok(())
    }

    pub(super) fn element_metadata_invariants(&self, span: &Span) -> Vec<Expr> {
        let mut invariants = Vec::new();
        for owner in self.heap.owners.values().chain(self.heap.borrowed.values()) {
            owner.visit(&mut |node| {
                if let Some(elements) = &node.elements {
                    if elements.precise {
                        if self.growth.transfer_loops.contains(&span.id) {
                            invariants.push(crate::ast_util::mk_eq(
                                span,
                                &expr::operation(
                                    span,
                                    "runtime",
                                    vec![elements.records.clone()],
                                    expr::memory_type(),
                                ),
                                &elements.records,
                            ));
                        }
                        invariants.push(expr::operation(
                            span,
                            "well_formed",
                            vec![elements.records.clone()],
                            crate::ast_util::bool_typ(),
                        ));
                        for (kind, id) in &elements.states {
                            invariants.push(crate::ast_util::mk_eq(
                                span,
                                &self.growth.elements[*id].bytes,
                                &self.metadata_cost(span, elements.records.clone(), kind),
                            ));
                        }
                    }
                }
            });
        }
        invariants
    }

    /// A non-growing forest can use its entry charge as an inductive ceiling.
    /// This is a candidate invariant: Verus proves it on every back edge.
    /// Direct append loops keep the existing length/count induction instead.
    pub(super) fn element_loop_bounds(
        &mut self,
        span: &Span,
        body: &Expr,
    ) -> Result<Vec<Expr>, VirErr> {
        let mut appends = std::collections::HashSet::new();
        crate::ast_visitor::expr_visitor_check(body, &mut |_, expression| {
            if let ExprX::Call { target: CallTarget::Fun(_, _, _, _, attrs), args, .. } =
                &expression.x
            {
                if attrs.resource_intrinsic == Some(ResourceIntrinsic::VecPush) {
                    if let Some(receiver) = args.first() {
                        if let Some(location) =
                            super::paths::expr(receiver, super::paths::referent(&receiver.typ))
                        {
                            appends.insert(location);
                        }
                    }
                }
            }
            Ok::<(), VirErr>(())
        })?;
        let mut counters = Vec::new();
        for (name, owner) in self.heap.owners.iter().chain(self.heap.borrowed.iter()) {
            owner.visit_paths(&mut vec![], &mut |path, node| {
                if !appends.contains(&(name.clone(), path.clone())) {
                    if let Some(elements) = &node.elements {
                        if elements.precise {
                            counters.extend(
                                elements
                                    .states
                                    .values()
                                    .map(|id| self.growth.elements[*id].bytes.clone()),
                            );
                        }
                    }
                }
            });
        }
        Ok(counters
            .into_iter()
            .map(|bytes| {
                let ceiling = self.loop_snapshot(span, &bytes);
                crate::ast_util::mk_ineq(span, &bytes, &ceiling, InequalityOp::Le)
            })
            .collect())
    }

    pub(super) fn metadata_path(&mut self, span: &Span, index: Expr) -> Result<Expr, VirErr> {
        let index = SpannedTyped::new(span, &crate::ast_util::int_typ(), index.x.clone());
        let snapshot = self.allocation_snapshot(span, index);
        Ok(expr::push(span, expr::path(span, []), snapshot))
    }

    pub(super) fn metadata_sum(&self, span: &Span, records: Expr) -> Expr {
        self.metadata_cost(span, records, &MemoryKind::host_heap())
    }
}
