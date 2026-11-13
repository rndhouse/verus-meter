//! Turn completed transfer summaries into inductive bounds and headroom checks.
//!
//! Evidence supplies proof candidates; entry assertions and loop invariants
//! must establish the reserved temporary and retained allocation allowance.

use super::super::{Loop, Transfer};
use crate::ast::*;
use crate::resource::memory::{analysis::Analysis, contracts, footprint, metadata, model, paths};

impl Analysis<'_> {
    /// Completed summary evidence becomes ordinary inductive proof candidates.
    /// Failed or partial inference cannot modify the body proof state.
    pub(in crate::resource::memory) fn apply_loop_evidence(
        &mut self,
        loops: &std::collections::HashMap<u64, Vec<Transfer>>,
        growth: &std::collections::HashMap<u64, Vec<(paths::LocalPath, Expr)>>,
        scratch: &std::collections::HashMap<u64, Expr>,
        repetitions: &std::collections::HashMap<u64, Expr>,
    ) -> Result<(), VirErr> {
        for (id, transfers) in loops {
            let record = self.transitions.loops[id].clone();
            self.growth.loops.entry(*id).or_default().extend(record.conservation(transfers));
            if transfers.iter().any(|transfer| transfer.additional.is_some()) {
                let mut additions = std::collections::BTreeMap::new();
                for transfer in transfers {
                    if let Some(amount) = &transfer.additional {
                        additions
                            .entry(transfer.target)
                            .and_modify(|old: &mut Expr| {
                                *old =
                                    contracts::maximum(&record.span, old.clone(), amount.clone());
                            })
                            .or_insert_with(|| amount.clone());
                    }
                }
                let amount = additions
                    .into_values()
                    .fold(contracts::literal(&record.span, 0), |sum, amount| {
                        contracts::add(&record.span, sum, amount)
                    });
                self.reserve_loop_headroom(&record, amount, scratch.get(id))?;
            }
        }
        for (id, allowance) in repetitions {
            let record = self.transitions.loops[id].clone();
            let sum = |entry: bool| {
                record.charges.iter().fold(contracts::literal(&record.span, 0), |sum, charge| {
                    let mut amount =
                        if entry { charge.entry.clone() } else { charge.current.clone() };
                    if let Some((current, initial)) = &charge.backing {
                        amount = contracts::add(
                            &record.span,
                            amount,
                            if entry { initial.clone() } else { current.clone() },
                        );
                    }
                    contracts::add(&record.span, sum, amount)
                })
            };
            let mut upper = sum(true);
            if contracts::constant(allowance) != Some(0) {
                let (completed, entry) = record.completed.clone().ok_or_else(|| {
                    model::unsupported(
                        &record.span,
                        "allocation growth without a checked iteration progress observation",
                    )
                })?;
                self.growth.loops.entry(*id).or_default().extend([
                    crate::ast_util::mk_ineq(
                        &record.span,
                        &contracts::literal(&record.span, 0),
                        &entry,
                        InequalityOp::Le,
                    ),
                    crate::ast_util::mk_ineq(
                        &record.span,
                        &contracts::literal(&record.span, 0),
                        &completed,
                        InequalityOp::Le,
                    ),
                ]);
                upper = contracts::add(
                    &record.span,
                    upper,
                    contracts::multiply(&record.span, allowance.clone(), completed),
                );
                self.reserve_loop_headroom(&record, allowance.clone(), scratch.get(id))?;
            }
            self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                &record.span,
                &sum(false),
                &upper,
                InequalityOp::Le,
            ));
        }
        for (id, bounds) in growth {
            let record = &self.transitions.loops[id];
            let mut envelopes = std::collections::BTreeMap::<_, Expr>::new();
            for (location, amount) in bounds {
                envelopes
                    .entry(location)
                    .and_modify(|old| {
                        *old = contracts::maximum(&record.span, old.clone(), amount.clone());
                    })
                    .or_insert_with(|| amount.clone());
            }
            for (location, amount) in envelopes {
                // These append envelopes describe owning children. Scalar
                // vector backing follows its existing growth policy; its new
                // snapshot is needed only by the ordered recurrence's sum.
                if let Some(charge) = record.charges.iter().find(|charge| {
                    &charge.location == location && contracts::constant(&charge.current) != Some(0)
                }) {
                    // Isolated loop queries do not retain the executable
                    // length's type bound for an erased integer snapshot.
                    self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                        &record.span,
                        &contracts::literal(&record.span, 0),
                        &charge.length.1,
                        InequalityOp::Le,
                    ));
                    // A positive prefix of a block costs at most the whole
                    // block. This pointwise envelope remains valid before an
                    // inner loop; exported forests retain the exact tiled cost.
                    let added = contracts::multiply(
                        &record.span,
                        amount.clone(),
                        contracts::subtract(
                            &record.span,
                            charge.length.0.clone(),
                            charge.length.1.clone(),
                        ),
                    );
                    let upper = contracts::add(&record.span, charge.entry.clone(), added);
                    self.growth.loops.entry(*id).or_default().push(crate::ast_util::mk_ineq(
                        &record.span,
                        &charge.current,
                        &upper,
                        InequalityOp::Le,
                    ));
                    self.growth
                        .loops
                        .entry(*id)
                        .or_default()
                        .extend(charge.append_backing(&record.span));
                }
            }
        }
        for (id, record) in &self.transitions.loops {
            self.growth.loops.entry(*id).or_default().extend(record.element_facts.iter().cloned());
        }
        self.inherit_loop_entries()
    }

    /// Reserve temporary and retained headroom using ordinary entry checks and
    /// inductive invariants, shared by disjoint and evolving loop summaries.
    fn reserve_loop_headroom(
        &mut self,
        record: &Loop,
        amount: Expr,
        scratch: Option<&Expr>,
    ) -> Result<(), VirErr> {
        let visits = record
            .visits_bound
            .clone()
            .unwrap_or_else(|| contracts::literal(&record.span, record.size_ceiling.unwrap_or(0)));
        if contracts::constant(&amount).is_none() {
            // Ordinary queries treat general multiplication as uninterpreted.
            // Supply pointwise order and successor facts for this envelope.
            self.growth.before.entry(record.span.id).or_default().push(metadata::expr::lemma(
                &record.span,
                "product_bounds",
                vec![amount.clone(), contracts::literal(&record.span, 0), visits.clone()],
            ));
            if let Some(observation) = &record.progress {
                self.growth.before.entry(record.body.span.id).or_default().push(
                    metadata::expr::lemma(
                        &record.body.span,
                        "product_bounds",
                        vec![amount.clone(), observation.ordinal.clone(), visits.clone()],
                    ),
                );
            }
        }
        let reserve = contracts::multiply(&record.span, amount, visits);
        let call_ceiling = scratch.cloned().unwrap_or_else(|| contracts::literal(&record.span, 0));
        let mut local_peak = contracts::literal(&record.span, 0);
        for cost in &record.local_costs {
            // Body-local scalar aliases do not exist at the loop head.
            // Their helper allowances use checked iteration ceilings;
            // explicit layout charges and stable bounds stay unchanged.
            let cost = cost.map(&record.span, &|amount| {
                        let stable = crate::ast_visitor::expr_visitor_check(amount, &mut |scope, value| {
                            if matches!(&value.x, ExprX::Var(name) if !scope.contains_key(name) && !record.proof_scalars.contains(name)) { Err(()) } else { Ok(()) }
                        }).is_ok();
                        Ok(if stable { amount.clone() } else { call_ceiling.clone() })
                    })?;
            let selected = cost.select(
                &record.span,
                &footprint::MemorySelection::kind(footprint::MemoryKind::host_local()),
            );
            local_peak = contracts::maximum(&record.span, local_peak, selected);
        }
        let reserve = contracts::add(&record.span, reserve, local_peak);
        let candidates = record
            .entry_headroom
            .iter()
            .map(|candidate| {
                let ExprX::Binary(BinaryOp::Inequality(InequalityOp::Le), live, bound) =
                    &candidate.x
                else {
                    unreachable!()
                };
                crate::ast_util::mk_ineq(
                    &record.span,
                    &contracts::add(&record.span, live.clone(), reserve.clone()),
                    bound,
                    InequalityOp::Le,
                )
            })
            .collect();
        let facts = self.freeze_loop_facts(&record.span, candidates)?;
        for fact in &facts {
            let check = SpannedTyped::new(
                &record.span,
                &crate::ast_util::unit_typ(),
                ExprX::AssertAssume {
                    is_assume: false,
                    expr: fact.clone(),
                    msg: Some(crate::messages::error(
                        &record.span,
                        "memory budget exceeded: cannot reserve heap headroom for loop allocations",
                    )),
                },
            );
            self.growth
                .before
                .entry(record.span.id)
                .or_default()
                .push(crate::def::Spanned::new(record.span.clone(), StmtX::Expr(check)));
        }
        self.growth.loops.entry(record.span.id).or_default().extend(facts);
        Ok(())
    }
}
