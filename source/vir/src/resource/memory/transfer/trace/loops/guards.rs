//! Partition counted iterations at stable predicate boundaries, in source order.
//!
//! Every selected program still passes the ordinary ownership composition check.
//! Stable decisions select complete programs, never byte allowances. Predicates
//! on payloads or changing collections have no closed selection map here.

use super::*;

/// A complete iteration program repeated over one ordered interval.
pub(super) struct Program {
    /// Branch-selected effects, with all guards discharged.
    pub(super) effects: Vec<Effect>,
    /// Exact interval width; all iterations take the same selected program.
    pub(super) count: Expr,
    /// First counter observation in this interval.
    pub(super) start: Expr,
    /// Stable decision selecting this whole program for the interval.
    pub(super) condition: Expr,
}

pub(super) fn partition(
    span: &Span,
    effects: &[Effect],
    binder: &VarIdent,
    start: Expr,
    count: Expr,
    stable: &HashMap<VarIdent, Expr>,
) -> Option<Vec<Vec<Program>>> {
    let mut guards = Vec::new();
    collect(effects, &mut guards, same_predicate);
    // An unconditional program already has its complete count. Preserve its
    // original expressions and avoid introducing redundant interval joins.
    if guards.is_empty() {
        return Some(vec![vec![Program {
            effects: effects.to_vec(),
            count,
            start,
            condition: crate::ast_util::mk_bool(span, true),
        }]]);
    }
    // Keep symbolic path expansion finite. Exceeding these limits is unsupported,
    // never permission to erase the relationship between choices and forests.
    if guards.len() > 6 {
        return None;
    }
    let mut cuts = Vec::new();
    for condition in &guards {
        boundaries(condition, binder, stable, &mut cuts)?;
    }
    let mut unique = Vec::new();
    for cut in cuts {
        if !unique.iter().any(|old| simplify::inspect::same_expression(old, &cut)) {
            unique.push(cut);
        }
    }
    let cuts = unique;
    if cuts.len() > 16 {
        return None;
    }
    let end = contracts::add(span, start.clone(), count);
    // Insertion sorting with min/max also handles symbolic, equal and out-of-range
    // thresholds. Clipping gives ordered nonnegative interval widths.
    let mut endpoints: Vec<Expr> = Vec::new();
    for cut in cuts {
        let mut next =
            contracts::maximum(span, start.clone(), contracts::minimum(span, end.clone(), cut));
        for point in &mut endpoints {
            let low = contracts::minimum(span, point.clone(), next.clone());
            next = contracts::maximum(span, point.clone(), next);
            *point = low;
        }
        endpoints.push(next);
    }
    endpoints.push(end);
    let mut programs = Vec::new();
    let mut low = start;
    for high in endpoints {
        let mut interval = Vec::new();
        let width = contracts::subtract(span, high.clone(), low.clone());
        let replacements = HashMap::from([(binder.clone(), low.clone())]);
        for selection in 0..(1usize << guards.len()) {
            let conditions = guards
                .iter()
                .enumerate()
                .map(|(index, guard)| {
                    let value = substitute(guard, &replacements);
                    if selection & (1 << index) != 0 {
                        value
                    } else {
                        SpannedTyped::new(span, &bool_typ(), ExprX::Unary(UnaryOp::Not, value))
                    }
                })
                .collect();
            let selected = contracts::simplify(&crate::ast_util::conjoin(span, &conditions));
            if matches!(selected.x, ExprX::Const(Constant::Bool(false)))
                || contracts::constant(&contracts::simplify(&width)) == Some(0)
            {
                continue;
            }
            let effects = select(effects, &guards, selection, same_predicate);
            interval.push(Program {
                effects,
                count: width.clone(),
                start: low.clone(),
                condition: selected,
            });
        }
        programs.push(interval);
        low = high;
    }
    Some(programs)
}

/// If every branch consumes the same ordered suffixes, membership after the
/// visit is independent of the decision. Keep reads as dependencies for an
/// enclosing loop. Appends, transfers, indexed places or unequal removals
/// require the full guarded program.
pub(super) fn common_pops(effects: &[Effect]) -> Option<(Vec<Effect>, Vec<Effect>)> {
    let mut guards = Vec::new();
    collect(effects, &mut guards, Arc::ptr_eq);
    if guards.len() > 6 {
        return None;
    }
    let mut reads = std::collections::BTreeSet::new();
    let mut common: Option<Vec<(Location, Typ)>> = None;
    for choice in 0..1 << guards.len() {
        let mut pops = Vec::new();
        for effect in select(effects, &guards, choice, Arc::ptr_eq) {
            match effect {
                Effect::Read(name) => {
                    reads.insert(name);
                }
                Effect::Pop { location, typ, .. }
                    if !location.1.iter().any(|slot| matches!(slot, OwnerSlot::Element(_))) =>
                {
                    // There are no persistent transfers in this program.
                    pops.push((location, typ));
                }
                _ => return None,
            }
        }
        if let Some(prior) = &common {
            if prior.len() != pops.len()
                || prior.iter().zip(&pops).any(|((a, _), (b, _))| a.0 != b.0 || a.1 != b.1)
            {
                return None;
            }
        } else {
            common = Some(pops);
        }
    }
    let pops = common?;
    (!pops.is_empty() && (!reads.is_empty() || !guards.is_empty())).then(|| {
        (
            reads.into_iter().map(Effect::Read).collect(),
            pops.into_iter()
                .map(|(location, typ)| Effect::Pop { location, typ, token: None })
                .collect(),
        )
    })
}

// Stable interval predicates are comparable by value. For a changing
// collection, only arms of the very same evaluation are complementary.
type CompareDecisions = fn(&Arc<Expr>, &Arc<Expr>) -> bool;

fn same_predicate(a: &Arc<Expr>, b: &Arc<Expr>) -> bool {
    simplify::inspect::same_expression(a, b)
}

fn collect(effects: &[Effect], guards: &mut Vec<Arc<Expr>>, same: CompareDecisions) {
    for effect in effects {
        if let Effect::Guarded { decision, effect, .. } = effect {
            if !guards.iter().any(|old| same(old, decision)) {
                guards.push(decision.clone());
            }
            collect(std::slice::from_ref(effect), guards, same);
        }
    }
}

fn select(
    effects: &[Effect],
    guards: &[Arc<Expr>],
    selection: usize,
    same: CompareDecisions,
) -> Vec<Effect> {
    let mut result = Vec::new();
    for effect in effects {
        if let Effect::Guarded { decision, selected, effect } = effect {
            let index = guards.iter().position(|old| same(old, decision)).unwrap();
            if (selection & (1 << index) != 0) == *selected {
                result.extend(select(std::slice::from_ref(effect), guards, selection, same));
            }
        } else {
            result.push(effect.clone());
        }
    }
    result
}

/// Stable expressions may use immutable scalar inputs. A varying comparison
/// may compare affine counter expressions with one such expression; Boolean
/// combinations inherit their finite cuts. Nonlinear and payload tests reject.
fn boundaries(
    value: &Expr,
    binder: &VarIdent,
    stable: &HashMap<VarIdent, Expr>,
    cuts: &mut Vec<Expr>,
) -> Option<()> {
    if independent(value, binder) {
        let mut valid = true;
        let _ = crate::ast_visitor::expr_visitor_check(value, &mut |_, value| {
            if let ExprX::Var(name) = &value.x {
                valid &= stable.contains_key(name);
            }
            Ok::<(), VirErr>(())
        });
        return valid.then_some(());
    }
    let span = &value.span;
    match &value.x {
        ExprX::Unary(UnaryOp::Not, operand) => boundaries(operand, binder, stable, cuts),
        ExprX::Logical(_, a, b) => {
            boundaries(a, binder, stable, cuts)?;
            boundaries(b, binder, stable, cuts)
        }
        // Short-circuit scalar evaluation produces conditional expressions.
        ExprX::If(condition, yes, Some(no)) => {
            boundaries(condition, binder, stable, cuts)?;
            boundaries(yes, binder, stable, cuts)?;
            boundaries(no, binder, stable, cuts)
        }
        ExprX::Binary(op @ (BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Inequality(_)), a, b) => {
            let direct = matches!(&a.x, ExprX::Var(name) if name == binder)
                || matches!(&b.x, ExprX::Var(name) if name == binder);
            if !direct {
                let (a_slope, a_offset) = simplify::bounds::affine(a, binder)?;
                let (b_slope, b_offset) = simplify::bounds::affine(b, binder)?;
                let slope =
                    crate::resource::memory::loops::progress::difference(&a_slope, &b_slope)?;
                if slope == 0 {
                    return None;
                }
                let intercept = contracts::subtract(span, a_offset, b_offset);
                boundaries(&intercept, binder, stable, cuts)?;
                let threshold = if slope > 0 {
                    contracts::subtract(span, expr::integer(span, 0), intercept)
                } else {
                    intercept
                };
                let magnitude = slope.checked_abs()?;
                let ceil = |value| {
                    crate::resource::memory::loops::progress::ceil_div(span, value, magnitude)
                };
                let lower = ceil(threshold.clone());
                let upper = ceil(contracts::add(span, threshold, expr::integer(span, 1)));
                match op {
                    BinaryOp::Eq(_) | BinaryOp::Ne => {
                        cuts.push(lower);
                        cuts.push(upper);
                    }
                    BinaryOp::Inequality(op) => {
                        let inclusive = matches!(
                            (slope > 0, op),
                            (true, InequalityOp::Le | InequalityOp::Gt)
                                | (false, InequalityOp::Lt | InequalityOp::Ge)
                        );
                        cuts.push(if inclusive { upper } else { lower });
                    }
                    _ => unreachable!(),
                }
                return Some(());
            }
            let (threshold, reverse) = if matches!(&a.x, ExprX::Var(name) if name == binder) {
                (b, false)
            } else {
                (a, true)
            };
            if !independent(threshold, binder) {
                return None;
            }
            boundaries(threshold, binder, stable, cuts)?;
            let successor = || contracts::add(span, threshold.clone(), expr::integer(span, 1));
            match op {
                BinaryOp::Eq(_) | BinaryOp::Ne => {
                    cuts.push(threshold.clone());
                    cuts.push(successor());
                }
                BinaryOp::Inequality(op) => {
                    let inclusive = matches!(
                        (reverse, op),
                        (false, InequalityOp::Le | InequalityOp::Gt)
                            | (true, InequalityOp::Lt | InequalityOp::Ge)
                    );
                    cuts.push(if inclusive { successor() } else { threshold.clone() });
                }
                _ => unreachable!(),
            }
            Some(())
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_common_pop_requires_complementary_arms_of_one_decision() {
        let span = Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "decisions".into(),
        };
        let name = VarIdent(Arc::new("handles".into()), VarIdentDisambiguate::VirTemp(1));
        let predicate = crate::ast_util::mk_bool(&span, true);
        let first = Arc::new(predicate.clone());
        let second = Arc::new(predicate);
        let pop = |decision, selected| Effect::Guarded {
            decision,
            selected,
            effect: Box::new(Effect::Pop {
                location: (name.clone(), Vec::new(), Vec::new()),
                typ: crate::ast_util::int_typ(),
                token: None,
            }),
        };
        assert!(common_pops(&[pop(first.clone(), true), pop(first.clone(), false)]).is_some());
        assert!(common_pops(&[pop(first, true), pop(second, false)]).is_none());
    }

    /// Compare the compact interval program with direct execution for each
    /// comparison direction, including empty, singleton and clipped intervals.
    #[test]
    fn interval_programs_preserve_comparison_selection_and_order() {
        let span = Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "intervals".into(),
        };
        let name = |value: &str| VarIdent(Arc::new(value.into()), VarIdentDisambiguate::VirTemp(1));
        let binder = name("iteration");
        let yes = name("yes");
        let no = name("no");
        let counter =
            SpannedTyped::new(&span, &crate::ast_util::int_typ(), ExprX::Var(binder.clone()));
        for (slope, offset) in [(1, 0), (2, 1), (-2, 7)] {
            let counter = simplify::simplify(&contracts::add(
                &span,
                expr::integer(&span, offset),
                contracts::multiply(&span, expr::integer(&span, slope), counter.clone()),
            ));
            for reverse in [false, true] {
                for threshold_value in [-2, 0, 2, 4, 7] {
                    for op in [
                        BinaryOp::Eq(Mode::Exec),
                        BinaryOp::Ne,
                        BinaryOp::Inequality(InequalityOp::Lt),
                        BinaryOp::Inequality(InequalityOp::Le),
                        BinaryOp::Inequality(InequalityOp::Gt),
                        BinaryOp::Inequality(InequalityOp::Ge),
                    ] {
                        let threshold = expr::integer(&span, threshold_value);
                        let (a, b) = if reverse {
                            (threshold.clone(), counter.clone())
                        } else {
                            (counter.clone(), threshold.clone())
                        };
                        let condition =
                            SpannedTyped::new(&span, &bool_typ(), ExprX::Binary(op, a, b));
                        let decision = Arc::new(condition);
                        let effects = vec![
                            Effect::Guarded {
                                decision: decision.clone(),
                                selected: true,
                                effect: Box::new(Effect::Mutation(yes.clone())),
                            },
                            Effect::Guarded {
                                decision: decision.clone(),
                                selected: false,
                                effect: Box::new(Effect::Mutation(no.clone())),
                            },
                        ];
                        let programs = partition(
                            &span,
                            &effects,
                            &binder,
                            expr::integer(&span, 0),
                            expr::integer(&span, 4),
                            &HashMap::new(),
                        )
                        .unwrap();
                        let actual: Vec<_> = programs
                            .iter()
                            .flatten()
                            .flat_map(|program| {
                                assert_eq!(program.effects.len(), 1);
                                std::iter::repeat_n(
                                    program.effects[0].root() == &yes,
                                    contracts::constant(&program.count).unwrap() as usize,
                                )
                            })
                            .collect();
                        let expected: Vec<_> = (0..4)
                            .map(|index| {
                                // Keep the oracle independent of the expression
                                // algebra used by the partitioner under test.
                                let value = slope * index + offset;
                                let (a, b) = if reverse {
                                    (threshold_value, value)
                                } else {
                                    (value, threshold_value)
                                };
                                match op {
                                    BinaryOp::Eq(_) => a == b,
                                    BinaryOp::Ne => a != b,
                                    BinaryOp::Inequality(InequalityOp::Lt) => a < b,
                                    BinaryOp::Inequality(InequalityOp::Le) => a <= b,
                                    BinaryOp::Inequality(InequalityOp::Gt) => a > b,
                                    BinaryOp::Inequality(InequalityOp::Ge) => a >= b,
                                    _ => unreachable!(),
                                }
                            })
                            .collect();
                        assert_eq!(actual, expected, "direction {reverse}, operator {op:?}");
                    }
                }
            }
        }
    }
}
