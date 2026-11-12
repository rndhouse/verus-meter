//! Mathematical visit counts and scalar transition candidates for checked loops.
//!
//! Source assignments propose translations. The ownership evaluator validates
//! their complete body effects; the body proof separately proves every generated
//! scalar and collection-length relationship at entry and on back edges.

use super::*;
use crate::resource::memory::{contracts, metadata::expr};
use num_traits::ToPrimitive;
use std::collections::BTreeMap;

/// Erased observations of the actual execution, independent of counter spelling.
#[derive(Clone)]
pub(in super::super) struct Observation {
    /// Number of completed visits, initialized to zero and advanced on back edges.
    pub(in super::super) ordinal: Expr,
    /// Left and right observations frozen before this invocation of the loop.
    pub(in super::super) bounds: (Expr, Expr),
    /// Current scalar observations and immutable snapshots at loop entry.
    pub(in super::super) scalars: HashMap<VarIdent, (Expr, Expr)>,
}

/// Evidence published only after the complete ownership transformation succeeds.
#[derive(Clone)]
pub(in super::super) struct Evidence {
    /// Positive decrease of the source comparison's gap on each visit.
    pub(in super::super) stride: i128,
    /// Monotone logical length changes from checked iteration operations.
    pub(in super::super) lengths: BTreeMap<LocalPath, i128>,
    /// Entry observations expressible using stable body values.
    pub(in super::super) bounds: (Option<Expr>, Option<Expr>),
    /// Closed scalar initializers retained in isolated loop queries.
    pub(in super::super) scalars: BTreeMap<VarIdent, Expr>,
    /// Definitions of immutable scalar locals, closed over stable body values.
    /// Isolated queries prove and preserve these relations as ordinary invariants.
    pub(in super::super) definitions: BTreeMap<VarIdent, Expr>,
    /// Closed logical lengths before the first visit.
    pub(in super::super) entry_lengths: BTreeMap<LocalPath, Expr>,
    /// Exact checked prefix lengths, including branch-selected visit intervals.
    pub(in super::super) prefixes: BTreeMap<LocalPath, Expr>,
}

/// Cancel additive terms without inventing identities for opaque observations.
/// This also recognizes equivalent assignment groupings in checked scalar steps.
pub(in super::super) fn difference(after: &Expr, before: &Expr) -> Option<i128> {
    fn collect(
        value: &Expr,
        sign: i128,
        terms: &mut Vec<(Expr, i128)>,
        sum: &mut i128,
    ) -> Option<()> {
        if let ExprX::Const(Constant::Int(value)) = &value.x {
            *sum = sum.checked_add(sign.checked_mul(value.to_i128()?)?)?;
            return Some(());
        }
        match &value.x {
            ExprX::Binary(BinaryOp::Arith(ArithOp::Add(_)), a, b) => {
                collect(a, sign, terms, sum)?;
                collect(b, sign, terms, sum)
            }
            ExprX::Binary(BinaryOp::Arith(ArithOp::Sub(_)), a, b) => {
                collect(a, sign, terms, sum)?;
                collect(b, sign.checked_neg()?, terms, sum)
            }
            _ => {
                if let Some((_, coefficient)) = terms.iter_mut().find(|(term, _)| {
                    crate::resource::memory::transfer::simplify::same_expression(term, value)
                }) {
                    *coefficient = coefficient.checked_add(sign)?;
                } else {
                    terms.push((value.clone(), sign));
                }
                Some(())
            }
        }
    }
    let mut terms = Vec::new();
    let mut sum = 0;
    collect(after, 1, &mut terms, &mut sum)?;
    collect(before, -1, &mut terms, &mut sum)?;
    terms.iter().all(|(_, coefficient)| *coefficient == 0).then_some(sum)
}

/// Count positive gap reductions, including a partial final stride. All
/// arithmetic is mathematical; native overflow stays an executable obligation.
pub(in super::super) fn count(span: &Span, gap: Expr, stride: i128) -> Expr {
    assert!(stride > 0);
    let gap = contracts::maximum(span, expr::integer(span, 0), gap);
    if stride == 1 {
        return gap;
    }
    ceil_div(span, gap, stride)
}

/// Signed thresholds use the same integer rounding without clamping the gap.
pub(in super::super) fn ceil_div(span: &Span, value: Expr, stride: i128) -> Expr {
    assert!(stride > 0);
    let numerator = contracts::add(span, value, expr::integer(span, stride - 1));
    contracts::simplify(&SpannedTyped::new(
        span,
        &crate::ast_util::int_typ(),
        ExprX::Binary(
            BinaryOp::Arith(ArithOp::EuclideanDiv(Div0Behavior::Allow)),
            numerator,
            expr::integer(span, stride),
        ),
    ))
}

impl Control {
    /// A comparison holds precisely while its integer gap is positive.
    pub(in super::super) fn gap(&self, left: Expr, right: Expr) -> Expr {
        let span = &self.start.span;
        let gap = match self.comparison {
            InequalityOp::Lt | InequalityOp::Le => contracts::subtract(span, right, left),
            InequalityOp::Gt | InequalityOp::Ge => contracts::subtract(span, left, right),
        };
        if matches!(self.comparison, InequalityOp::Le | InequalityOp::Ge) {
            contracts::add(span, gap, expr::integer(span, 1))
        } else {
            gap
        }
    }

    /// Relative progress allows either side of the comparison to change.
    pub(in super::super) fn stride(&self, left: i128, right: i128) -> Option<i128> {
        let stride = match self.comparison {
            InequalityOp::Lt | InequalityOp::Le => left.checked_sub(right)?,
            InequalityOp::Gt | InequalityOp::Ge => right.checked_sub(left)?,
        };
        (stride > 0).then_some(stride)
    }
}

/// Propose unconditional integer translations. Conditional writes and nested
/// recurrences need their own checked closed form and are deliberately excluded.
pub(in super::super) fn scalar_steps(body: &Expr) -> HashMap<VarIdent, (Typ, i128)> {
    fn constant(value: &Expr) -> Option<i128> {
        if let ExprX::Const(Constant::Int(value)) = &value.x {
            return value.to_i128();
        }
        if let Some(Constant::Int(value)) = crate::resource::memory::model::negative_literal(value)
        {
            return value.to_i128();
        }
        None
    }
    fn translation(rhs: &Expr, name: &VarIdent) -> Option<i128> {
        if super::local(rhs).as_ref() == Some(name) {
            return Some(0);
        }
        match &rhs.x {
            ExprX::Binary(BinaryOp::Arith(ArithOp::Add(_)), a, b) => translation(a, name)
                .and_then(|step| step.checked_add(constant(b)?))
                .or_else(|| constant(a)?.checked_add(translation(b, name)?)),
            ExprX::Binary(BinaryOp::Arith(ArithOp::Sub(_)), a, b) => {
                translation(a, name)?.checked_sub(constant(b)?)
            }
            _ => None,
        }
    }
    fn visit(value: &Expr, result: &mut HashMap<VarIdent, (Typ, i128)>) {
        match &value.x {
            ExprX::Block(statements, tail) => {
                for statement in statements.iter() {
                    if let StmtX::Expr(value) = &statement.x {
                        visit(value, result);
                    }
                }
                if let Some(tail) = tail {
                    visit(tail, result);
                }
            }
            ExprX::Assign { place, rhs, op, typ, .. } => {
                let PlaceX::Local(name) = &place.x else { return };
                if !matches!(&**typ, TypX::Int(_)) {
                    return;
                }
                let delta = match op {
                    Some(BinaryOp::Arith(ArithOp::Add(_))) => constant(rhs),
                    Some(BinaryOp::Arith(ArithOp::Sub(_))) => {
                        constant(rhs).and_then(i128::checked_neg)
                    }
                    None => translation(rhs, name),
                    _ => None,
                };
                if let Some(delta) = delta {
                    let previous = result.get(name).map_or(0, |(_, delta)| *delta);
                    if let Some(delta) =
                        previous.checked_add(delta).filter(|delta| delta.checked_abs().is_some())
                    {
                        result.insert(name.clone(), (typ.clone(), delta));
                    }
                }
            }
            _ => {}
        }
    }
    let mut result = HashMap::new();
    visit(body, &mut result);
    result
}
