//! Checked loop-prefix obligations for collections of outstanding workers.

use crate::ast::*;
use crate::ast_util::{mk_eq, mk_ineq};
use crate::messages::Span;
use crate::resource::memory::{growth::Growth, metadata::expr, transfer};
use std::collections::HashMap;

/// Exact membership and its associated source observations. When the owner
/// crosses into a worker, the publishing trace specializes only the candidates.
/// The receiving loop must prove them against its real state at every boundary.
#[derive(Clone)]
pub(in super::super) struct PopulationPrefix {
    span: Span,
    body: Span,
    /// Actual records and the inferred records after the observed visit count.
    forest: (Expr, Expr),
    /// Actual and expected logical length in the receiving actor.
    length: Option<(Expr, Expr)>,
    /// Actual backing charge and its inferred upper bound.
    backing: Option<(Expr, Expr)>,
}

impl PopulationPrefix {
    pub(in super::super) fn new(
        record: &super::Loop,
        role: &super::LocalPath,
        forest: (Expr, Expr),
        length: Option<Expr>,
        backing: Option<Expr>,
    ) -> Self {
        let charge = record.charges.iter().find(|charge| &charge.location == role);
        Self {
            span: record.span.clone(),
            body: record.body.span.clone(),
            forest,
            length: length.and_then(|expected| Some((charge?.length.0.clone(), expected))),
            backing: backing.and_then(|upper| Some((charge?.backing.as_ref()?.0.clone(), upper))),
        }
    }

    pub(in super::super) fn emit(
        &self,
        growth: &mut Growth,
        captures: &HashMap<VarIdent, Expr>,
    ) -> Result<(), VirErr> {
        let span = &self.span;
        let specialize = |value: &Expr| {
            if captures.is_empty() {
                value.clone()
            } else {
                transfer::simplify::specialize(value, captures)
            }
        };
        let expected = specialize(&self.forest.1);
        let mut proofs = Vec::new();
        transfer::prove_loop_prefix(span, &expected, &mut proofs)?;
        let proof = crate::def::Spanned::new(
            span.clone(),
            StmtX::Expr(crate::ast_util::mk_block(span, proofs, None)),
        );
        growth.before_loop_proof(span, proof.clone());
        growth.before.entry(self.body.id).or_default().push(proof.clone());
        growth.after.entry(self.body.id).or_default().push(proof.clone());
        // Loop-body facts do not escape an isolated query. Instantiate the
        // same transport laws at exit before any subsequent join or drop.
        growth.after.entry(span.id).or_default().push(proof);
        let invariants = growth.loops.entry(span.id).or_default();
        invariants.push(expr::purpose(
            mk_eq(span, &self.forest.0, &expected),
            "memory worker collection membership",
        ));
        if let Some((actual, length)) = &self.length {
            invariants.push(expr::purpose(
                mk_eq(span, actual, &specialize(length)),
                "captured worker collection length",
            ));
        }
        if let Some((actual, upper)) = &self.backing {
            invariants.push(expr::purpose(
                mk_ineq(span, actual, &specialize(upper), InequalityOp::Le),
                "memory collection backing-storage bound",
            ));
        }
        Ok(())
    }
}
