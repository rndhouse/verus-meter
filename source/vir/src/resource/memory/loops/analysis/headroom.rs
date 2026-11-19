//! Preserve stable branch conditions when carrying a visit's local costs to
//! the loop head. Every operation still checks its full cost at its own site.

use super::Loop;
use crate::ast::*;
use crate::ast_util::mk_ineq;
use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
use crate::resource::memory::{contracts, footprint::Footprint, for_loops::ForLoop};
use std::collections::{HashMap, HashSet};
use std::convert::Infallible;

/// Each source site belongs to its enclosing stable path. A guard depending on
/// an item or a mutable local cannot be tested at entry, so its arms share the
/// parent's reservation.
struct Guards<'a> {
    /// Immutable scalars already in scope at this loop head.
    stable: &'a HashSet<VarIdent>,
    /// Conjunction of branch predicates for each distinct path.
    paths: Vec<Expr>,
    /// Source node to enclosing path, shared with the accounting cost sites.
    sites: HashMap<u64, usize>,
    /// Path of the node being visited, with zero denoting any successful visit.
    current: usize,
}

impl Guards<'_> {
    fn site(&mut self, id: u64) {
        // Lowered nodes can share an identity. Keep a shared site's charge
        // unconditional if its occurrences have different guards.
        self.sites
            .entry(id)
            .and_modify(|path| {
                if *path != self.current {
                    *path = 0;
                }
            })
            .or_insert(self.current);
    }

    fn arm(&mut self, body: &Expr, predicate: Expr) -> Result<(), Infallible> {
        let parent = self.current;
        self.current = self.paths.len();
        self.paths.push(predicate.new_x(ExprX::Logical(
            LogicalOp::And,
            self.paths[parent].clone(),
            predicate.clone(),
        )));
        self.visit_expr(body)?;
        self.current = parent;
        Ok(())
    }
}

impl AstVisitor<Walk, Infallible, NoScoper> for Guards<'_> {
    fn visit_expr(&mut self, expr: &Expr) -> Result<(), Infallible> {
        self.site(expr.span.id);
        if let ExprX::If(cond, yes, no) = &expr.x
            && let Ok(predicate) = contracts::predicate(cond, self.stable)
        {
            self.visit_expr(cond)?;
            self.arm(yes, predicate.clone())?;
            if let Some(no) = no {
                self.arm(no, predicate.new_x(ExprX::Unary(UnaryOp::Not, predicate.clone())))?;
            }
            return Ok(());
        }
        self.visit_expr_rec(expr)
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), Infallible> {
        self.site(stmt.span.id);
        self.visit_stmt_rec(stmt)
    }

    fn visit_place(&mut self, place: &Place) -> Result<(), Infallible> {
        self.site(place.span.id);
        self.visit_place_rec(place)
    }

    fn visit_pattern(&mut self, pattern: &Pattern) -> Result<(), Infallible> {
        self.site(pattern.span.id);
        self.visit_pattern_rec(pattern)
    }

    fn visit_typ(&mut self, _: &Typ) -> Result<(), Infallible> {
        Ok(())
    }
}

impl Loop {
    /// Carry the maximum measurable overlap on each stable path. Costs outside
    /// the source body use the common successful-visit guard.
    pub(super) fn iterator_headroom(
        &self,
        iterator: &ForLoop,
        stable: &HashSet<VarIdent>,
        heap: &Expr,
        bound: &Expr,
        measure: impl Fn(&Footprint) -> Option<u64>,
    ) -> Vec<Expr> {
        let span = &self.span;
        let mut guards = Guards {
            stable,
            paths: vec![iterator.nonempty(span)],
            sites: HashMap::new(),
            current: 0,
        };
        let Ok(()) = guards.visit_expr(&self.body);
        let mut maxima = vec![None; guards.paths.len()];
        for (site, cost) in &self.local_costs {
            if let Some(bytes) = measure(cost) {
                let path = guards.sites.get(&site.id).copied().unwrap_or(0);
                maxima[path] = maxima[path].max(Some(bytes));
            }
        }
        guards
            .paths
            .into_iter()
            .zip(maxima)
            .filter_map(|(guard, bytes)| {
                let cost = contracts::add(span, heap.clone(), contracts::literal(span, bytes?));
                let fits = mk_ineq(span, &cost, bound, InequalityOp::Le);
                Some(crate::ast_util::mk_implies(span, &guard, &fits))
            })
            .collect()
    }
}
