//! Identify proof sites whose entire evaluation preserves the worker count.
//! Checks can run before or after operands. At a compound site containing a
//! publication or collection, use the independently proved population ceiling.

use crate::ast::*;
use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
use crate::messages::AstId;
use std::collections::{BTreeMap, HashSet};
use std::convert::Infallible;

pub(super) fn stable_sites<T>(
    body: &Expr,
    spawn: AstId,
    joins: &BTreeMap<AstId, T>,
) -> HashSet<AstId> {
    let mut sites = Sites {
        transitions: joins.keys().copied().chain([spawn]).collect(),
        visited: 0,
        stable: HashSet::new(),
        changing: HashSet::new(),
    };
    sites.visit_expr(body).unwrap();
    sites.stable.retain(|id| !sites.changing.contains(id));
    sites.stable
}

struct Sites {
    transitions: HashSet<AstId>,
    visited: usize,
    stable: HashSet<AstId>,
    changing: HashSet<AstId>,
}

impl Sites {
    fn record(&mut self, site: AstId, entry: usize) {
        if entry == self.visited {
            self.stable.insert(site);
        } else {
            self.changing.insert(site);
        }
    }
}

impl AstVisitor<Walk, Infallible, NoScoper> for Sites {
    fn visit_expr(&mut self, e: &Expr) -> Result<(), Infallible> {
        let entry = self.visited;
        self.visited += usize::from(self.transitions.contains(&e.span.id));
        if !matches!(e.x, ExprX::NonSpecClosure { .. }) {
            self.visit_expr_rec(e)?;
        }
        self.record(e.span.id, entry);
        Ok(())
    }

    fn visit_stmt(&mut self, s: &Stmt) -> Result<(), Infallible> {
        let entry = self.visited;
        self.visit_stmt_rec(s)?;
        self.record(s.span.id, entry);
        Ok(())
    }

    fn visit_place(&mut self, p: &Place) -> Result<(), Infallible> {
        let entry = self.visited;
        self.visit_place_rec(p)?;
        self.record(p.span.id, entry);
        Ok(())
    }

    fn visit_typ(&mut self, _: &Typ) -> Result<(), Infallible> {
        Ok(())
    }

    fn visit_pattern(&mut self, _: &Pattern) -> Result<(), Infallible> {
        Ok(())
    }
}
