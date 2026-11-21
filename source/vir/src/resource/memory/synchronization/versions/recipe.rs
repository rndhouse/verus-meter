//! Propose portable descriptors from the assignments that accounting already
//! emits. Each proposed value is checked at the original snapshot. Traversal
//! order alone therefore never establishes a fact about executable control flow.

use crate::ast::*;
use crate::ast_visitor::{AstVisitor, NoScoper, Walk};
use crate::resource::memory::{growth::Growth, metadata::expr, transfer::simplify};
use std::collections::{HashMap, HashSet};

/// Source conditions and statement order at a snapshot. Compare these only
/// within the same single-visit actor. Match guards can be evaluated for
/// several arms; only their bodies are mutually exclusive.
#[derive(Clone, Default)]
pub(super) struct Position {
    arms: Vec<(u64, usize)>,
    statements: Vec<(u64, usize)>,
}

impl Position {
    pub(super) fn can_precede(&self, other: &Self) -> bool {
        self.arms.iter().all(|(site, arm)| !other.arms.iter().any(|(s, a)| s == site && a != arm))
            && self.statements.iter().all(|(block, index)| {
                !other.statements.iter().any(|(b, i)| b == block && index > i)
            })
    }
}

pub(super) fn variable(value: &Expr) -> &VarIdent {
    let ExprX::Var(name) = &value.x else { unreachable!("generated snapshot local") };
    name
}

pub(super) fn assignment(statement: &Stmt) -> Option<(&VarIdent, &Expr)> {
    let StmtX::Expr(value) = &statement.x else { return None };
    let ExprX::Assign { place, rhs, op: None, .. } = &value.x else { return None };
    let PlaceX::Local(name) = &place.x else { return None };
    Some((name, rhs))
}

/// Only erased expressions in the memory algebra can travel between scopes.
/// Every free variable must be bound by a reaching definition or the entry.
fn operands(value: &Expr) -> Option<Vec<VarIdent>> {
    let mut names = Vec::new();
    crate::ast_visitor::expr_visitor_check(value, &mut |_, node| {
        match &node.x {
            ExprX::Var(name) => names.push(name.clone()),
            ExprX::Const(_)
            | ExprX::Unary(..)
            | ExprX::UnaryOpr(UnaryOpr::Field(_), _)
            | ExprX::Binary(..)
            | ExprX::If(_, _, Some(_)) => {}
            ExprX::Call {
                target: CallTarget::Fun(_, fun, _, _, _),
                post_args: None,
                body: None,
                ..
            } if matches!(fun.path.segments.last(), Some(Segment::V(name, _))
                    if expr::is_operation(fun, name))
                || *fun == crate::fun!(CrateId::Vstd => "seq", "Seq"; "empty")
                || *fun == crate::fun!(CrateId::Vstd => "seq", "Seq"; "push")
                || *fun == crate::fun!(CrateId::Vstd => "seq", "Seq"; "add") => {}
            _ => return Err(()),
        }
        Ok(())
    })
    .ok()?;
    Some(names)
}

/// A backward slice ending at a particular outgoing or publishing snapshot.
/// Local names are only keys for substitution; none appear in the result.
pub(super) struct Recipe {
    assignments: Vec<(VarIdent, Expr)>,
    pub(super) parameters: HashSet<VarIdent>,
    pub(super) exit: Position,
}

impl Recipe {
    /// Request the algebra facts used to evaluate each component of a
    /// projected result. Nested children can read a lookup on a subtree that
    /// is already gone from the normalized result descriptor.
    pub(super) fn result_facts(
        &self,
        site: &crate::messages::Span,
        entry: &Expr,
        input: &Expr,
        parameters: &HashMap<VarIdent, Expr>,
        facts: &mut Vec<Stmt>,
    ) -> Option<()> {
        let mut values = parameters.clone();
        values.insert(variable(entry).clone(), input.clone());
        for (name, value) in &self.assignments {
            let step = crate::ast_visitor::map_expr_visitor(value, &|e| {
                if let ExprX::Var(n) = &e.x
                    && let Some(v) = values.get(n)
                {
                    Ok(v.clone())
                } else {
                    Ok(e.clone())
                }
            })
            .ok()?;
            crate::resource::memory::transfer::fixed_selection_facts(site, &step, facts);
            let normalized = simplify::simplify(&step);
            values.insert(name.clone(), normalized);
        }
        Some(())
    }

    pub(super) fn apply(&self, input: Option<(&Expr, &Expr)>) -> Expr {
        let mut values = HashMap::new();
        if let Some((formal, actual)) = input {
            values.insert(variable(formal).clone(), actual.clone());
        }
        let mut last = None;
        for (name, value) in &self.assignments {
            let resolved = simplify::specialize(value, &values);
            values.insert(name.clone(), resolved.clone());
            last = Some(resolved);
        }
        last.expect("a snapshot has a defining assignment")
    }
}

pub(super) struct Schedule<'a> {
    growth: &'a Growth,
    position: Position,
    writes: Vec<(VarIdent, Expr, Position)>,
}

impl<'a> Schedule<'a> {
    pub(super) fn for_body(growth: &'a Growth, body: &Expr) -> Self {
        let mut schedule = Self { growth, position: Position::default(), writes: Vec::new() };
        schedule.visit_expr(body).expect("infallible schedule visit");
        schedule
    }

    pub(super) fn position(&self, snapshot: &Expr) -> Option<&Position> {
        self.writes.iter().rev().find(|(name, _, _)| name == variable(snapshot)).map(|w| &w.2)
    }

    pub(super) fn recipe(
        &self,
        output: &Expr,
        entry: Option<&Expr>,
        parameters: &HashMap<VarIdent, VarIdent>,
    ) -> Option<Recipe> {
        let name = variable(output);
        let end = self.writes.iter().rposition(|(n, _, _)| n == name)?;
        let exit = &self.writes[end].2;
        let mut needed: HashSet<_> = [name.clone()].into();
        let mut assignments = Vec::new();
        for (n, rhs, position) in self.writes[..=end].iter().rev() {
            if !needed.contains(n) || !position.can_precede(exit) {
                continue;
            }
            if !position.arms.iter().all(|arm| exit.arms.contains(arm)) {
                // A write is conditional at the requested snapshot. Until it
                // has a closed branch join, preserve the arbitrary input.
                return None;
            }
            needed.remove(n);
            if entry.is_some_and(|input| variable(input) == n) {
                continue;
            }
            let rhs = if parameters.is_empty() {
                rhs.clone()
            } else {
                crate::ast_visitor::map_expr_visitor(rhs, &|value| {
                    let parameter = match &value.x {
                        ExprX::Var(name) => parameters.get(name),
                        ExprX::ReadPlace(place, _) => match &place.x {
                            PlaceX::Local(name) => parameters.get(name),
                            _ => None,
                        },
                        _ => None,
                    };
                    Ok(parameter.map_or_else(
                        || value.clone(),
                        |formal| {
                            SpannedTyped::new(&value.span, &value.typ, ExprX::Var(formal.clone()))
                        },
                    ))
                })
                .ok()?
            };
            needed.extend(operands(&rhs)?);
            assignments.push((n.clone(), rhs));
        }
        if !needed.iter().all(|n| parameters.values().any(|p| p == n)) {
            return None;
        }
        assignments.reverse();
        Some(Recipe { assignments, parameters: needed, exit: exit.clone() })
    }

    fn observe(&mut self, actions: Option<&Vec<Stmt>>) {
        self.writes.extend(
            actions
                .into_iter()
                .flatten()
                .filter_map(assignment)
                .map(|(name, rhs)| (name.clone(), rhs.clone(), self.position.clone())),
        );
    }
}

impl AstVisitor<Walk, (), NoScoper> for Schedule<'_> {
    fn visit_expr(&mut self, value: &Expr) -> Result<(), ()> {
        let site = value.span.id;
        let growth = self.growth;
        self.observe(growth.before.get(&site));
        self.observe(growth.updates.get(&site));
        match &value.x {
            ExprX::NonSpecClosure { .. } => {}
            ExprX::If(test, yes, no) => {
                self.visit_expr(test)?;
                for (arm, body) in std::iter::once(yes).chain(no).enumerate() {
                    self.position.arms.push((site, arm));
                    self.visit_expr(body)?;
                    self.position.arms.pop();
                }
            }
            ExprX::Match(scrutinee, arms, _) => {
                self.visit_place(scrutinee)?;
                for (index, arm) in arms.iter().enumerate() {
                    self.visit_expr(&arm.x.guard)?;
                    self.position.arms.push((site, index));
                    self.visit_expr(&arm.x.body)?;
                    self.position.arms.pop();
                }
            }
            ExprX::Block(stmts, tail) => {
                for (index, stmt) in stmts.iter().enumerate() {
                    self.position.statements.push((site, index));
                    self.visit_stmt(stmt)?;
                    self.position.statements.pop();
                }
                if let Some(tail) = tail {
                    self.position.statements.push((site, stmts.len()));
                    self.visit_expr(tail)?;
                    self.position.statements.pop();
                }
            }
            _ => self.visit_expr_rec(value)?,
        }
        self.observe(growth.after.get(&site));
        self.observe(growth.operand_observations.get(&site));
        Ok(())
    }
    fn visit_typ(&mut self, _: &Typ) -> Result<(), ()> {
        Ok(())
    }
    fn visit_pattern(&mut self, _: &Pattern) -> Result<(), ()> {
        Ok(())
    }
    fn visit_place(&mut self, place: &Place) -> Result<(), ()> {
        self.visit_place_rec(place)
    }
    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), ()> {
        self.visit_stmt_rec(stmt)
    }
}
