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
    fallthrough: Vec<(u64, usize)>,
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
            | ExprX::Logical(..)
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

fn bind_parameters(rhs: &Expr, parameters: &HashMap<VarIdent, VarIdent>) -> Option<Expr> {
    Some(if parameters.is_empty() {
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
                |formal| SpannedTyped::new(&value.span, &value.typ, ExprX::Var(formal.clone())),
            ))
        })
        .ok()?
    })
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
    tests: HashMap<u64, Expr>,
    /// Source arms that dominate entry to each loop in this body.
    loop_entries: HashMap<u64, Position>,
}

impl<'a> Schedule<'a> {
    pub(super) fn for_body(growth: &'a Growth, body: &Expr) -> Self {
        let mut schedule = Self {
            growth,
            position: Position::default(),
            writes: Vec::new(),
            tests: HashMap::new(),
            loop_entries: HashMap::new(),
        };
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
        // Bound the number of symbolic control paths just as histories bound
        // the number of interleavings. An incomplete slice supplies no facts.
        self.path_recipe(name, end, exit, entry, parameters, &mut 64)
    }

    /// Outside a release's source arm the cell keeps its incoming forest.
    /// Only portable conditions are useful here. The equality is still
    /// checked at the real release before another actor may rely on it.
    pub(super) fn release_recipe(
        &self,
        output: &Expr,
        entry: &Expr,
        parameters: &HashMap<VarIdent, VarIdent>,
    ) -> Option<Recipe> {
        let mut recipe = self.recipe(output, Some(entry), parameters)?;
        for &(site, arm) in recipe.exit.arms.iter().chain(&recipe.exit.fallthrough) {
            let Some((condition, free)) = self.portable_test(site, parameters) else { continue };
            recipe.parameters.extend(free);
            let value =
                SpannedTyped::new(&output.span, &output.typ, ExprX::Var(variable(output).clone()));
            let (yes, no) = if arm == 0 { (value, entry.clone()) } else { (entry.clone(), value) };
            recipe.assignments.push((
                variable(output).clone(),
                SpannedTyped::new(&output.span, &output.typ, ExprX::If(condition, yes, Some(no))),
            ));
        }
        Some(recipe)
    }

    /// Immutable path conditions visible before the loop must also be proved
    /// in Verus's isolated loop query. Supply them as ordinary invariants.
    pub(super) fn entry_guards(
        &self,
        site: crate::messages::AstId,
        parameters: &HashMap<VarIdent, VarIdent>,
    ) -> Vec<Expr> {
        let Some(position) = self.loop_entries.get(&site) else { return Vec::new() };
        position
            .arms
            .iter()
            .chain(&position.fallthrough)
            .filter_map(|(site, arm)| {
                let (condition, _) = self.portable_test(*site, parameters)?;
                Some(if *arm == 0 {
                    condition
                } else {
                    SpannedTyped::new(
                        &condition.span,
                        &condition.typ,
                        ExprX::Unary(UnaryOp::Not, condition.clone()),
                    )
                })
            })
            .collect()
    }

    fn portable_test(
        &self,
        site: u64,
        parameters: &HashMap<VarIdent, VarIdent>,
    ) -> Option<(Expr, HashSet<VarIdent>)> {
        let test = crate::resource::memory::projections::spec_value(self.tests.get(&site)?).ok()?;
        let test = bind_parameters(&test, parameters)?;
        let free: HashSet<_> = operands(&test)?.into_iter().collect();
        free.iter().all(|n| parameters.values().any(|p| p == n)).then_some((test, free))
    }

    fn path_recipe(
        &self,
        name: &VarIdent,
        end: usize,
        path: &Position,
        entry: Option<&Expr>,
        parameters: &HashMap<VarIdent, VarIdent>,
        remaining: &mut usize,
    ) -> Option<Recipe> {
        *remaining = remaining.checked_sub(1)?;
        let mut needed: HashSet<_> = [name.clone()].into();
        let mut assignments = Vec::new();
        for (n, rhs, position) in self.writes[..=end].iter().rev() {
            if !needed.contains(n) || !position.can_precede(path) {
                continue;
            }
            if let Some(&(site, _)) = position.arms.iter().find(|arm| !path.arms.contains(arm)) {
                // Resolve both reaching definitions, including an unchanged
                // input on the arm that did not assign. Only immutable source
                // parameters can select a branch in another worker's scope.
                let (test, mut free) = self.portable_test(site, parameters)?;
                let mut branch = |arm| {
                    let mut selected = path.clone();
                    selected.arms.push((site, arm));
                    let recipe =
                        self.path_recipe(name, end, &selected, entry, parameters, remaining)?;
                    free.extend(recipe.parameters.iter().cloned());
                    Some(recipe.apply(entry.map(|e| (e, e))))
                };
                let yes = branch(0)?;
                let no = branch(1)?;
                let value = SpannedTyped::new(
                    &test.span,
                    &yes.typ,
                    ExprX::If(test.clone(), yes.clone(), Some(no)),
                );
                return Some(Recipe {
                    assignments: vec![(name.clone(), value)],
                    parameters: free,
                    exit: self.writes[end].2.clone(),
                });
            }
            needed.remove(n);
            if entry.is_some_and(|input| variable(input) == n) {
                continue;
            }
            let rhs = bind_parameters(rhs, parameters)?;
            needed.extend(operands(&rhs)?);
            assignments.push((n.clone(), rhs));
        }
        if !needed.iter().all(|n| parameters.values().any(|p| p == n)) {
            return None;
        }
        assignments.reverse();
        Some(Recipe { assignments, parameters: needed, exit: self.writes[end].2.clone() })
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

/// A return or loop jump has no fallthrough edge, including a unit block ending
/// in a semicolon. Unrecognized control flow supplies no path restriction.
fn exits(value: &Expr) -> bool {
    match &value.x {
        ExprX::Return(_) | ExprX::BreakOrContinue { .. } => true,
        ExprX::NeverToAny(inner) => exits(inner),
        ExprX::ReadPlace(place, _) => matches!(&place.x, PlaceX::Temporary(inner) if exits(inner)),
        ExprX::Block(stmts, tail) => {
            tail.as_ref().is_some_and(exits)
                || stmts.iter().any(|stmt| matches!(&stmt.x, StmtX::Expr(e) if exits(e)))
        }
        ExprX::If(_, yes, Some(no)) => exits(yes) && exits(no),
        _ => false,
    }
}

impl AstVisitor<Walk, (), NoScoper> for Schedule<'_> {
    fn visit_expr(&mut self, value: &Expr) -> Result<(), ()> {
        let site = value.span.id;
        let entry_guards = self.position.fallthrough.len();
        let growth = self.growth;
        self.observe(growth.before.get(&site));
        self.observe(growth.updates.get(&site));
        match &value.x {
            ExprX::NonSpecClosure { .. } => {}
            ExprX::Loop { cond, body, .. } => {
                self.loop_entries.insert(site, self.position.clone());
                if let Some(test) = cond {
                    self.visit_expr(test)?;
                    // Every iteration of an unsigned counter < end implies
                    // 0 < end. A stable end travels to another worker even
                    // when the changing counter cannot leave its own loop.
                    let guard = match &test.x {
                        ExprX::Binary(BinaryOp::Inequality(InequalityOp::Lt), start, end)
                            if matches!(
                                &*start.typ,
                                TypX::Int(IntRange::U(_) | IntRange::USize | IntRange::Nat)
                            ) =>
                        {
                            crate::ast_util::mk_ineq(
                                &test.span,
                                &expr::integer(&test.span, 0),
                                end,
                                InequalityOp::Lt,
                            )
                        }
                        _ => test.clone(),
                    };
                    self.tests.insert(site, guard);
                    self.position.fallthrough.push((site, 0));
                }
                self.visit_expr(body)?;
            }
            ExprX::If(test, yes, no) => {
                self.tests.insert(site, test.clone());
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
                    if let StmtX::Expr(value) = &stmt.x
                        && let ExprX::If(_, yes, no) = &value.x
                    {
                        if exits(yes) {
                            self.position.fallthrough.push((value.span.id, 1));
                        }
                        if no.as_ref().is_some_and(exits) {
                            self.position.fallthrough.push((value.span.id, 0));
                        }
                    }
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
        self.position.fallthrough.truncate(entry_guards);
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
