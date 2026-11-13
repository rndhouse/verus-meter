//! Freeze parent invariants at each nested loop's actual entry.
//!
//! Nested queries retain checked parent facts without assuming that they start
//! on the first syntactic visit to the enclosing body.

use crate::ast::*;
use crate::resource::memory::analysis::Analysis;

impl Analysis<'_> {
    /// A nested query needs facts about its actual entry, not observations from
    /// the first syntactic visit to its parent's body. Freeze the parent's
    /// completed inductive facts at that entry after both summaries are known.
    /// These remain ordinary invariants checked before the nested loop.
    pub(super) fn inherit_loop_entries(&mut self) -> Result<(), VirErr> {
        let records = self.transitions.loops.clone();
        let mut descendants = std::collections::HashMap::new();
        for (id, record) in &records {
            let mut children = std::collections::HashSet::new();
            crate::ast_visitor::expr_visitor_check(&record.body, &mut |_, value| {
                if matches!(value.x, ExprX::Loop { .. }) && records.contains_key(&value.span.id) {
                    children.insert(value.span.id);
                }
                Ok::<(), VirErr>(())
            })?;
            descendants.insert(*id, children);
        }
        let mut parents = Vec::new();
        for child in records.keys() {
            if let Some((parent, children)) = descendants
                .iter()
                .filter(|(_, children)| children.contains(child))
                .min_by_key(|(_, children)| children.len())
            {
                parents.push((children.len(), *parent, *child));
            }
        }
        parents.sort_by_key(|(size, _, _)| std::cmp::Reverse(*size));
        for (_, parent, child) in parents {
            let record = &records[&child];
            if record.single_visit {
                continue;
            }
            let mut immutable = self
                .growth
                .loop_entry
                .get(&parent)
                .map(|entries| entries.values().cloned().collect::<Vec<_>>())
                .unwrap_or_default();
            for charge in &records[&parent].charges {
                immutable.push(charge.entry.clone());
                immutable.push(charge.length.1.clone());
                if let Some((_, entry)) = &charge.backing {
                    immutable.push(entry.clone());
                }
            }
            for charge in &record.charges {
                immutable.push(charge.length.1.clone());
            }
            let mut preserved = std::collections::HashMap::new();
            for value in immutable {
                crate::ast_visitor::expr_visitor_check(&value, &mut |_, value| {
                    if let ExprX::Var(name) = &value.x {
                        preserved.insert(name.clone(), value.clone());
                    }
                    Ok::<(), VirErr>(())
                })?;
            }
            for (name, value) in preserved {
                if let Some(previous) =
                    self.growth.loop_entry.entry(child).or_default().insert(name, value.clone())
                {
                    self.growth.loops.entry(child).or_default().push(crate::ast_util::mk_eq(
                        &record.span,
                        &previous,
                        &value,
                    ));
                }
            }
            let facts = self.growth.loops.get(&parent).cloned().unwrap_or_default();
            let facts = if let Some(iterator) = &records[&parent].iterator {
                facts.iter().map(|fact| iterator.body_fact(fact)).collect::<Result<_, _>>()?
            } else {
                facts
            };
            let facts = self.freeze_loop_facts(&record.span, facts)?;
            self.growth.loops.entry(child).or_default().extend(facts);
            for charge in &record.charges {
                let fact = crate::ast_util::mk_eq(&record.span, &charge.length.0, &charge.length.1);
                let fact = self.freeze_loop_facts(&record.span, vec![fact])?;
                self.growth.loops.entry(child).or_default().extend(fact);
            }
        }
        Ok(())
    }
}
