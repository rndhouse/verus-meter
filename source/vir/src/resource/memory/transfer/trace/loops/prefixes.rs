//! Exact collection membership at an arbitrary completed loop prefix.
//!
//! Reuse ordinary loop composition to propose the invariant. Membership and
//! backing-byte bounds remain separate obligations in the executable body.

use super::*;

impl Trace<'_> {
    /// Reuse the accepted program to describe the actual completed prefix.
    /// Equality is submitted as an invariant, so both initialization and every
    /// transition must establish it; summary inference supplies no assumptions.
    pub(super) fn record_prefix_forests(
        &mut self,
        record: &Loop,
        effects: &[Effect],
        tokens: &HashSet<VarIdent>,
        binder: &VarIdent,
        before: &State,
    ) -> Option<()> {
        if record.reference_forests.is_empty() {
            return Some(());
        }
        let observation = record.progress.as_ref()?;
        let span = &record.span;
        let programs = guards::partition(
            span,
            effects,
            binder,
            expr::integer(span, 0),
            observation.ordinal.clone(),
            &self.proof_values,
        )?;
        let mut prefix = self.clone();
        prefix.state = before.clone();
        let mut original = record
            .regions
            .iter()
            .map(|region| {
                Some((
                    region.location.clone(),
                    match region.entry {
                        Some(id) => self.regions.get(&id)?.clone(),
                        None => expr::empty(span, expr::record_type()),
                    },
                ))
            })
            .collect::<Option<BTreeMap<_, _>>>()?;
        let mut phases = Vec::new();
        for phase in programs {
            let mut planned = Vec::new();
            for mut program in phase {
                program.effects = self.collection_blocks(span, program.effects, tokens, binder)?;
                planned.push(program);
            }
            phases.push(planned);
        }
        prefix.apply_phases(record, phases, &mut original)?;
        let mut forests = Vec::new();
        let mut backing_bounds = BTreeMap::new();
        for ((name, path), (typ, actual)) in &record.reference_forests {
            let location = (
                name.clone(),
                path.clone(),
                path.iter()
                    .map(|slot| expr::integer(span, self.layouts.metadata_slot(slot)))
                    .collect(),
            );
            let node = prefix.get(span, &location, typ)?;
            let backing =
                substitute(&property(span, node.memory.clone(), "bytes"), &self.proof_values);
            let memory = expr::operation(span, "runtime", vec![node.memory], expr::memory_type());
            let memory = substitute(&memory, &self.proof_values);
            let closed = crate::ast_visitor::expr_visitor_check(&memory, &mut |scope, value| {
                if matches!(&value.x, ExprX::Var(name) if !scope.contains_key(name) && self.symbols.iter().any(|symbol| &symbol.name == name)) { Err(()) } else { Ok(()) }
            }).is_ok();
            if !closed {
                return None;
            }
            let backing_closed = crate::ast_visitor::expr_visitor_check(&backing, &mut |scope, value| {
                if matches!(&value.x, ExprX::Var(name) if !scope.contains_key(name) && self.symbols.iter().any(|symbol| &symbol.name == name)) { Err(()) } else { Ok(()) }
            }).is_ok();
            if backing_closed {
                backing_bounds.insert((name.clone(), path.clone()), backing);
            }
            forests.push((actual.clone(), memory));
        }
        self.loop_progress.get_mut(&span.id)?.forests = forests;
        self.loop_progress.get_mut(&span.id)?.backing_bounds = backing_bounds;
        Some(())
    }
}
