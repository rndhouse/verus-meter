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
        let closed = |value: &Expr| {
            crate::ast_visitor::expr_visitor_check(value, &mut |scope, value| {
                if let ExprX::Var(name) = &value.x
                    && !scope.contains_key(name)
                    && self.symbols.iter().any(|symbol| &symbol.name == name)
                {
                    return Err(());
                }
                Ok(())
            })
            .is_ok()
        };
        let mut populations = Vec::new();
        for (role, (typ, actual)) in &record.reference_forests {
            let (name, path) = role;
            let location = (
                name.clone(),
                path.clone(),
                path.iter()
                    .map(|slot| expr::integer(span, self.layouts.metadata_slot(slot)))
                    .collect(),
            );
            let node = prefix.get(span, &location, typ)?;
            let field =
                |field| substitute(&property(span, node.memory.clone(), field), &self.proof_values);
            let length = (!self.checked.captured_populations.is_empty())
                .then(|| field("length"))
                .filter(&closed);
            let backing = field("bytes");
            let backing = closed(&backing).then_some(backing);
            let expected = expr::operation(span, "runtime", vec![node.memory], expr::memory_type());
            let expected = substitute(&expected, &self.proof_values);
            if !closed(&expected) {
                return None;
            }
            populations.push(crate::resource::memory::loops::populations::PopulationPrefix::new(
                record,
                role,
                (actual.clone(), expected),
                length,
                backing,
            ));
        }
        self.loop_progress.get_mut(&span.id)?.populations = populations;
        Some(())
    }
}
