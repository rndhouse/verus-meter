//! Publish a body-checked borrowed output at a critical section inside a helper.
//! With a single acquisition and a unit return, the helper's own last write to
//! the borrowed tree is exactly what it leaves at unlock. The proof substitutes
//! the contents at that acquisition, even if peers run before or after it.
use super::*;
use crate::resource::memory::{
    projections,
    summary::FunctionSummary,
    synchronization::helpers::Call,
    transfer::{self, Input, simplify},
};
use std::collections::HashMap;

impl transfer::Checked {
    pub(in crate::resource::memory) fn closed_mutex_output(
        &self,
        callee: &Function,
        modified: &std::collections::BTreeSet<usize>,
        points: &[crate::resource::memory::accounting::Point],
        template: Option<&transfer::Template>,
    ) -> Option<(usize, Interval)> {
        let template = template?;
        let (parameter, interval) = self.closed_mutex_section()?;
        if !crate::resource::memory::model::unit(&callee.x.outer_ret.x.typ)
            || modified.len() != 1
            || !modified.contains(&parameter)
            || !template.borrowed.contains_key(&parameter)
            || !self.release_retains_inputs(parameter, interval, points)
            || template.symbols.iter().filter(|s| matches!(s.input, Input::LockTest)).count() > 1
            || callee.x.params.iter().enumerate().any(|(i, p)| {
                i != parameter
                    && p.x.mode == Mode::Exec
                    && !crate::resource::memory::contracts::scalar(&p.x.typ)
            })
        {
            return None;
        }
        Some((parameter, interval))
    }
}

impl Analysis<'_> {
    pub(in crate::resource::memory) fn publish_internal_section(
        &mut self,
        value: &Expr,
        callee: &Function,
        args: &Exprs,
        summary: &FunctionSummary,
        parameter: usize,
        call: &mut Call,
    ) -> Result<(), VirErr> {
        let site = &value.span;
        let interval = call.publish_section(parameter, site)?;
        // Snapshots are emitted at the source call. Later argument evaluation
        // must not change a scalar already observed by this transformation.
        for (index, (param, arg)) in callee.x.params.iter().zip(args.iter()).enumerate() {
            if index != parameter && param.x.mode == Mode::Exec {
                projections::spec_value(arg)?;
            }
        }
        let mutex = self
            .layouts
            .borrowed_descriptor(&callee.x.params[parameter].x.typ)
            .expect("borrowed mutex interface");
        let payload = self
            .layouts
            .mutex_payload(&mutex)
            .ok_or_else(|| unsupported(site, "a helper release without its mutex payload type"))?
            .clone();
        let root = self
            .heap
            .shared
            .imported_mutex(interval.instance, &payload, site)?
            .ok_or_else(|| unsupported(site, "a helper release without its imported mutex"))?;
        if !self.needs_payload_binding(root, interval, &payload, site)? {
            return Err(unsupported(site, "a helper release reusing an open acquired payload"));
        }
        let entry = self.unrestricted_payload(site, "helper_acquired_contents");
        let template = summary.transfer.as_ref().expect("checked helper output");
        let slot = self.layouts.metadata_slot(&OwnerSlot::Contents);
        let contents = expr::path(site, [slot]);
        let wrapper = expr::prefix(site, entry.clone(), contents.clone());
        let mut values = HashMap::new();
        let mut test = None;
        for symbol in &template.symbols {
            let actual = match &symbol.input {
                Input::LockTest => {
                    test = Some(symbol.name.clone());
                    continue;
                }
                Input::Complete => crate::ast_util::mk_bool(site, true),
                Input::Scalar(index) => projections::spec_value(&args[*index])?,
                Input::Forest(index) if *index == parameter => wrapper.clone(),
                Input::Property(index, path, field) if *index == parameter => {
                    if path.is_empty() {
                        // The mutex wrapper has no dynamic storage or cardinality.
                        expr::integer(site, 0)
                    } else {
                        let path =
                            expr::path(site, path.iter().map(|s| self.layouts.metadata_slot(s)));
                        transfer::property(
                            site,
                            simplify::simplify(&expr::subtree(site, wrapper.clone(), path)),
                            field,
                        )
                    }
                }
                Input::Minimum(index, _) if *index == parameter => expr::integer(site, 0),
                _ => {
                    return Err(unsupported(
                        site,
                        "a helper release depending on an unbound owner",
                    ));
                }
            };
            values.insert(symbol.name.clone(), actual);
        }
        let visit = self.source_visit(site.clone(), self.local_occurrences(site)?);
        let mut releases = Vec::new();
        let output = &template.borrowed[&parameter].memory;
        for outcome in [false, true] {
            if let Some(test) = &test {
                values.insert(test.clone(), crate::ast_util::mk_bool(site, outcome));
            } else if outcome {
                break;
            }
            let updated = simplify::specialize(output, &values);
            let forest = simplify::simplify(&expr::subtree(site, updated, contents.clone()));
            let snapshot = self.metadata_local(site, "helper_released_contents", forest);
            releases.push(Release {
                visit: visit.clone(),
                contents: snapshot,
                origins: PayloadOrigins::Helper(parameter),
                complete: true,
            });
        }
        self.growth.versioned_shared.insert(root, None);
        self.transitions.protected_versions.bindings.insert(
            interval,
            Binding {
                root,
                payload_type: payload,
                entry,
                input_origins: PayloadOrigins::Helper(parameter),
                access: self.source_visit(site.id, self.local_occurrences(site)?),
                releases,
            },
        );
        Ok(())
    }
}
