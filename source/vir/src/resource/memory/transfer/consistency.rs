//! Check the ownership interface shared by local accounting and forest tracing.
//!
//! This checks effect coverage and result types, not numerical equality of byte
//! bounds or a semantic equivalence proof for complete forest expressions.
//! Descriptor transformations and their proof obligations remain authoritative
//! for individual operations. An interface disagreement is an analyser bug.

use super::{Template, Value};
use crate::ast::*;
use crate::messages::{Span, error};
use crate::resource::memory::{layout::Layouts, summary::FunctionSummary};
use std::collections::BTreeSet;

pub(in super::super) fn validate(
    function: &Function,
    layouts: &Layouts,
    summary: &FunctionSummary,
) -> Result<(), VirErr> {
    let affected = &summary.modified_parameters;
    let Some(template) = checked_template(&function.span, summary, affected)? else {
        return Ok(());
    };
    for input in summary.profiles.iter().flat_map(|point| &point.inputs) {
        if *input >= summary.input_paths.len() && !template.regions.contains_key(input) {
            return Err(error(
                &function.span,
                "internal memory analysis inconsistency: missing input lifetime region",
            ));
        }
    }
    if let Value::Owner(node) = &template.result {
        if !crate::ast_util::types_equal(&node.typ, &function.x.outer_ret.x.typ) {
            return Err(error(
                &function.span,
                "internal memory analysis inconsistency: ownership result type differs",
            ));
        }
    }
    for (index, node) in &template.borrowed {
        let typ = function
            .x
            .params
            .get(*index)
            .and_then(|parameter| layouts.borrowed_owner(&parameter.x.typ));
        if typ.is_none_or(|typ| !crate::ast_util::types_equal(typ, &node.typ)) {
            return Err(error(
                &function.span,
                "internal memory analysis inconsistency: borrowed ownership type differs",
            ));
        }
    }
    Ok(())
}

/// Validate every published ownership interface, including optional templates
/// that callers may select to recover exact reservation and cardinality facts.
fn checked_template<'a>(
    span: &Span,
    summary: &'a FunctionSummary,
    affected: &BTreeSet<usize>,
) -> Result<Option<&'a Template>, VirErr> {
    let Some(template) = summary.transfer.as_ref() else {
        return if summary.transfer_required {
            Err(error(span, "internal memory analysis inconsistency: missing ownership template"))
        } else {
            Ok(None)
        };
    };
    check_interface(span, summary.allocations.returned.is_some(), affected, template)?;
    Ok(Some(template))
}

/// Borrowed roots changed by authoritative operations, independently of whether
/// those operations allocate storage. In particular, a reserved push changes
/// geometry even when the native allocation summary has no retained effect.
pub(in super::super) fn modified_parameters(
    parameters: &Params,
    layouts: &Layouts,
    checked: &super::Checked,
) -> BTreeSet<usize> {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| {
            (layouts.borrowed_owner(&parameter.x.typ).is_some()
                && checked.mutates(&parameter.x.name))
            .then_some(index)
        })
        .collect()
}

fn check_interface(
    span: &Span,
    returns_owner: bool,
    affected: &BTreeSet<usize>,
    template: &Template,
) -> Result<(), VirErr> {
    if returns_owner != matches!(template.result, Value::Owner(_)) {
        return Err(error(
            span,
            "internal memory analysis inconsistency: ownership result is missing or invented",
        ));
    }
    let traced = template.borrowed.keys().copied().collect();
    if affected != &traced {
        return Err(error(
            span,
            "internal memory analysis inconsistency: borrowed ownership effects disagree",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resource::memory::{metadata::expr, transfer::Node};
    use std::sync::Arc;

    #[test]
    fn missing_or_invented_effects_are_errors() {
        let span = Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "ownership consistency".into(),
        };
        let mut template = Template {
            ordered: false,
            origins: Default::default(),
            regions: Default::default(),
            symbols: vec![],
            effects: None,
            borrowed: Default::default(),
            result: Value::Unit,
        };
        let affected = [0].into();
        assert!(check_interface(&span, false, &affected, &template).is_err());
        let node = Node {
            origin: None,
            typ: crate::ast_util::unit_typ(),
            memory: expr::empty(&span, expr::record_type()),
            minima: Default::default(),
        };
        template.borrowed.insert(0, node.clone());
        assert!(check_interface(&span, false, &affected, &template).is_ok());
        assert!(check_interface(&span, false, &[1].into(), &template).is_err());
        assert!(check_interface(&span, true, &affected, &template).is_err());
        template.result = Value::Owner(node);
        assert!(check_interface(&span, false, &affected, &template).is_err());
        assert!(check_interface(&span, true, &affected, &template).is_ok());
    }

    #[test]
    fn optional_templates_are_checked_before_publication() {
        use crate::resource::memory::{
            allocations::AllocationSummary, vector_calls::VectorSummary,
        };

        let span = Span {
            raw_span: Arc::new(()),
            id: 2,
            data: Arc::new([]),
            as_string: "optional ownership consistency".into(),
        };
        let mut summary = FunctionSummary {
            modified_parameters: Default::default(),
            transfer_required: false,
            transfer: None,
            allocations: AllocationSummary {
                returned: None,
                retained: Default::default(),
                children: Default::default(),
                collections: Default::default(),
            },
            vectors: VectorSummary {
                reservations: Default::default(),
                returned_capacities: Default::default(),
                removals: Default::default(),
            },
            input_paths: vec![],
            return_parameter: None,
            profiles: vec![],
        };
        let affected = BTreeSet::new();
        assert!(checked_template(&span, &summary, &affected).unwrap().is_none());
        summary.transfer_required = true;
        assert!(checked_template(&span, &summary, &affected).is_err());
        summary.transfer_required = false;
        summary.transfer = Some(Template {
            ordered: false,
            origins: Default::default(),
            regions: Default::default(),
            symbols: vec![],
            effects: None,
            borrowed: Default::default(),
            result: Value::Unit,
        });
        assert!(checked_template(&span, &summary, &affected).unwrap().is_some());
        // A native summary says no owning result exists. Even an optional
        // template must not invent one when callers choose to specialize it.
        summary.transfer.as_mut().unwrap().result = Value::Owner(Node {
            origin: None,
            typ: crate::ast_util::unit_typ(),
            memory: expr::empty(&span, expr::record_type()),
            minima: Default::default(),
        });
        assert!(checked_template(&span, &summary, &affected).is_err());
    }

    #[test]
    fn reserved_pushes_count_as_borrowed_mutations() {
        let span = Span {
            raw_span: Arc::new(()),
            id: 3,
            data: Arc::new([]),
            as_string: "reserved push mutation".into(),
        };
        let vector_id = Dt::Path(crate::path!(CrateId::Vstd => "tests", "Vector"));
        let vector = Arc::new(TypX::Datatype(
            vector_id.clone(),
            Arc::new(vec![Arc::new(TypX::Int(IntRange::U(32)))]),
            Arc::new(vec![]),
        ));
        let layouts = Layouts::new(&[], None, Some(vector_id), None);
        let parameters: Params = Arc::new(
            (0..3)
                .map(|index| {
                    crate::def::Spanned::new(
                        span.clone(),
                        ParamX {
                            name: VarIdent(
                                Arc::new(format!("parameter_{index}")),
                                VarIdentDisambiguate::VirTemp(index),
                            ),
                            typ: if index == 2 {
                                vector.clone()
                            } else {
                                Arc::new(TypX::MutRef(vector.clone()))
                            },
                            mode: Mode::Exec,
                            user_mut: false,
                            unwrapped_info: None,
                        },
                    )
                })
                .collect(),
        );
        let mut checked = super::super::Checked::default();
        for index in [1, 2] {
            let parameter = &parameters[index];
            checked.operation(
                &span,
                super::super::checked::Operation::Push {
                    receiver: super::super::checked::Place {
                        source: SpannedTyped::new(
                            &span,
                            &parameter.x.typ,
                            ExprX::Var(parameter.x.name.clone()),
                        ),
                        typ: vector.clone(),
                        location: (parameter.x.name.clone(), vec![]),
                    },
                    child: expr::integer(&span, 0),
                    element: 4,
                    grow: false,
                    allocation: None,
                    input: None,
                },
            );
        }
        // Neither push grows a buffer. Only the borrowed root belongs in the
        // caller-visible mutation set; the owned parameter is consumed locally.
        assert_eq!(modified_parameters(&parameters, &layouts, &checked), [1].into());
    }
}
