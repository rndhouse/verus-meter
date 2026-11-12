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
    if !summary.transfer_required {
        return Ok(());
    }
    let template = summary.transfer.as_ref().ok_or_else(|| {
        error(&function.span, "internal memory analysis inconsistency: missing ownership template")
    })?;
    let affected = modified_parameters(function, layouts, summary);
    for input in summary.profiles.iter().flat_map(|point| &point.inputs) {
        if *input >= summary.input_paths.len() && !template.regions.contains_key(input) {
            return Err(error(
                &function.span,
                "internal memory analysis inconsistency: missing input lifetime region",
            ));
        }
    }
    check_interface(&function.span, summary.allocations.returned.is_some(), &affected, template)?;
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

/// Borrowed parameters with checked allocation or collection-shape effects.
pub(in super::super) fn modified_parameters(
    function: &Function,
    layouts: &Layouts,
    summary: &FunctionSummary,
) -> BTreeSet<usize> {
    let mut affected = BTreeSet::new();
    for (index, _) in summary
        .allocations
        .retained
        .keys()
        .chain(summary.allocations.children.keys())
        .chain(summary.allocations.collections.keys())
        .chain(summary.vectors.removals.iter())
    {
        if layouts.borrowed_owner(&function.x.params[*index].x.typ).is_some() {
            affected.insert(*index);
        }
    }
    affected
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
}
