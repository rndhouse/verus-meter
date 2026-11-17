//! Match source effects to exact calls in the compiler's original control graph.
//! Missing or ambiguous spans remain unbound; accounting must reject them when
//! executed. Keep graph namespaces and back edges rather than inferring event
//! multiplicity from the number of static sites or matching nearby source text.

use vir::{
    ast::Function,
    resolution_inference::ResolutionInfo,
    resource::memory::{
        concurrency::sites::{self, Binding},
        synchronization::{
            CompilerEvidence,
            flow::{Call, Point, Terminator},
        },
    },
};

pub(super) fn resolve(
    function: &Function,
    modes: &ResolutionInfo,
    functions: &[Function],
    evidence: &mut CompilerEvidence,
) {
    for call in sites::calls(function, modes, functions, &evidence.concurrency, true) {
        let Some(source) = crate::spans::from_raw_span(&call.span.raw_span) else { continue };
        let Some(graph) = evidence.graph(&call.scope) else { continue };
        let points: Vec<_> = graph.blocks.iter().enumerate().filter_map(|(block, node)| {
            if crate::spans::from_raw_span(&node.span.raw_span) == Some(source)
                && matches!(node.terminator, Terminator::Call { call: Call::Concurrent(operation), .. } if operation == call.operation)
            {
                Some(Point { block, statement: node.statements.len() })
            } else { None }
        }).collect();
        if let [point] = points.as_slice() {
            evidence.concurrency.record_native_site(
                call.id,
                Binding {
                    anchor: call.anchor,
                    scope: call.scope,
                    point: *point,
                    operation: call.operation,
                },
            );
        }
    }
}

/// Explain binding coverage only when the user explicitly requests tracing.
/// Missing latent-body bindings are not errors until that body is analyzed.
pub(super) fn diagnostics(
    function: &Function,
    modes: &ResolutionInfo,
    functions: &[Function],
    evidence: &CompilerEvidence,
) -> Vec<vir::ast::VirErrAs> {
    sites::calls(function, modes, functions, &evidence.concurrency, true)
        .into_iter()
        .map(|call| {
            let scope =
                if call.scope == function.x.name { "function body" } else { "closure body" };
            let message = if let Some(binding) = evidence.concurrency.native_site(call.id) {
                format!(
                    "memory native call binding: {:?} ({scope}, compiler block {})",
                    call.operation, binding.point.block,
                )
            } else {
                format!("memory native call unbound: {:?} ({scope})", call.operation)
            };
            vir::ast::VirErrAs::Note(vir::messages::note(&call.span, message))
        })
        .collect()
}
