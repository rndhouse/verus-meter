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
    let calls = sites::all_calls(function, modes, functions, &evidence.concurrency);
    for call in calls.concurrent {
        if let Some(binding) = bind(evidence, &call, |native| match native {
            Call::Concurrent(operation) => Some(*operation),
            _ => None,
        }) {
            evidence.concurrency.record_native_site(call.id, binding);
        }
    }
    for call in calls.synchronization {
        if let Some(binding) = bind(evidence, &call, |native| match native {
            Call::Primitive(operation) => Some(*operation),
            _ => None,
        }) {
            evidence.concurrency.synchronization_sites.insert(call.id, binding);
        }
    }
}

fn bind<T: Copy + Eq>(
    evidence: &CompilerEvidence,
    call: &sites::Call<T>,
    resolved: impl Fn(&Call) -> Option<T>,
) -> Option<Binding<T>> {
    let source = crate::spans::from_raw_span(&call.span.raw_span)?;
    let graph = evidence.graph(&call.scope)?;
    let mut points = graph.blocks.iter().enumerate().filter_map(|(index, block)| {
        let Terminator::Call { call: native, .. } = &block.terminator else { return None };
        (resolved(native) == Some(call.operation)
            && crate::spans::from_raw_span(&block.span.raw_span) == Some(source))
        .then_some(Point { block: index, statement: block.statements.len() })
    });
    let point = points.next()?;
    points.next().is_none().then(|| Binding {
        anchor: call.anchor,
        scope: call.scope.clone(),
        point,
        operation: call.operation,
        iterations: call.iterations.clone(),
    })
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
            let iterations = call.iterations.len();
            let region = call.iterations.last().map(|iteration| match iteration.part {
                sites::LoopPart::Head => "head",
                sites::LoopPart::Body => "body",
            });
            let context = region.map_or_else(
                || "no local loop".to_owned(),
                |region| format!("{iterations} local loop(s), {region}"),
            );
            let message = if let Some(binding) = evidence.concurrency.native_site(call.id) {
                format!(
                    "memory native call binding: {:?} ({scope}, {context}, compiler block {})",
                    call.operation, binding.point.block,
                )
            } else {
                format!("memory native call unbound: {:?} ({scope}, {context})", call.operation)
            };
            vir::ast::VirErrAs::Note(vir::messages::note(&call.span, message))
        })
        .collect()
}
