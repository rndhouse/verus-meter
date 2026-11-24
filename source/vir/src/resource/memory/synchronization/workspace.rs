//! A verified generic library body can use an inline payload whose byte width
//! is only known in the caller. Keep its actual executable VIR and checked
//! variable modes. At a concrete call, run the ordinary memory analysis with
//! an opaque payload of that width. The resulting profile covers frame storage
//! only. Ownership of the concrete payload requires a separate transfer.
use super::CheckedBody;
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{BudgetExprX, ResourceContract, analysis, model::unsupported};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, sync::Arc};
use vir_macros::ToDebugSNode;

/// Public payload transitions and the internal verified cell workspaces they call.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, ToDebugSNode)]
pub enum WorkspaceMethod {
    New,
    Read,
    Write,
    Borrow,
    ReleaseRead,
    ReleaseWrite,
    IntoInner,
    Cell,
}

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
pub struct WorkspaceSource {
    pub(in crate::resource::memory) method: WorkspaceMethod,
    body: Expr,
    modes: Vec<(VarIdent, Mode)>,
}

impl WorkspaceSource {
    /// Capture only original, local executable bodies with mode-checking evidence.
    pub fn capture(
        method: WorkspaceMethod,
        function: &Function,
        modes: &crate::resolution_inference::ResolutionInfo,
    ) -> Option<Self> {
        if function.x.attrs.is_external_body || function.x.mode != Mode::Exec {
            return None;
        }
        let mut entries: Vec<_> = modes.var_modes.iter().map(|(v, m)| (v.clone(), *m)).collect();
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        Some(Self { method, body: function.x.body.clone()?, modes: entries })
    }
}

impl analysis::Analysis<'_> {
    pub(in crate::resource::memory) fn workspace_for(
        &self,
        target: &Fun,
        types: &[Typ],
        span: &Span,
    ) -> Result<Option<CheckedBody>, VirErr> {
        let Some(template) = self.layouts.template_sources.get(target) else {
            return Ok(self.layouts.imported_leaves.get(target).copied());
        };
        if self.layouts.workspace.is_none()
            && template
                .x
                .attrs
                .resource_template
                .as_ref()
                .is_some_and(|s| s.method == WorkspaceMethod::Cell)
        {
            return Err(unsupported(
                span,
                "metering an internal permissioned cell outside its checked payload transfer",
            ));
        }
        let parameter = template
            .x
            .typ_params
            .first()
            .ok_or_else(|| unsupported(span, "a workspace without its payload parameter"))?;
        let actual = types
            .first()
            .ok_or_else(|| unsupported(span, "a workspace without its concrete payload type"))?;
        let width = self.layouts.size(actual, span)?;
        let key = (target.clone(), width);
        if let Some(leaf) = self.layouts.workspace_cache.borrow().get(&key) {
            return Ok(Some(*leaf));
        }
        let mut layouts = self.layouts.clone();
        if !layouts.measuring.insert(target.clone()) {
            return Err(unsupported(span, "recursive parametric workspaces"));
        }
        layouts.workspace = Some((target.clone(), parameter.clone(), width));
        let source = template
            .x
            .attrs
            .resource_template
            .as_ref()
            .ok_or_else(|| unsupported(span, "an uncertified parametric workspace"))?;
        let mut f = template.x.clone();
        f.body = Some(source.body.clone());
        let attrs = Arc::make_mut(&mut f.attrs);
        attrs.resource_template = None;
        attrs.resource_contract = Some(ResourceContract {
            budget: crate::def::Spanned::new(span.clone(), BudgetExprX::Literal(u64::MAX)),
        });
        let f = template.new_x(f);
        let modes = source.modes.iter().cloned().collect();
        let checked = analysis::check(
            &f,
            Some(&modes),
            &HashMap::from([(target.clone(), f.clone())]),
            &layouts,
            &HashMap::from([(target.clone(), u64::MAX)]),
            &HashMap::new(),
            &Default::default(),
            self.fresh_span,
        )?
        .ok_or_else(|| unsupported(span, "a workspace without checked body effects"))?;
        if !checked.checks.is_empty()
            || checked
                .obligations
                .iter()
                .any(|o| crate::resource::memory::symbolic::obligation(o).is_some())
        {
            return Err(unsupported(
                span,
                "a parametric workspace requiring additional caller proofs",
            ));
        }
        let leaf = CheckedBody::from_body(&f, &checked)?;
        self.layouts.workspace_cache.borrow_mut().insert(key, leaf);
        Ok(Some(leaf))
    }
}
