//! Facts derived together while checking a function, consumed together at calls.

/// Call-composition facts established together by a checked function body.
#[derive(Clone)]
pub(super) struct FunctionSummary {
    /// Inferred minimum entry reservations, proved from allocation state at calls.
    pub(super) reservations: std::collections::HashMap<usize, crate::ast::Expr>,
    /// How an owning result retains an input allocation or creates a fresh one.
    pub(super) returned: Option<super::ownership::Returned>,
    /// Zero-based input index when the result forwards that value's charge.
    pub(super) return_parameter: Option<usize>,
    /// Simultaneous costs and input/result lifetimes needed to compose a call.
    pub(super) profiles: Vec<super::lifetime::Profile>,
    /// Bounds for replacement buffers retained through mutable vector parameters.
    pub(super) growth: std::collections::HashMap<usize, crate::ast::Expr>,
}
