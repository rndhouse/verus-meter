//! Facts derived together while checking a function, consumed together at calls.

#[derive(Clone)]
pub(super) struct FunctionSummary {
    pub(super) returned: Option<super::ownership::Returned>,
    pub(super) return_parameter: Option<usize>,
    pub(super) profiles: Vec<super::lifetime::Profile>,
}
