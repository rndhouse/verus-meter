//! A helper runs on each reaching caller path. Partition the actual live
//! ledger before adding callee costs so unrelated branch maxima never cancel.

use super::{
    Accounting, Boundary, Condition, Footprint, Live, Point, contracts, transport::Allocations,
    unsupported,
};
use crate::{
    ast::VirErr,
    messages::Span,
    resource::memory::{
        elements::ElementState, heap::Owner, synchronization::helpers::Call, transfer::Prepared,
    },
};
use std::collections::HashSet;

pub(in super::super) struct CallFrame {
    /// The caller frame with arguments, transferred regions and the result slot removed.
    path: Live,
    cost: Footprint,
    inputs: Vec<InputRegion>,
}

/// Allocation identities and byte cost of one original parameter node on this path.
struct InputRegion {
    cost: Footprint,
    inputs: HashSet<usize>,
    fixed: Vec<super::origins::FixedOrigin>,
    dynamic: Vec<u64>,
}

impl Accounting {
    pub(in super::super) fn call_frames(
        &self,
        span: &Span,
        owners: &[Option<Owner>],
        elements: &[ElementState],
        result_ids: &HashSet<u64>,
    ) -> Result<Vec<CallFrame>, VirErr> {
        let partitions = owners
            .iter()
            .map(|owner| {
                let allocations = Allocations::owned(owner.as_ref(), elements, span)?;
                let origins = owner.as_ref().map(Owner::inputs).unwrap_or_default();
                Ok((allocations, origins))
            })
            .collect::<Result<Vec<_>, VirErr>>()?;
        self.paths
            .iter()
            .map(|path| {
                let mut frame = path.clone();
                frame.values.retain(|id, _| !result_ids.contains(id));
                let mut inputs = Vec::new();
                for (allocations, origins) in &partitions {
                    let mut cost = Footprint::zero(span);
                    for (kind, bytes) in &allocations.fixed {
                        let missing =
                            || unsupported(span, "a transferred input outside its caller frame");
                        let remaining = frame.fixed.get_mut(kind).ok_or_else(missing)?;
                        *remaining = remaining.checked_sub(*bytes).ok_or_else(missing)?;
                        cost = cost.add(
                            span,
                            Footprint::charge(kind.clone(), contracts::literal(span, *bytes)),
                        );
                    }
                    let fixed = allocations
                        .roles
                        .values()
                        .flatten()
                        .map(|role| {
                            frame.owned.remove(role).ok_or_else(|| {
                                unsupported(
                                    span,
                                    "a transferred input without its original allocation",
                                )
                            })
                        })
                        .collect::<Result<_, _>>()?;
                    let mut dynamic = Vec::new();
                    for id in &allocations.dynamic {
                        if let Some(charge) = frame.dynamic.remove(id) {
                            dynamic.push(*id);
                            cost = cost.add(span, Footprint::charge(charge.kind, charge.amount));
                        }
                    }
                    frame.inputs.retain(|id| !origins.contains(id));
                    inputs.push(InputRegion { cost, inputs: origins.clone(), fixed, dynamic });
                }
                let cost = Accounting::path_expression(&frame, span);
                Ok(CallFrame { path: frame, cost, inputs })
            })
            .collect()
    }
}

impl CallFrame {
    /// Record a relative profile or scalar allowance. The source observation
    /// stays reachable through its checked call edge, including nested calls.
    pub(in super::super) fn observe(
        &self,
        storage: &mut Accounting,
        span: &Span,
        mut cost: Footprint,
        live: Option<(&HashSet<usize>, Option<&Prepared>)>,
        result: &HashSet<u64>,
        point: Option<usize>,
        synchronization: Option<(&Condition, &Call)>,
    ) -> Result<(), VirErr> {
        let mut path = self.path.clone();
        let mut boundary = Boundary::Live;
        if let Some((phase, call)) = synchronization {
            for supplied in call.incoming_actuals() {
                path.held.remove(&supplied);
            }
            path.held.extend(&phase.held);
            // Alias substitution can make an acquiring try-lock alternative impossible.
            let instances: std::collections::BTreeSet<_> =
                path.held.iter().map(|held| held.instance).collect();
            if instances.len() < path.held.len() {
                return Ok(());
            }
            boundary = phase.boundary;
            if let Boundary::Wait(wait) = boundary
                && instances.contains(&wait.instance)
            {
                return Err(unsupported(
                    span,
                    "reentrant blocking acquisition of a held mutex through a helper",
                ));
            }
        }
        let mut observation = Point::from_live(span, self.cost.clone(), &path, boundary);
        observation.values.extend(result);
        observation.call_point = point;
        if let Some((live, transfer)) = live {
            let mut ordered: Vec<_> = live.iter().collect();
            ordered.sort_unstable();
            for id in ordered {
                if let Some(region) = self.inputs.get(*id) {
                    cost = cost.add(span, region.cost.clone());
                    observation.inputs.extend(&region.inputs);
                    observation.fixed_origins.extend(&region.fixed);
                    observation.allocations.extend(&region.dynamic);
                } else if let Some(region) = transfer.and_then(|t| t.regions.get(id)) {
                    cost = cost.add(span, region.clone());
                } else {
                    return Err(unsupported(span, "an input lifetime without a precise region"));
                }
                observation.inputs.extend(transfer.and_then(|t| t.origins.peaks.get(id)));
            }
        }
        observation.cost = self.cost.add(span, cost);
        storage.peak_costs.push((span.clone(), observation.cost.clone()));
        std::sync::Arc::make_mut(&mut storage.report.points).push(observation);
        storage.report.conditional = true;
        Ok(())
    }
}
