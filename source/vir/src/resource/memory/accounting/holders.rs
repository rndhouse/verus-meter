//! Pair intact protocol witnesses with the actual heap regions on each reaching path.
use super::{Accounting, MemoryReport, Point};
use crate::{ast::VirErrAs, resource::memory::synchronization::holders::Witness};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

impl Accounting {
    /// Annotate only observations made by this frame during the checked source statement.
    pub(in super::super) fn mark_holders(&mut self, start: usize, inputs: &[Witness]) {
        if !inputs.is_empty() {
            for point in &mut Arc::make_mut(&mut self.report.points)[start..] {
                point.holders.extend_from_slice(inputs);
            }
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Region {
    Fixed(super::origins::FixedOrigin),
    Dynamic(u64),
}

impl Witness {
    fn description(self) -> String {
        match self {
            Self::Input(index) => format!("input {index}"),
            Self::Call(_) => "helper acquisition".into(),
            Self::Local(_) => "local".into(),
            Self::Capture(_, index) => format!("capture {index}"),
        }
    }
}

impl MemoryReport {
    /// Local observations remain available while the global concurrency proof is pending.
    pub fn synchronization_diagnostics(&self) -> Vec<VirErrAs> {
        let mut notes = self.interval_diagnostics();
        for body in &self.holder_effects {
            notes.extend(holder_diagnostics(&body.points));
            notes.extend(issuer_notes(body));
        }
        notes
    }
}

fn holder_diagnostics(points: &[Point]) -> Vec<VirErrAs> {
    if !points.iter().any(|p| !p.holders.is_empty()) {
        return vec![];
    }
    // Compare exactly the points carrying each allocation identity. Two
    // allocations of equal extent can have different lifetimes.
    let mut regions = BTreeMap::new();
    let mut calls = BTreeMap::new();
    for p in points.iter() {
        let held = p.holders.iter().copied().collect::<BTreeSet<_>>();
        if p.call_point.is_some() {
            for &witness in &held {
                calls.insert((p.span.id, witness), &p.span);
            }
        }
        for region in p
            .fixed_origins
            .iter()
            .copied()
            .map(Region::Fixed)
            .chain(p.allocations.iter().copied().map(Region::Dynamic))
        {
            let (span, ever, always) = regions
                .entry(region)
                .or_insert_with(|| (&p.span, BTreeSet::<Witness>::new(), held.clone()));
            if ever.is_empty() && !held.is_empty() {
                *span = &p.span;
            }
            ever.extend(&held);
            always.retain(|id| held.contains(id));
        }
    }
    let mut notes = vec![];
    for ((_, id), span) in calls {
        let witness = id.description();
        notes.push(VirErrAs::Note(crate::messages::note(
            span,
            format!("checked helper phase with intact holder {witness}"),
        )));
    }
    for (region, (span, ever, always)) in regions {
        let allocation = match region {
            Region::Fixed(origin) => format!("{}-byte allocation", origin.bytes),
            Region::Dynamic(_) => "dynamic storage region".to_owned(),
        };
        for witness in ever {
            let relation = if always.contains(&witness) {
                "only observed within"
            } else {
                "also observed outside"
            };
            let binding = witness.description();
            notes.push(VirErrAs::Note(crate::messages::note(
                span,
                format!("{allocation} {relation} intact holder {binding}"),
            )));
        }
    }
    notes
}

/// Display issuer evidence only at points containing an intact witness and an
/// executable allocation. Keep worker and publishing function scopes separate.
fn issuer_notes(body: &super::super::summary::BodyEffects) -> Vec<VirErrAs> {
    use super::super::synchronization::holders::Issuer;
    let mut notes = BTreeMap::new();
    for point in body.points.iter() {
        for holder in &point.holders {
            let Some(issuer) = body.ownership.holders.issuer(*holder) else { continue };
            for origin in &point.fixed_origins {
                let source = match issuer {
                    Issuer::Input(i) => format!("input {i}"),
                    Issuer::Fixed(id) => format!("fixed binding {id}"),
                    Issuer::Shared(root) => format!("shared backing {}", root.serial()),
                };
                notes.entry((*origin, *holder, issuer)).or_insert_with(|| {
                    VirErrAs::Note(crate::messages::note(
                        &point.span,
                        format!(
                            "{}-byte allocation observed with holder issued by {source}",
                            origin.bytes
                        ),
                    ))
                });
            }
        }
    }
    notes.into_values().collect()
}
