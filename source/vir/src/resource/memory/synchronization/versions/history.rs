//! A state is either a checked publication baseline or the result of one
//! particular release acting on its predecessor. Equal byte descriptions can
//! come from different allocations. Keep those edges even when a local byte
//! proof can share a single case for both.

use super::{Interval, Publication, recipe::Position, section::Section};
use crate::{
    ast::Expr,
    resource::memory::{transfer::simplify::inspect::same_expression, workers::WorkerId},
};
use std::collections::BTreeSet;

/// Exceeding this search limit leaves the entire mutex input unrestricted.
const MAX_HISTORY_STATES: usize = 128;

enum Origin {
    /// See the publication observations of this initial state.
    Publisher,
    /// The frozen release identifies its source edge and allocation origins in
    /// the worker summary. The predecessor identifies its incoming element tree.
    Release {
        previous: usize,
        actor: WorkerId,
        position: Position,
        interval: Interval,
        snapshot: Expr,
    },
}

struct State {
    origin: Origin,
    forest: Expr,
}

#[derive(Default)]
pub(in crate::resource::memory) struct History {
    /// In a loop these finite forests are induction candidates. All releases
    /// must preserve their union before it can constrain any acquisition.
    pub(super) repeated: bool,
    states: Vec<State>,
    /// Each real publication keeps its own proof and allocation origins even
    /// when identical starting contents admit the same sequence of releases.
    publications: Vec<(Publication, usize)>,
    /// Candidate inputs for this particular acquisition. Indexes refer to
    /// states of this root only, ordered after their dependencies.
    incoming: std::collections::BTreeMap<Interval, Vec<usize>>,
}

impl History {
    pub(super) fn acquisitions(&self) -> usize {
        self.incoming.len()
    }

    fn can_enter(&self, mut previous: usize, section: &Section<'_>) -> bool {
        while let Origin::Release { previous: parent, actor, position, .. } =
            &self.states[previous].origin
        {
            if *actor == section.worker.actor && !position.can_precede(&section.access) {
                return false;
            }
            previous = *parent;
        }
        true
    }

    pub(super) fn build(seeds: Vec<(Publication, Expr)>, sections: &[Section<'_>]) -> Option<Self> {
        let mut history = Self { repeated: sections.iter().any(|s| s.repeated), ..Self::default() };
        let mut pending = Vec::new();
        for (publication, forest) in seeds {
            let index =
                match history.states.iter().position(|s| same_expression(&s.forest, &forest)) {
                    Some(index) => index,
                    None => {
                        let index = history.states.len();
                        if index >= MAX_HISTORY_STATES {
                            return None;
                        }
                        pending.push((BTreeSet::new(), index));
                        history.states.push(State { origin: Origin::Publisher, forest });
                        index
                    }
                };
            history.publications.push((publication, index));
        }
        // A prefix may stop before any unused holder runs. A non-acquiring
        // attempt, or a path with no payload access, leaves the forest intact.
        // Follow one release at a time; a fixed acquisition cannot run twice.
        while let Some((used, previous)) = pending.pop() {
            let input = history.states[previous].forest.clone();
            for section in sections {
                if used.contains(&section.interval) || !history.can_enter(previous, section) {
                    continue;
                }
                history.incoming.entry(section.interval).or_default().push(previous);
                let mut next = used.clone();
                next.insert(section.interval);
                for (release, recipe) in section.binding.releases.iter().zip(&section.releases) {
                    // Bound compiler work on large finite populations. The
                    // caller keeps the arbitrary incoming forest for this
                    // entire root if the explicit histories would be too many.
                    if history.states.len() >= MAX_HISTORY_STATES {
                        return None;
                    }
                    if next.len() < sections.len() {
                        pending.push((next.clone(), history.states.len()));
                    }
                    history.states.push(State {
                        origin: Origin::Release {
                            previous,
                            actor: section.worker.actor,
                            position: recipe.exit.clone(),
                            interval: section.interval,
                            snapshot: release.contents.clone(),
                        },
                        forest: recipe.apply(Some((&section.binding.entry, &input))),
                    });
                }
            }
        }
        Some(history)
    }

    pub(super) fn seeds(&self) -> impl Iterator<Item = (&Publication, &Expr)> {
        self.publications.iter().map(|(seed, state)| (seed, &self.states[*state].forest))
    }

    pub(super) fn inputs(&self, interval: Interval) -> Vec<&Expr> {
        let mut inputs: Vec<&Expr> = Vec::new();
        if self.repeated {
            return self.candidates();
        }
        for id in &self.incoming[&interval] {
            let forest = &self.states[*id].forest;
            if !inputs.iter().any(|other| same_expression(other, forest)) {
                inputs.push(forest);
            }
        }
        inputs
    }

    pub(super) fn candidates(&self) -> Vec<&Expr> {
        let mut values: Vec<&Expr> = Vec::new();
        for state in &self.states {
            if !values.iter().any(|other| same_expression(other, &state.forest)) {
                values.push(&state.forest);
            }
        }
        values
    }

    /// Each prefix can be a completed run if other holders skip their
    /// protected access. Look up the input of the actual returning holder
    /// on that same prefix. An absent holder retained its default empty input.
    pub(super) fn terminal_states(&self) -> std::ops::Range<usize> {
        0..self.states.len()
    }

    pub(super) fn input_before(&self, mut state: usize, interval: Interval) -> Option<&Expr> {
        while let Origin::Release { previous, interval: step, .. } = &self.states[state].origin {
            if *step == interval {
                return Some(&self.states[*previous].forest);
            }
            state = *previous;
        }
        None
    }

    /// All cuts of this history compatible with the native joins seen at the
    /// observation. Unjoined actors can already have run. Future actors cannot.
    pub(super) fn at_join(&self, mut end: usize, observation: &super::Observation) -> Vec<&Expr> {
        let mut path = vec![end];
        while let Origin::Release { previous, .. } = &self.states[end].origin {
            end = *previous;
            path.push(end);
        }
        path.reverse();
        let mut first = 0;
        let mut last = path.len() - 1;
        for (i, &state) in path.iter().enumerate().skip(1) {
            let Origin::Release { actor, .. } = &self.states[state].origin else { unreachable!() };
            if observation.completed.contains(actor) {
                first = i;
            }
            if !observation.published.contains(actor) {
                last = last.min(i - 1);
            }
        }
        // This ordering violates publication order. Including its baseline
        // conservatively keeps every choice defined.
        path.get(first..=last)
            .unwrap_or(&path[..1])
            .iter()
            .map(|&i| &self.states[i].forest)
            .collect()
    }

    pub(super) fn transitions(&self, interval: Interval, release: &Expr) -> Vec<(&Expr, &Expr)> {
        let mut edges: Vec<(&Expr, &Expr)> = Vec::new();
        for state in &self.states {
            if let Origin::Release { previous, interval: id, snapshot, .. } = &state.origin
                && *id == interval
                && std::sync::Arc::ptr_eq(snapshot, release)
            {
                let input = &self.states[*previous].forest;
                if !edges
                    .iter()
                    .any(|(i, o)| same_expression(i, input) && same_expression(o, &state.forest))
                {
                    edges.push((input, &state.forest));
                }
            }
        }
        edges
    }
}
