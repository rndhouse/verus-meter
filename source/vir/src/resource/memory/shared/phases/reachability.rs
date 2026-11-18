//! Project a worker destructor through the acyclic graph of canonical payloads.
use super::*;

/// Live finite references and indexed ancestors that may still keep a payload edge alive.
#[derive(Default)]
pub(super) struct Reachable {
    pub(super) fixed: BTreeMap<RootId, u64>,
    pub(super) indexed_ancestors: BTreeMap<RootId, BTreeSet<RootId>>,
}

impl SharedRoots {
    /// Find the fixed ownership graph reachable from these imports, then
    /// propagate final drops through it. Two edges to one root are two
    /// strong references, but its control block and payload are charged once.
    pub(super) fn at_worker_checkpoint(
        &self,
        checkpoint: &Checkpoint,
        indexed: impl Fn(RootId) -> bool,
    ) -> Result<Reachable, VirErr> {
        let span = &checkpoint.site;
        let mut counts = BTreeMap::new();
        let mut children = BTreeMap::new();
        let mut pending: Vec<_> = checkpoint.handles.keys().copied().collect();
        while let Some(id) = pending.pop() {
            if counts.contains_key(&id) {
                continue;
            }
            let root = self.roots.get(&id).ok_or_else(|| {
                unsupported(span, "a worker checkpoint outside its shared allocation domain")
            })?;
            let mut count = root.strong;
            if let Some(observed) = checkpoint.handles.get(&id) {
                count = observed.in_domain(count).ok_or_else(|| {
                    unsupported(span, "inconsistent checkpoint strong-reference counts")
                })?;
            }
            counts.insert(id, count);
            if let Backing::Owned(owner) = &root.storage {
                let mut edges = Vec::new();
                super::super::visit_strong_handles(
                    owner,
                    span,
                    super::super::References::None,
                    |link| {
                        let StrongLink::Known(child) = link else {
                            return Err(unsupported(
                                span,
                                "a selected alias inside a worker checkpoint backing",
                            ));
                        };
                        edges.push(child);
                        Ok(())
                    },
                )?;
                pending.extend(edges.iter().copied());
                children.insert(id, edges);
            }
        }
        let mut dead: Vec<_> =
            counts.iter().filter_map(|(id, count)| (*count == 0).then_some(*id)).collect();
        let mut ancestors: BTreeMap<RootId, BTreeSet<RootId>> = BTreeMap::new();
        while let Some(id) = dead.pop() {
            // All finite edges disappearing does not discharge an indexed owner.
            // Pass that condition down each immutable edge while subtracting the
            // finite handle count once for every field (including duplicate links).
            let mut retained = ancestors.get(&id).cloned().unwrap_or_default();
            if indexed(id) {
                retained.insert(id);
            }
            for child in children.remove(&id).into_iter().flatten() {
                if !retained.is_empty() {
                    ancestors.entry(child).or_default().extend(&retained);
                }
                let count = counts.get_mut(&child).unwrap();
                *count = count.checked_sub(1).ok_or_else(|| {
                    unsupported(span, "duplicate final destruction of a shared payload")
                })?;
                if *count == 0 {
                    dead.push(child);
                }
            }
        }
        Ok(Reachable { fixed: counts, indexed_ancestors: ancestors })
    }
}
