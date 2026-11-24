//! The checked cell has one persistent ownership slot. A read lends that slot.
//! A writer takes its entire tree and puts the replacement tree back on release.
use super::{CheckedBody, WorkspaceMethod};
use crate::ast::*;
use crate::messages::Span;
use crate::resource::memory::{
    accounting::Accounting,
    analysis::Analysis,
    heap::{Owner, OwnerSlot},
    model::unsupported,
    paths, places,
    transfer::checked,
};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::resource::memory) enum Location {
    Cell(u64),
    Reader(u64),
    Writer(u64),
    /// A real borrowed/returned reader for which the local frame has no payload forest.
    ObservedReader,
    /// The current payload came from the version at this exclusive acquisition.
    SharedWriter(super::local::Interval),
}

impl Location {
    pub(in crate::resource::memory) fn fresh_cell() -> Self {
        Self::Cell(Accounting::fresh_allocation())
    }
}

impl Owner {
    pub(in crate::resource::memory) fn populated_rw_cell(&self) -> bool {
        matches!(self.rw_location, Some(Location::Cell(_)))
            && self.children.contains_key(&OwnerSlot::Contents)
    }

    /// A by-value caller must supply every populated input slot. Shared
    /// references need a version contract before a helper may mutate the slot.
    pub(in crate::resource::memory) fn contains_rw_cell(&self) -> bool {
        let mut found = false;
        self.visit(&mut |node| found |= matches!(node.rw_location, Some(Location::Cell(_))));
        found
    }
}

impl Analysis<'_> {
    /// Locals have already undergone source cleanup. Owned parameter slots still
    /// present on a normal or early return will also be destroyed by Rust.
    pub(in crate::resource::memory) fn check_populated_cell_exits(
        &self,
        span: &Span,
    ) -> Result<(), VirErr> {
        let check = |heap: &crate::resource::memory::heap::Heap, site: &Span| {
            let mut populated = false;
            for owner in heap.owners.values() {
                owner.visit(&mut |node| populated |= node.populated_rw_cell());
            }
            if populated { Err(unreclaimed(site)) } else { Ok(()) }
        };
        if self.flow.reachable {
            check(&self.heap, span)?;
        }
        for edge in &self.flow.exits {
            check(&edge.state.heap, &edge.span)?;
        }
        Ok(())
    }

    /// Locate the unique storage owner, independently of which handle/alias
    /// provided access. A copied worker ledger cannot decide a shared version.
    pub(super) fn rw_cell_path(&self, id: u64, span: &Span) -> Result<paths::LocalPath, VirErr> {
        self.rw_cell_access(id, false, span)
    }

    fn rw_cell_access(
        &self,
        id: u64,
        write: bool,
        span: &Span,
    ) -> Result<paths::LocalPath, VirErr> {
        let mut found = Vec::new();
        let mut search = |name: VarIdent, root: &Owner| {
            root.visit_paths(&mut Vec::new(), &mut |path, owner| {
                if owner.rw_location == Some(Location::Cell(id)) {
                    found.push((name.clone(), path.clone()));
                }
            })
        };
        for (name, root) in self.heap.owners.iter().chain(&self.heap.borrowed) {
            search(name.clone(), root);
        }
        for root in self.heap.shared.allocation_ids() {
            if (!write || !self.heap.workers.shares_root(root))
                && !self.growth.indexed_shared.contains_key(&root)
                && let Some(backing) = self.heap.shared.backing_at(&root.binder())
            {
                search(root.binder(), backing);
            }
        }
        if found.len() != 1 {
            return Err(unsupported(
                span,
                "a reader/writer payload without one current canonical owner",
            ));
        }
        Ok(found.pop().unwrap())
    }

    pub(super) fn rw_receiver(&self, value: &Expr) -> Option<Location> {
        if let ExprX::ReadPlace(p, _) = &value.x
            && let PlaceX::Temporary(e) = &p.x
            && places::arc_borrow_adapter(&e.typ, &p.typ)
        {
            let (name, path) = paths::expr(e, &e.typ)?;
            let link = self.heap.root(&name)?.at(&path)?.shared?;
            let super::Instance::Fresh(id) = self.heap.shared.mutex_instance(link)? else {
                return None;
            };
            return Some(Location::Cell(id));
        }
        let (name, path) = paths::expr(value, &value.typ)?;
        self.heap.root(&name)?.at(&path)?.rw_location
    }

    pub(in crate::resource::memory) fn rw_payload_call(
        &mut self,
        method: WorkspaceMethod,
        call: &Expr,
        args: &Exprs,
        leaf: CheckedBody,
        destination: bool,
    ) -> Result<(), VirErr> {
        let span = &call.span;
        let fail = || {
            unsupported(
                span,
                "a reader/writer operation without its actual payload and protocol location",
            )
        };
        let receiver = args.first().and_then(|arg| self.rw_receiver(arg));
        let mut owners = Vec::new();
        let mut slots = Vec::new();
        for (index, arg) in args.iter().enumerate() {
            slots.push(self.produce(arg)?);
            if !self.flow.reachable {
                return Ok(());
            }
            let owner = if self.layouts.owner(&arg.typ) {
                let mut child = self.result_owner.take().ok_or_else(fail)?;
                if (method == WorkspaceMethod::New && index == 0)
                    || (method == WorkspaceMethod::ReleaseWrite && index == 1)
                {
                    self.freeze_rw_payload(arg, &mut child);
                }
                Some(child)
            } else {
                None
            };
            owners.push(owner);
        }
        for value in slots {
            self.release_value(value, span);
        }
        self.charge_workspace(leaf, call, destination)?;
        let mut operation = checked::Operation::Evaluate { args: args.clone() };
        let result = match method {
            WorkspaceMethod::New => {
                let child = owners[0].take().ok_or_else(fail)?;
                operation = checked::Operation::Aggregate {
                    fields: vec![(args[0].clone(), Some(OwnerSlot::Contents))],
                    tag: 0,
                };
                let mut cell =
                    Owner { rw_location: Some(Location::fresh_cell()), ..Default::default() };
                cell.children.insert(OwnerSlot::Contents, child);
                Some(cell)
            }
            WorkspaceMethod::Read => {
                let payload = super::RwRecord::payload(&call.typ).ok_or_else(fail)?.1;
                let location = match receiver {
                    Some(Location::Cell(id)) if !self.rw_observed_read(id, payload, span)? => {
                        let (name, path) = self.rw_cell_path(id, span)?;
                        let cell =
                            self.heap.root(&name).and_then(|r| r.at(&path)).ok_or_else(fail)?;
                        if !cell.populated_rw_cell() {
                            return Err(fail());
                        }
                        Location::Reader(id)
                    }
                    // A returned read handle certifies an initialized cell at the real
                    // receiver. No ownership or geometry is imported on this path.
                    Some(Location::Cell(_)) | None => Location::ObservedReader,
                    _ => return Err(fail()),
                };
                Some(Owner { rw_location: Some(location), ..Default::default() })
            }
            WorkspaceMethod::Write => {
                let Some(Location::Cell(id)) = receiver else { return Err(fail()) };
                let (ty, handle) = super::RwRecord::write_pair(&call.typ).ok_or_else(fail)?;
                let shared = self.rw_acquire_shared(call, id, ty, handle)?;
                let (where_, (name, path)) = match shared {
                    Some(interval) => {
                        (Location::SharedWriter(interval), (interval.payload_name(), vec![]))
                    }
                    None => (Location::Writer(id), self.rw_cell_access(id, true, span)?),
                };
                let cell =
                    self.heap.root_mut(&name).and_then(|r| r.at_mut(&path)).ok_or_else(fail)?;
                let value = cell.children.remove(&OwnerSlot::Contents).ok_or_else(fail)?;
                let visit = if let Some(interval) = shared {
                    Some((interval, self.source_visit(span.id, self.local_occurrences(span)?)))
                } else {
                    None
                };
                operation = write_transition(&args[0], name, path, ty, None, visit);
                let writer = Owner { rw_location: Some(where_), ..Default::default() };
                Some(Owner {
                    children: [
                        (OwnerSlot::Field(Arc::new("0".into())), value),
                        (OwnerSlot::Field(Arc::new("1".into())), writer),
                    ]
                    .into(),
                    ..Default::default()
                })
            }
            WorkspaceMethod::ReleaseWrite => {
                let writer = owners[0].take().ok_or_else(fail)?;
                let (name, path) = match writer.rw_location {
                    Some(Location::Writer(id)) => self.rw_cell_access(id, true, span)?,
                    Some(Location::SharedWriter(interval)) => (interval.payload_name(), vec![]),
                    _ => return Err(fail()),
                };
                let cell =
                    self.heap.root_mut(&name).and_then(|r| r.at_mut(&path)).ok_or_else(fail)?;
                operation = write_transition(
                    &args[0],
                    name,
                    path,
                    &args[1].typ,
                    Some(args[1].clone()),
                    None,
                );
                if cell
                    .children
                    .insert(OwnerSlot::Contents, owners[1].take().ok_or_else(fail)?)
                    .is_some()
                {
                    return Err(fail());
                }
                if let Some(Location::SharedWriter(interval)) = writer.rw_location {
                    self.rw_release_shared(interval, span)?;
                    // The measured frame does not split at the atomic unlock. Its
                    // tail can overlap the next writer, so observe it after release too.
                    self.charge_workspace(leaf, call, destination)?;
                }
                None
            }
            WorkspaceMethod::Borrow => {
                match receiver {
                    Some(Location::Reader(id)) => {
                        self.rw_cell_path(id, span)?;
                    }
                    Some(Location::ObservedReader) | None => {}
                    _ => return Err(fail()),
                }
                None
            }
            WorkspaceMethod::ReleaseRead => {
                let reader = owners[0].take().ok_or_else(fail)?;
                if !matches!(
                    reader.rw_location,
                    Some(Location::Reader(_) | Location::ObservedReader)
                ) {
                    return Err(fail());
                }
                None
            }
            WorkspaceMethod::IntoInner => {
                operation =
                    checked::Operation::Unwrap { source: args[0].clone(), observed_scalar: false };
                let mut cell = owners[0].take().ok_or_else(fail)?;
                if !matches!(cell.rw_location, Some(Location::Cell(_))) {
                    return Err(fail());
                }
                let payload = cell.children.remove(&OwnerSlot::Contents).ok_or_else(fail)?;
                self.release_owner(cell, span);
                Some(payload)
            }
            WorkspaceMethod::Cell => return Err(fail()),
        };
        if owners.iter().any(Option::is_some) {
            return Err(fail());
        }
        self.result_owner = result;
        self.transitions.operation(span, operation);
        Ok(())
    }
}

/// The location is the uniquely resolved cell, even when release names only the token.
fn write_transition(
    receiver: &Expr,
    name: VarIdent,
    mut path: crate::resource::memory::heap::OwnerPath,
    typ: &Typ,
    replacement: Option<Expr>,
    acquired: Option<(
        super::local::Interval,
        crate::resource::memory::workers::SourceVisit<crate::messages::AstId>,
    )>,
) -> checked::Operation {
    path.push(OwnerSlot::Contents);
    checked::Operation::RwWrite {
        receiver: receiver.clone(),
        slot: checked::Place { source: receiver.clone(), typ: typ.clone(), location: (name, path) },
        replacement,
        acquired,
    }
}

pub(in crate::resource::memory) fn unreclaimed(span: &Span) -> VirErr {
    unsupported(
        span,
        "discarding a populated RwLock whose cell retains a separately owned allocation",
    )
}
