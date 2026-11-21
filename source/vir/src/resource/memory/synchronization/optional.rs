//! Return a native guard on selected normal exits of a checked helper.

use super::local::{Interval, Owned};
use crate::ast::VirErr;
use crate::messages::Span;
use crate::resource::memory::{
    analysis::Analysis,
    heap::{Owner, OwnerSlot},
    model::unsupported,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum GuardOption {
    Absent,
    Present(Interval),
    /// Both variants occur, and every Some carries the same acquisition.
    Conditional(Interval),
}

impl GuardOption {
    pub(in super::super) fn interval(self) -> Option<Interval> {
        match self {
            Self::Absent => None,
            Self::Present(id) | Self::Conditional(id) => Some(id),
        }
    }

    pub(super) fn substitute(self, bind: impl Fn(Interval) -> Interval) -> Self {
        match self {
            Self::Absent => Self::Absent,
            Self::Present(id) => Self::Present(bind(id)),
            Self::Conditional(id) => Self::Conditional(bind(id)),
        }
    }

    /// A merged variant tag can select presence, but cannot distinguish two
    /// acquisitions carried by the same Some variant.
    pub(in super::super) fn merge_results(left: &mut Owner, right: &mut Owner) {
        let (Some(Owned::GuardOption(a)), Some(Owned::GuardOption(b))) =
            (left.synchronization, right.synchronization)
        else {
            return;
        };
        if a == b {
            return;
        }
        let (a, b) = (a.interval(), b.interval());
        if a.is_some() && b.is_some() && a != b {
            return;
        }
        let merged = Self::Conditional(a.or(b).expect("different guard outcomes"));
        for owner in [left, right] {
            owner.synchronization = Some(Owned::GuardOption(merged));
            owner.geometry = None;
            owner.geometry_known = false;
        }
    }
}

impl Analysis<'_> {
    /// Keep the tag and guard together. The native guard carries inline bytes
    /// in the Option slot and has no separate allocation below it.
    pub(in super::super) fn package_optional_guard(
        &mut self,
        span: &Span,
        owner: &mut Owner,
        present: bool,
    ) -> Result<(), VirErr> {
        let child = owner
            .children
            .get_mut(&OwnerSlot::Contents)
            .expect("reviewed guard option constructor");
        let tag = if present {
            let Some(Owned::Guard(id)) = child.synchronization.take() else {
                return Err(unsupported(
                    span,
                    "a present guard without its executable acquisition",
                ));
            };
            if !self.storage.holds_interval(id) {
                return Err(unsupported(span, "a present guard outside its acquisition"));
            }
            GuardOption::Present(id)
        } else {
            GuardOption::Absent
        };
        if let Some(region) = child.input {
            self.storage.release_input(region);
        }
        *child = Owner::default();
        owner.synchronization = Some(Owned::GuardOption(tag));
        Ok(())
    }

    /// Select the actual Option tag before binding a guard or continuing
    /// without it. Only the Some edge gets a destructor for the acquisition.
    pub(in super::super) fn select_optional_guard(
        &mut self,
        owner: &mut Owner,
        present: bool,
        span: &Span,
    ) -> Result<bool, VirErr> {
        let Some(Owned::GuardOption(tag)) = owner.synchronization else {
            return Ok(true);
        };
        if !present && matches!(tag, GuardOption::Present(_)) {
            return Ok(false);
        }
        owner.synchronization = None;
        let Some(id) = tag.interval() else { return Ok(!present) };
        if !self.storage.select_interval(id, present) {
            return Ok(false);
        }
        let saved = owner.suspended_payload.take();
        if present {
            if let Some(saved) = saved {
                self.restore_guard_payload(&saved, span)?;
            }
            owner.children.entry(OwnerSlot::Contents).or_default().synchronization =
                Some(Owned::Guard(id));
        }
        Ok(true)
    }
}
