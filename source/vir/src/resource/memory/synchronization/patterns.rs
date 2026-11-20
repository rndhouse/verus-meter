//! By-value native Result arms transfer the release responsibility. A poison
//! wrapper owns its guard. WouldBlock carries no guard, even on a poisoned mutex.

use super::local::Owned;
use crate::{
    ast::*,
    resource::memory::{analysis::Analysis, heap::Owner, model::unsupported, transfer::checked},
};

impl Analysis<'_> {
    /// The compiler checked the exhaustive match. Each supported arm must also
    /// identify which actual owner is bound or discarded on that source edge.
    pub(in super::super) fn lock_result_pattern(
        &mut self,
        pattern: &Pattern,
        owner: Option<Owner>,
        slots: &mut Vec<(VarIdent, u64)>,
    ) -> Result<bool, VirErr> {
        let mut owner =
            owner.ok_or_else(|| unsupported(&pattern.span, "a lock Result without its owner"))?;
        let interval = owner.synchronization.and_then(Owned::interval).ok_or_else(|| {
            unsupported(&pattern.span, "a lock Result without its native acquisition")
        })?;
        let PatternX::Constructor(name, variant, fields) = &pattern.x else {
            return Err(unsupported(
                &pattern.span,
                "a lock Result without an explicit variant pattern",
            ));
        };
        let TypX::Datatype(actual, _, _) = &*pattern.typ else { unreachable!() };
        let [field] = fields.as_slice() else {
            return Err(unsupported(&pattern.span, "this lock Result payload pattern"));
        };
        if name != actual {
            return Err(unsupported(&pattern.span, "this lock Result variant type"));
        }
        let attempt = matches!(owner.synchronization, Some(Owned::Attempt(_)));
        let (acquired, binding) = match (variant.as_str(), &field.a.x) {
            ("Ok", _) => (Some(true), Some(&field.a)),
            ("Err", PatternX::Constructor(error, alternative, fields)) if attempt => {
                let TypX::Datatype(actual, _, _) = &*field.a.typ else { unreachable!() };
                if error != actual {
                    return Err(unsupported(&field.a.span, "this native try-lock error type"));
                }
                match (alternative.as_str(), fields.as_slice()) {
                    ("WouldBlock", []) => (Some(false), None),
                    ("Poisoned", [poison]) => (Some(true), Some(&poison.a)),
                    _ => return Err(unsupported(&field.a.span, "this try-lock error outcome")),
                }
            }
            ("Err", _) => (if attempt { None } else { Some(true) }, Some(&field.a)),
            _ => return Err(unsupported(&pattern.span, "this native lock Result variant")),
        };
        self.transitions
            .pattern(&pattern.span, checked::Pattern::LockOutcome { interval, acquired });
        if let Some(acquired) = acquired {
            if !self.storage.select_interval(interval, acquired) {
                return Ok(false);
            }
            if acquired {
                owner.synchronization = Some(Owned::Guard(interval));
            }
        }
        if let Some(binding) = binding {
            self.option_pattern(binding, &binding.typ, slots, Some(owner), None)?;
        }
        Ok(true)
    }
}
