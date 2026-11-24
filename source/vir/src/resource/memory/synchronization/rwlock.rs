//! Nominal vstd records used by the reader/writer protocol. Executable lock
//! fields use their declared types. Its potentially empty cell retains the
//! inline payload slot even while a writer owns the value taken from it.
use crate::ast::*;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RwRecord {
    /// Contains the cell, two atomics and erased proof state.
    Lock,
    /// A shared read handle with an explicit release method.
    Reader,
    /// A writer token, separate from the owned value taken from the cell.
    Writer,
    /// The potentially uninitialized inline storage inside the lock.
    Cell,
    /// Opaque vstd cell containing one possibly unsized storage slot.
    PrimitiveCell,
    /// The standard Rust storage slot for a possibly uninitialized value.
    MaybeUninit,
}

impl RwRecord {
    pub(in crate::resource::memory) fn payload(typ: &Typ) -> Option<(Self, &Typ)> {
        let TypX::Datatype(dt, args, _) = &**typ else { return None };
        Some((Self::of(dt)?, args.first()?))
    }

    /// The writer result moves the value and its distinct handle together.
    pub fn write_pair(ty: &Typ) -> Option<(&Typ, &Typ)> {
        let TypX::Datatype(Dt::Tuple(2), fields, _) = &**ty else { return None };
        let [payload, handle] = fields.as_slice() else { return None };
        let TypX::Datatype(dt, args, _) = &**handle else { return None };
        (Self::of(dt) == Some(Self::Writer)
            && args.first().is_some_and(|v| crate::ast_util::types_equal(v, payload)))
        .then_some((payload, handle))
    }

    /// Match resolved type namespace segments in the distinguished vstd crate.
    pub fn of(dt: &Dt) -> Option<Self> {
        let Dt::Path(p) = dt else { return None };
        if p.krate == CrateId::Core {
            return matches!(p.segments.as_slice(), [Segment::T(a,0), Segment::T(b,0), Segment::T(c,0)]
                if a.as_str()=="mem" && b.as_str()=="maybe_uninit" && c.as_str()=="MaybeUninit").then_some(Self::MaybeUninit);
        }
        if p.krate != CrateId::Vstd {
            return None;
        }
        match p.segments.as_slice() {
            [Segment::T(m, 0), Segment::T(n, 0)] if m.as_str() == "rwlock" => match n.as_str() {
                "RwLock" => Some(Self::Lock),
                "ReadHandle" => Some(Self::Reader),
                "WriteHandle" => Some(Self::Writer),
                _ => None,
            },
            [Segment::T(m, 0), Segment::T(v, 0), Segment::T(n, 0)]
                if m.as_str() == "cell"
                    && v.as_str() == "pcell_maybe_uninit"
                    && n.as_str() == "PCell" =>
            {
                Some(Self::Cell)
            }
            [Segment::T(a, 0), Segment::T(b, 0), Segment::T(c, 0)]
                if a.as_str() == "cell" && b.as_str() == "pcell" && c.as_str() == "PCell" =>
            {
                Some(Self::PrimitiveCell)
            }
            _ => None,
        }
    }
}

/// Both executable fields take ownership of their part of the one returned
/// value. A wildcard or borrowed projection needs a different cleanup rule.
pub(in crate::resource::memory) fn write_pattern(pattern: &Pattern) -> Option<[&Pattern; 2]> {
    let (v, h) = RwRecord::write_pair(&pattern.typ)?;
    let PatternX::Constructor(Dt::Tuple(2), _, fields) = &pattern.x else { return None };
    let [a, b] = fields.as_slice() else { return None };
    (a.name.as_str()=="0" && b.name.as_str()=="1" && crate::ast_util::types_equal(&a.a.typ,v)
        && crate::ast_util::types_equal(&b.a.typ,h) &&
        [&a.a,&b.a].into_iter().all(|p| matches!(&p.x, PatternX::Var(b) if matches!(b.by_ref,ByRef::No) && b.user_mut.is_some()))).then_some([&a.a,&b.a])
}

impl crate::resource::memory::analysis::Analysis<'_> {
    pub(in crate::resource::memory) fn split_writer_result(
        &mut self,
        source: &Place,
        fields: [&Pattern; 2],
        locals: &mut Vec<(crate::messages::Span, VarIdent)>,
        owned_locals: &mut Vec<VarIdent>,
    ) -> Result<(), VirErr> {
        let value = self.produce_place(source, &source.typ, false, &source.span)?;
        if !self.flow.reachable {
            return Ok(());
        }
        self.release_value(value, &source.span);
        let mut owner = self.result_owner.take();
        for (i, field) in fields.into_iter().enumerate() {
            let PatternX::Var(binding) = &field.x else { unreachable!() };
            if self.var_modes.get(&binding.name) != Some(&Mode::Exec) {
                return Err(crate::resource::memory::model::unsupported(
                    &field.span,
                    "an erased writer result binding",
                ));
            }
            let site = match &source.x {
                PlaceX::Temporary(call) => &call.span,
                _ => &source.span,
            };
            let slot = self.fresh_value(site, &field.typ)?;
            self.slots.insert(binding.name.clone(), slot);
            locals.push((field.span.clone(), binding.name.clone()));
            if self.layouts.owner(&binding.typ) {
                let child = owner
                    .as_mut()
                    .and_then(|o| {
                        o.children.remove(&crate::resource::memory::heap::OwnerSlot::Field(
                            Arc::new(i.to_string()),
                        ))
                    })
                    .ok_or_else(|| {
                        crate::resource::memory::model::unsupported(
                            &field.span,
                            "a writer result without its owned payload",
                        )
                    })?;
                self.heap.owners.insert(binding.name.clone(), child);
                owned_locals.push(binding.name.clone());
            }
        }
        if owner.is_some_and(|o| !o.children.is_empty()) {
            return Err(crate::resource::memory::model::unsupported(
                &source.span,
                "unmatched ownership in a writer result",
            ));
        }
        Ok(())
    }
}
