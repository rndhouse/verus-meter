//! Connect the owned FnOnce entry to the original executable body and cleanup.
//! A borrowed Fn/FnMut body returning does not itself destroy the environment.
//! Keep the adapter's call, destructor and return as separate compiler points;
//! unwind edges remain in the retained graph and require separate panic proofs.

use super::{
    super::{model::unsupported, synchronization::flow::*},
    Closure,
};
use crate::{
    ast::{ClosureKind, Fun, VirErr},
    messages::Span,
};
use std::collections::BTreeSet;

/// How execution of the actual body relates to the retained environment frame.
/// This validates transport, not allocation coverage or a worker memory bound.
#[derive(Clone, PartialEq, Eq)]
pub enum Invocation {
    /// The FnOnce body itself owns the environment and executes its cleanup.
    OwnedBody,
    /// A compiler adapter lends the environment to its body, then destroys its
    /// remaining owners. Inline argument storage remains until adapter return.
    /// All points belong to `Closure::once_adapter`, not the original body.
    Adapter {
        /// Call of the original body with a borrow of this owned environment.
        call: Point,
        /// Destruction of remaining captured owners, if required by the layout.
        release: Option<Point>,
        /// Return of the body's result and end of the adapter's inline frame.
        returned: Point,
    },
}

impl Invocation {
    /// Validate the selected zero-argument closure's compiler entry and normal
    /// cleanup transport. This does not prove panic freedom or account for the
    /// body or unwind storage; their graphs remain separate proof obligations.
    /// `owns` must come from the executable capture layout: an owning environment
    /// requires a real destruction point after the borrowed body returns.
    pub fn checked(closure: &Closure, owns: bool, span: &Span) -> Result<Self, VirErr> {
        if closure.body.arguments != 1 || closure.body.locals < 2 {
            return Err(unsupported(span, "a worker invocation with explicit closure arguments"));
        }
        match (closure.kind, &closure.once_adapter) {
            (ClosureKind::FnOnce, None) => Ok(Self::OwnedBody),
            (ClosureKind::Fn | ClosureKind::FnMut, Some(adapter)) => {
                Self::adapter(adapter, &closure.function, owns, span)
            }
            _ => Err(unsupported(span, "a worker without its exact compiler FnOnce invocation")),
        }
    }

    fn adapter(graph: &Graph, body: &Fun, owns: bool, span: &Span) -> Result<Self, VirErr> {
        let invalid = || unsupported(span, "an unmodeled compiler FnOnce invocation or cleanup");
        // The selected worker signature has no explicit arguments. Its adapter
        // takes owned Self and the unit Args tuple; the original body takes Self.
        if graph.arguments != 2 || graph.locals < 3 {
            return Err(invalid());
        }
        let whole = |place: &Place, local| place.local == local && place.projection.is_empty();
        let mut aliases = BTreeSet::new();
        let mut visited = BTreeSet::new();
        let mut block = 0;
        let mut call = None;
        let mut release = None;
        loop {
            if !visited.insert(block) {
                return Err(invalid());
            }
            let node = graph.blocks.get(block).ok_or_else(invalid)?;
            if node.cleanup {
                return Err(invalid());
            }
            for (_, statement) in &node.statements {
                match statement {
                    Statement::Nop => {}
                    Statement::StorageLive(local) | Statement::StorageDead(local)
                        if *local > graph.arguments && *local < graph.locals =>
                    {
                        aliases.remove(local);
                    }
                    Statement::Assign(target, Value::Borrow(source))
                        if call.is_none()
                            && whole(source, 1)
                            && target.local > graph.arguments
                            && target.local < graph.locals
                            && target.projection.is_empty() =>
                    {
                        aliases.insert(target.local);
                    }
                    // No operation may overwrite the return value, move Self,
                    // or construct a replacement environment before invocation.
                    _ => return Err(invalid()),
                }
            }
            let point = Point { block, statement: node.statements.len() };
            match &node.terminator {
                Terminator::Goto(next) => block = *next,
                Terminator::Call {
                    call: Call::Closure(target),
                    arguments,
                    destination,
                    next: Some(next),
                    outcomes,
                    ..
                } if call.is_none()
                    && target == body
                    && whole(destination, 0)
                    && outcomes.is_empty() =>
                {
                    let [Operand::Move(receiver), Operand::Move(args)] = arguments.as_slice()
                    else {
                        return Err(invalid());
                    };
                    if !receiver.projection.is_empty()
                        || !aliases.contains(&receiver.local)
                        || !whole(args, 2)
                    {
                        return Err(invalid());
                    }
                    aliases.remove(&receiver.local);
                    call = Some(point);
                    block = *next;
                }
                Terminator::Drop { place, next, .. }
                    if call.is_some() && release.is_none() && whole(place, 1) =>
                {
                    release = Some(point);
                    block = *next;
                }
                Terminator::Return if call.is_some() && (!owns || release.is_some()) => {
                    return Ok(Self::Adapter { call: call.unwrap(), release, returned: point });
                }
                _ => return Err(invalid()),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::HashMap, sync::Arc};

    fn span() -> Span {
        Span {
            raw_span: Arc::new(()),
            id: 1,
            data: Arc::new([]),
            as_string: "FnOnce adapter".into(),
        }
    }

    fn local(local: usize) -> Place {
        Place { local, projection: vec![] }
    }

    /// Actual pinned compiler shim shape: borrow Self, call the original body,
    /// drop Self, return the body's result. Failure cleanup stays in its graph.
    fn graph(body: &Fun) -> Graph {
        let block =
            |terminator, cleanup| Block { statements: vec![], span: span(), terminator, cleanup };
        let mut entry = block(
            Terminator::Call {
                call: Call::Closure(body.clone()),
                arguments: vec![Operand::Move(local(3)), Operand::Move(local(2))],
                destination: local(0),
                outcomes: vec![],
                next: Some(1),
                unwind: Unwind::Cleanup(3),
            },
            false,
        );
        entry.statements.push((span(), Statement::Assign(local(3), Value::Borrow(local(1)))));
        Graph {
            blocks: vec![
                entry,
                block(Terminator::Drop { place: local(1), next: 2, unwind: Unwind::Exit }, false),
                block(Terminator::Return, false),
                block(Terminator::Drop { place: local(1), next: 4, unwind: Unwind::Exit }, true),
                block(Terminator::Unwind, true),
            ],
            bindings: HashMap::new(),
            locals: 4,
            arguments: 2,
        }
    }

    #[test]
    fn borrowed_body_return_does_not_end_the_owned_environment() {
        let body = crate::fun!(crate::ast::CrateId::Internal => "worker_test"; "body");
        let mut graph = graph(&body);
        assert!(matches!(
            Invocation::adapter(&graph, &body, true, &span()).unwrap(),
            Invocation::Adapter {
                call: Point { block: 0, statement: 1 },
                release: Some(Point { block: 1, statement: 0 }),
                returned: Point { block: 2, statement: 0 },
            }
        ));
        graph.blocks[1].terminator = Terminator::Goto(2);
        assert!(Invocation::adapter(&graph, &body, true, &span()).is_err());
        // A Copy environment has no owned descendants to destroy, but its
        // inline frame still survives the body call until the adapter returns.
        assert!(matches!(
            Invocation::adapter(&graph, &body, false, &span()).unwrap(),
            Invocation::Adapter { release: None, returned: Point { block: 2, .. }, .. }
        ));
    }

    #[test]
    fn invocation_requires_exact_self_body_and_unmodified_return_transport() {
        let body = crate::fun!(crate::ast::CrateId::Internal => "worker_test"; "body");
        let other = crate::fun!(crate::ast::CrateId::Internal => "worker_test"; "other");
        let original = graph(&body);
        assert!(Invocation::adapter(&original, &other, true, &span()).is_err());
        let mut wrong_self = original.clone();
        wrong_self.blocks[0].statements[0].1 = Statement::Assign(local(3), Value::Borrow(local(2)));
        assert!(Invocation::adapter(&wrong_self, &body, true, &span()).is_err());
        let mut replaced = original.clone();
        replaced.blocks[2].statements.push((span(), Statement::Assign(local(0), Value::Other)));
        assert!(Invocation::adapter(&replaced, &body, true, &span()).is_err());
        let mut skipped = original.clone();
        skipped.blocks[0].terminator = Terminator::Goto(1);
        assert!(Invocation::adapter(&skipped, &body, true, &span()).is_err());
        let mut cycle = original;
        cycle.blocks[2].terminator = Terminator::Goto(0);
        assert!(Invocation::adapter(&cycle, &body, true, &span()).is_err());
    }
}
