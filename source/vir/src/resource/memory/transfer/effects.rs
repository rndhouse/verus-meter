//! Ordered ownership effects shared by direct operations, helpers and loops.
//!
//! Blocks contain complete forests, not aggregate byte allowances. A block's
//! logical width is separate from its cost; nested repetition preserves both.

use super::*;
use crate::resource::memory::heap::OwnerSlot;

pub(in super::super) type Location = (VarIdent, Vec<OwnerSlot>, Vec<Expr>);

#[derive(Clone)]
pub(in super::super) enum Effect {
    Mutation(VarIdent),
    Read(VarIdent),
    Append {
        location: Location,
        typ: Typ,
        child: Value,
        element: u64,
        grow: bool,
    },
    Pop {
        location: Location,
        typ: Typ,
        token: Option<VarIdent>,
    },
    /// A complete ordered block of fresh children at relative runtime indices.
    AppendBlock {
        location: Location,
        typ: Typ,
        memory: Expr,
        length: Expr,
        minima: Minima,
        element: u64,
        grow: bool,
    },
    /// A completed batch of last-element removals, optionally linked to a transfer.
    PopBlock {
        location: Location,
        typ: Typ,
        amount: Expr,
        /// Ordered range identities when every removed child is transferred.
        flows: Option<Vec<VarIdent>>,
    },
    /// Append a whole range in extraction order from one persistent source.
    TransferBlock {
        location: Location,
        source: Location,
        typ: Typ,
        amount: Expr,
        flows: Vec<VarIdent>,
        minima: Minima,
        element: u64,
        grow: bool,
    },
    /// Checked operations restore this role's complete entry forest.
    Identity {
        location: Location,
        typ: Typ,
    },
}

impl Effect {
    pub(in super::super) fn location(&self) -> Option<&Location> {
        match self {
            Self::TransferBlock { location, .. }
            | Self::AppendBlock { location, .. }
            | Self::PopBlock { location, .. }
            | Self::Append { location, .. }
            | Self::Pop { location, .. }
            | Self::Identity { location, .. } => Some(location),
            _ => None,
        }
    }

    pub(super) fn root(&self) -> &VarIdent {
        match self {
            Self::Mutation(name) | Self::Read(name) => name,
            Self::TransferBlock { location, .. }
            | Self::AppendBlock { location, .. }
            | Self::PopBlock { location, .. }
            | Self::Append { location, .. }
            | Self::Pop { location, .. }
            | Self::Identity { location, .. } => &location.0,
        }
    }
}

impl Effect {
    /// Visit forest expressions, scalar observations and reservation floors.
    pub(super) fn expressions(&self, visit: &mut impl FnMut(&Expr)) {
        let minima = match self {
            Self::Append { child: Value::Owner(node), .. } => {
                visit(&node.memory);
                Some(&node.minima)
            }
            Self::AppendBlock { memory, length, minima, .. } => {
                visit(memory);
                visit(length);
                Some(minima)
            }
            Self::TransferBlock { amount, minima, .. } => {
                visit(amount);
                Some(minima)
            }
            Self::PopBlock { amount, .. } => {
                visit(amount);
                None
            }
            _ => None,
        };
        if let Some(minima) = minima {
            for floor in minima.values() {
                visit(&floor.capacity);
            }
        }
    }

    /// Resolve a helper's parameter role against its checked caller place.
    pub(super) fn instantiate(
        &self,
        prefix: &Location,
        values: &HashMap<VarIdent, Expr>,
        arguments: &HashMap<usize, Value>,
    ) -> Self {
        let mut result = self.clone();
        let location = match &mut result {
            // Parameter programs do not export unresolved range endpoints.
            Self::TransferBlock { .. } => {
                unreachable!("range endpoints require a checked source role")
            }
            Self::Mutation(name) | Self::Read(name) => {
                *name = prefix.0.clone();
                return result;
            }
            Self::Append { location, child, .. } => {
                *child = match child {
                    Value::Owner(Node { origin: Some(index), .. }) => arguments[index].clone(),
                    _ => instantiate_value(child, values),
                };
                location
            }
            Self::AppendBlock { location, memory, length, minima, .. } => {
                *memory = substitute(memory, values);
                *length = substitute(length, values);
                for floor in minima.values_mut() {
                    floor.capacity = substitute(&floor.capacity, values);
                }
                location
            }
            Self::PopBlock { location, amount, .. } => {
                *amount = substitute(amount, values);
                location
            }
            Self::Pop { location, .. } | Self::Identity { location, .. } => location,
        };
        location.0 = prefix.0.clone();
        location.1 = prefix.1.iter().chain(location.1.iter()).cloned().collect();
        location.2 = prefix
            .2
            .iter()
            .chain(location.2.iter())
            .map(|value| substitute(value, values))
            .collect();
        result
    }
}
