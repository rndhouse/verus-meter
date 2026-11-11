//! Partition incoming lifetimes independently of this frame's allocation charges.
//!
//! The body tracks identities, while the checked transfer evaluator supplies
//! their forest expressions. Each fixed node owns its descriptor and runtime
//! descendants; fixed children receive separate identities so partial drops
//! remain independent. Old identities survive in earlier peak profiles only.

use super::{analysis::Analysis, heap::Owner, model::unsupported, transfer::checked::InputSplit};
use crate::{ast::VirErr, messages::Span};

impl Analysis<'_> {
    pub(super) fn split_input(
        &mut self,
        span: &Span,
        location: &super::paths::LocalPath,
        child: &mut Owner,
    ) -> Result<Option<InputSplit>, VirErr> {
        let (name, path) = location;
        let root = self.heap.root(name).expect("tracked extraction receiver");
        let ancestor = (0..=path.len()).rev().find_map(|depth| {
            let owner = root.at(&path[..depth])?;
            // Fixed child regions are independent of this node's identity.
            // A fresh replacement beneath one must not split the ancestor.
            if depth < path.len() && !matches!(path[depth], super::heap::OwnerSlot::Element(_)) {
                return None;
            }
            owner.input.map(|input| (depth, input, owner.input_divisible))
        });
        let Some((depth, source, divisible)) = ancestor else {
            return Ok(None);
        };
        self.heap.check_transfer(name, span)?;
        if !divisible {
            return Err(unsupported(span, "owned incoming extraction after indexed replacement"));
        }
        let remaining = self.transitions.fresh_region();
        self.storage.release_input(source);
        self.storage.add_input(remaining);
        self.heap.root_mut(name).unwrap().at_mut(&path[..depth]).unwrap().input = Some(remaining);
        let mut selected = std::collections::BTreeMap::new();
        fn mark(analysis: &mut Analysis<'_>, owner: &mut Owner) {
            let input = analysis.transitions.fresh_region();
            analysis.storage.add_input(input);
            owner.input = Some(input);
            for child in owner.children.values_mut() {
                mark(analysis, child);
            }
        }
        mark(self, child);
        child.visit_paths(&mut vec![], &mut |path, owner| {
            selected.insert(path.clone(), owner.input.unwrap());
        });
        Ok(Some(InputSplit { source, depth, remaining, selected }))
    }
}
