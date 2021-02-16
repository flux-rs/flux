use crate::local_env::LocalEnv;

use liquid_rust_common::index::IndexMap;
use liquid_rust_mir::BBlockId;

/// Environment for the types of basic blocks.
///
/// The type of a basic block is a local environment. Intuitively, this environment encodes the
/// necessary preconditions to be able to jump to the block.
pub(crate) struct BBlockEnv {
    types: IndexMap<BBlockId, LocalEnv>,
}

impl BBlockEnv {
    pub(crate) fn new() -> Self {
        Self {
            types: IndexMap::new(),
        }
    }

    pub(crate) fn insert(&mut self, env: LocalEnv) -> BBlockId {
        self.types.insert(env)
    }

    pub(crate) fn get_ty(&self, bb_id: BBlockId) -> Option<&LocalEnv> {
        self.types.get(bb_id)
    }
}
