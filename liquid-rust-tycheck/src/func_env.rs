use liquid_rust_common::index::IndexMap;
use liquid_rust_mir::{ty::FuncTy, FuncId};

/// Environment for the types of functions.
pub(crate) struct FuncEnv {
    types: IndexMap<FuncId, FuncTy>,
}

impl FuncEnv {
    pub(crate) fn new(types: impl Iterator<Item = FuncTy>) -> Self {
        Self {
            types: IndexMap::from_raw(types.collect()),
        }
    }

    pub(crate) fn get_ty(&self, func_id: FuncId) -> Option<&FuncTy> {
        self.types.get(func_id)
    }
}
