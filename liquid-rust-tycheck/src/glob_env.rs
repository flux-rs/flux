use liquid_rust_common::index::{IndexGen, IndexMap};
use liquid_rust_mir::{
    ty::{FuncTy, Hole, HoleId},
    FuncId, Program,
};

pub(crate) struct GlobEnv {
    hole_gen: IndexGen<HoleId>,
    types: IndexMap<FuncId, FuncTy>,
}

impl GlobEnv {
    pub(crate) fn new(prog: &Program) -> Self {
        let mut types = IndexMap::new();

        for (_, func) in prog.iter() {
            types.insert(func.ty().clone());
        }

        Self {
            types,
            hole_gen: IndexGen::new(),
        }
    }

    pub(crate) fn new_pred(&self) -> Hole {
        Hole {
            id: self.hole_gen.generate(),
            substs: Vec::new(),
        }
    }

    pub(crate) fn get_ty(&self, func_id: FuncId) -> &FuncTy {
        self.types.get(func_id).unwrap()
    }
}
