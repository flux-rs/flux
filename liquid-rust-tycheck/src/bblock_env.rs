use crate::{env::Env, glob_env::GlobEnv};

use liquid_rust_common::index::IndexMap;
use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{
    ty::{Predicate, Ty},
    BBlockId, Func,
};

use std::fmt;

#[derive(Clone)]
pub(crate) struct BBlockTy {
    pub input: Env,
    pub output: Env,
}

impl fmt::Display for BBlockTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ▷ {}", self.input, self.output)
    }
}

pub(crate) struct BBlockEnv {
    types: IndexMap<BBlockId, BBlockTy>,
}

impl BBlockEnv {
    pub(crate) fn new(func: &Func, genv: &GlobEnv, emitter: &mut Emitter) -> Self {
        let mut types = IndexMap::new();

        for (bb_id, _) in func.bblocks() {
            let input = Env::new(func.local_decls().map(|(_, base_ty)| {
                let hole = genv.new_pred();
                emitter.add_wf(*base_ty, hole.id);
                Ty::Refined(*base_ty, Predicate::Hole(hole))
            }));
            let output = Env::new(func.local_decls().map(|(_, base_ty)| {
                let hole = genv.new_pred();
                emitter.add_wf(*base_ty, hole.id);
                Ty::Refined(*base_ty, Predicate::Hole(hole))
            }));

            let bb_ty = BBlockTy { input, output };

            println!("{}: {}", bb_id, bb_ty);

            types.insert(bb_ty);
        }

        Self { types }
    }

    pub(crate) fn get_ty(&self, bb_id: BBlockId) -> &BBlockTy {
        self.types.get(bb_id).unwrap()
    }
}
