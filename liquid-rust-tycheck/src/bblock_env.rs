use crate::{env::Env, glob_env::GlobEnv};

use liquid_rust_common::index::IndexMap;
use liquid_rust_mir::{BBlockId, Func};
use liquid_rust_ty::Ty;

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
    pub(crate) fn new<S>(func: &Func<S>, genv: &GlobEnv) -> Self {
        let mut types = IndexMap::new();

        for (bb_id, _) in func.bblocks() {
            let input = func
                .local_decls()
                .map(|(_, base_ty)| Ty::Refined(*base_ty, genv.new_pred()));
            let output = func
                .local_decls()
                .map(|(_, base_ty)| Ty::Refined(*base_ty, genv.new_pred()));

            let bb_ty = BBlockTy {
                input: Env::new(input),
                output: Env::new(output),
            };

            println!("{}: {}", bb_id, bb_ty);

            types.insert(bb_ty);
        }

        Self { types }
    }

    pub(crate) fn get_ty(&self, bb_id: BBlockId) -> &BBlockTy {
        self.types.get(bb_id).unwrap()
    }
}
