use crate::ty::Ty;
use liquid_rust_core::ir::Local;
use rustc_hash::FxHashMap;

pub struct LocalEnv {
    locals: FxHashMap<Local, Ty>,
}

impl LocalEnv {
    pub fn new() -> Self {
        LocalEnv {
            locals: FxHashMap::default(),
        }
    }

    pub fn insert_local(&mut self, local: Local, ty: Ty) {
        self.locals.insert(local, ty);
    }

    pub fn lookup_local(&mut self, local: Local) -> Ty {
        self.locals.get(&local).cloned().unwrap()
    }
}
