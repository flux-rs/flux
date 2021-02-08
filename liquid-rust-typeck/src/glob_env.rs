use std::collections::HashMap;

use liquid_rust_core::{
    names::{ContId, FnId},
    ty::{ContTy, FnTy},
};

#[derive(Default)]
pub struct GlobEnv {
    fn_tys: HashMap<FnId, FnTy>,
    conts: HashMap<(FnId, ContId), ContTy>,
}

impl GlobEnv {
    pub fn new() -> Self {
        Self {
            fn_tys: HashMap::new(),
            conts: HashMap::new(),
        }
    }

    pub fn insert_fn(&mut self, fn_id: FnId, ty: FnTy, conts: HashMap<ContId, ContTy>) {
        self.fn_tys.insert(fn_id, ty);
        self.conts.extend(
            conts
                .into_iter()
                .map(|(cont_id, cont_ty)| ((fn_id, cont_id), cont_ty)),
        );
    }

    pub fn get_ty(&self, fn_id: FnId) -> Option<&FnTy> {
        self.fn_tys.get(&fn_id)
    }

    pub fn get_cont_ty(&self, fn_id: FnId, cont_id: ContId) -> Option<&ContTy> {
        self.conts.get(&(fn_id, cont_id))
    }
}
