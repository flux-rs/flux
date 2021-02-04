use std::collections::HashMap;

use crate::{names::FnId, ty::FnTy};

#[derive(Default)]
pub struct Program {
    pub fns: HashMap<FnId, FnTy>,
}

impl Program {
    pub fn new() -> Self {
        Program {
            fns: HashMap::new(),
        }
    }

    pub fn add_fn(&mut self, fn_id: FnId, fn_ty: FnTy) {
        self.fns.insert(fn_id, fn_ty);
    }

    pub fn get_fn(&self, fn_id: FnId) -> Option<&FnTy> {
        self.fns.get(&fn_id)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&FnId, &FnTy)> {
        self.fns.iter()
    }
}
