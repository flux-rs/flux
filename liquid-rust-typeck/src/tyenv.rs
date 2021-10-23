use crate::ty::{Region, Ty, TyKind};
use liquid_rust_core::ir::{self, Local};
use rustc_hash::FxHashMap;

pub struct TyEnv {
    locals: FxHashMap<Local, Ty>,
}

impl TyEnv {
    pub fn new() -> Self {
        TyEnv {
            locals: FxHashMap::default(),
        }
    }

    pub fn insert_local(&mut self, local: Local, ty: Ty) {
        self.locals.insert(local, ty);
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.locals.get(&local).cloned().unwrap()
    }

    pub fn lookup_place(&self, place: &ir::Place) -> Ty {
        let mut ty = self.lookup_local(place.local);
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(Region::Concrete(local))) => {
                    ty = self.lookup_local(*local);
                }
                _ => {
                    unreachable!("invalid place for lookup: `{:?}`", place);
                }
            }
        }
        ty
    }

    pub fn write_place(&mut self, place: &ir::Place, new_ty: Ty) {
        let mut ty = self.lookup_local(place.local);
        let mut local = place.local;
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(Region::Concrete(l))) => {
                    local = *l;
                    ty = self.lookup_local(*l);
                }
                _ => {
                    unreachable!("invalid place for write: `{:?}`", place);
                }
            }
        }
        self.insert_local(local, new_ty);
    }
}
