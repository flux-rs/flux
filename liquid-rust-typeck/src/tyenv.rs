use std::fmt;

use crate::{
    constraint_builder::Cursor,
    subst::Subst,
    ty::{ExprKind, Region, Ty, TyKind, Var},
};
use liquid_rust_common::{disjoint_sets::DisjointSetsMap, index::IndexGen};
use liquid_rust_core::ir::{self, Local};
use rustc_hash::FxHashMap;

#[derive(Clone)]
pub struct TyEnv<'a> {
    types: DisjointSetsMap<Local, Ty>,
    // locals: FxHashMap<Local, Ty>,
    name_gen: &'a IndexGen<Var>,
}

impl TyEnv<'_> {
    pub fn new(name_gen: &IndexGen<Var>, locals: usize) -> TyEnv {
        TyEnv {
            name_gen,
            types: DisjointSetsMap::new(locals),
        }
    }

    pub fn define_local(&mut self, local: Local, ty: Ty) {
        self.types.insert(local, ty);
    }

    pub fn lookup_place(&self, place: &ir::Place) -> Ty {
        let (_, ty) = self.walk_place(place);
        ty
    }

    pub fn get_region(&self, place: &ir::Place) -> Region {
        let (local, _) = self.walk_place(place);
        self.types.iter_set(local).collect()
    }

    pub fn move_place(&mut self, place: &ir::Place) -> Ty {
        let mut local = place.local;
        let mut ty = self.types[place.local].clone();
        self.types[place.local] = TyKind::Uninit(ty.layout()).intern();
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(region)) => {
                    self.types[region[0]] = TyKind::Uninit(ty.layout()).intern();
                    ty = self.types[region[0]].clone();
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        ty
    }

    pub fn write_place(&mut self, place: &ir::Place, new_ty: Ty) {
        let (local, ty) = self.walk_place(place);

        match (ty.kind(), new_ty.kind()) {
            (TyKind::Refine(..) | TyKind::Uninit(_), TyKind::Refine(..)) => {
                self.types.insert(local, new_ty);
            }
            (TyKind::Uninit(_), TyKind::MutRef(_)) => {
                self.types.insert(local, new_ty);
            }
            (TyKind::MutRef(_), TyKind::MutRef(_)) => {
                todo!("implement update of mutable references")
            }
            _ => unreachable!("unexpected types: `{:?}` `{:?}`", ty, new_ty),
        }
    }

    fn walk_place(&self, place: &ir::Place) -> (Local, Ty) {
        let mut local = place.local;
        let mut ty = self.types[place.local].clone();
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(region)) => {
                    local = region[0];
                    ty = self.types[local].clone();
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        (local, ty)
    }
}

impl fmt::Debug for TyEnv<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.types, f)
    }
}
