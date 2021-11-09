use std::fmt;

use crate::{
    constraint_builder::Cursor,
    inference,
    subst::Subst,
    ty::{Expr, ExprKind, KVid, Pred, Region, Ty, TyKind, Var},
};
use liquid_rust_common::{
    disjoint_sets::{DisjointSetsMap, Set},
    index::IndexGen,
};
use liquid_rust_core::ir::{self, Local};
use rustc_hash::FxHashMap;

#[derive(Clone)]
pub struct TyEnv {
    types: DisjointSetsMap<Local, (RegionKind, Ty)>,
}

#[derive(Debug, Clone)]
enum RegionKind {
    Concrete,
    Abstract(Ty),
}

impl TyEnv {
    pub fn new() -> TyEnv {
        TyEnv {
            types: DisjointSetsMap::new(),
        }
    }

    pub fn push_local(&mut self, ty: Ty) {
        self.types.push((RegionKind::Concrete, ty));
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.types[local].1.clone()
    }

    pub fn lookup_place(&self, place: &ir::Place) -> Ty {
        let (_, ty) = self.walk_place(place);
        ty
    }

    fn update_region(&mut self, cursor: &mut Cursor, local: Local, new_ty: Ty) {
        match self.types[local].0.clone() {
            RegionKind::Concrete => self.types[local] = (RegionKind::Concrete, new_ty),
            RegionKind::Abstract(bound) => {
                cursor.subtyping(new_ty, bound);
            }
        }
    }

    pub fn get_region(&self, place: &ir::Place) -> Region {
        let (local, _) = self.walk_place(place);
        self.types.set(local).collect()
    }

    pub fn move_place(&mut self, place: &ir::Place) -> Ty {
        let mut local = place.local;
        let mut ty = self.lookup_local(place.local);
        self.types[place.local] = (RegionKind::Concrete, TyKind::Uninit.intern());
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(region)) => {
                    self.types[region[0]] = (RegionKind::Concrete, TyKind::Uninit.intern());
                    ty = self.lookup_local(region[0]);
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        ty
    }

    pub fn write_place(&mut self, cursor: &mut Cursor, place: &ir::Place, new_ty: Ty) {
        let (local, ty) = self.walk_place(place);

        match ty.kind() {
            TyKind::Uninit | TyKind::Refine(..) => {
                self.update_region(cursor, local, new_ty);
            }
            TyKind::MutRef(_) => {
                todo!("implement update of mutable references")
            }
            TyKind::Exists(..) => unreachable!("unpacked existential: `{:?}`", ty),
        }
    }

    fn walk_place(&self, place: &ir::Place) -> (Local, Ty) {
        let mut local = place.local;
        let mut ty = self.lookup_local(place.local);
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(region)) => {
                    local = region[0];
                    ty = self.lookup_local(local);
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        (local, ty)
    }

    pub fn infer_bb_env(
        &self,
        cursor: &mut Cursor,
        shape: DisjointSetsMap<Local, inference::Ty>,
        name_gen: &IndexGen<Var>,
    ) -> TyEnv {
        let types = shape.map(|local, region_size, ty| {
            let ty = match &*ty {
                inference::TyS::Refine(_, _) => self.lookup_local(local),
                inference::TyS::Exists(bty) => {
                    let fresh = name_gen.fresh();
                    let pred = cursor.fresh_kvar(fresh, bty.sort());
                    TyKind::Exists(*bty, fresh, pred).intern()
                }
                inference::TyS::Uninit => TyKind::Uninit.intern(),
                inference::TyS::MutRef(region) => TyKind::MutRef(region.clone()).intern(),
            };
            if region_size > 1 {
                (RegionKind::Abstract(ty.clone()), ty)
            } else {
                (RegionKind::Concrete, ty)
            }
        });
        TyEnv { types }
    }

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (impl ExactSizeIterator<Item = Local> + '_, Ty)> + '_ {
        self.types
            .iter()
            .map(|(set_iter, (_, ty))| (set_iter, ty.clone()))
    }

    pub fn unpack(&mut self, cursor: &mut Cursor, name_gen: &IndexGen<Var>) {
        for (region_kind, ty) in self.types.values_mut() {
            *ty = cursor.unpack(name_gen, ty.clone());
        }
    }
}

impl fmt::Debug for TyEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.types, f)
    }
}

impl From<DisjointSetsMap<Local, inference::Ty>> for TyEnv {
    fn from(map: DisjointSetsMap<Local, inference::Ty>) -> Self {
        todo!()
    }
}
