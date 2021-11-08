use std::fmt;

use crate::{
    constraint_builder::Cursor,
    inference,
    subst::Subst,
    ty::{Expr, ExprKind, KVar, KVid, Pred, Region, Ty, TyKind, Var},
};
use liquid_rust_common::{
    disjoint_sets::{DisjointSetsMap, SetIter},
    index::IndexGen,
};
use liquid_rust_core::ir::{self, Local};
use rustc_hash::FxHashMap;

#[derive(Clone)]
pub struct TyEnv {
    types: DisjointSetsMap<Local, Ty>,
}

impl TyEnv {
    pub fn new() -> TyEnv {
        TyEnv {
            types: DisjointSetsMap::new(),
        }
    }

    pub fn push_local(&mut self, ty: Ty) {
        self.types.push(ty);
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.types[local].clone()
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
        self.types[place.local] = TyKind::Uninit.intern();
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(region)) => {
                    self.types[region[0]] = TyKind::Uninit.intern();
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
            (TyKind::Refine(..) | TyKind::Uninit, TyKind::Refine(..)) => {
                self.types.insert(local, new_ty);
            }
            (TyKind::Uninit, TyKind::MutRef(_)) => {
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

    pub fn infer_bb_env(
        &self,
        shape: DisjointSetsMap<Local, inference::Ty>,
        name_gen: &IndexGen<Var>,
        kvid_gen: &IndexGen<KVid>,
    ) -> TyEnv {
        let types = shape.map(|local, ty| match &*ty {
            inference::TyS::Refine(_, _) => self.types[local].clone(),
            inference::TyS::Exists(bty) => {
                let fresh = name_gen.fresh();
                let kvid = kvid_gen.fresh();
                let kvar = KVar::new(kvid, vec![Expr::from(fresh)]);
                TyKind::Exists(*bty, fresh, Pred::KVar(kvar)).intern()
            }
            inference::TyS::Uninit => TyKind::Uninit.intern(),
            inference::TyS::MutRef(region) => TyKind::MutRef(region.clone()).intern(),
        });
        TyEnv { types }
    }

    pub fn iter(&self) -> impl Iterator<Item = (SetIter<Local, Ty>, Ty)> + '_ {
        self.types
            .iter()
            .map(|(set_iter, ty)| (set_iter, ty.clone()))
    }

    pub fn unpack(&mut self, cursor: &mut Cursor, name_gen: &IndexGen<Var>) {
        for ty in self.types.values_mut() {
            // FIXME: this code is duplicated in crate::lib::unpack
            match ty.kind() {
                TyKind::Exists(bty, evar, p) => {
                    let fresh = name_gen.fresh();
                    cursor.push_forall(
                        fresh,
                        bty.sort(),
                        Subst::new([(*evar, ExprKind::Var(fresh).intern())]).subst_pred(p.clone()),
                    );
                    *ty = TyKind::Refine(*bty, ExprKind::Var(fresh).intern()).intern();
                }
                _ => {}
            };
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
