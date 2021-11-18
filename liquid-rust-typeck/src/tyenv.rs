use std::fmt;

use crate::{
    constraint_builder::Cursor,
    inference,
    ty::{Expr, ExprKind, KVid, Pred, RVid, Region, Ty, TyKind, Var},
};
use liquid_rust_common::{
    disjoint_sets::{DisjointSetsMap, Set},
    index::{Idx, IndexGen, IndexVec},
};
use liquid_rust_core::{
    self as core,
    ir::{self, Local},
};
use rustc_hash::FxHashMap;

#[derive(Clone)]
pub struct TyEnv {
    regions: DisjointSetsMap<RVid, RegionKind>,
}

pub struct TyEnvBuilder {
    regions: IndexVec<RVid, Option<Ty>>,
}

impl TyEnvBuilder {
    pub fn new(locals: usize) -> Self {
        TyEnvBuilder {
            regions: IndexVec::from_elem_n(None, locals),
        }
    }

    pub fn define_local(&mut self, local: ir::Local, ty: Ty) {
        self.regions[RVid::new(local.as_usize())] = Some(ty);
    }

    pub fn define_abstract_region(&mut self, ty: Ty) -> RVid {
        self.regions.push(Some(ty))
    }

    pub fn build(self) -> TyEnv {
        TyEnv {
            regions: DisjointSetsMap::from_iter(
                self.regions
                    .into_iter()
                    .map(|rkind| RegionKind::Strong(rkind.unwrap())),
            ),
        }
    }
}

#[derive(Clone)]
enum RegionKind {
    Strong(Ty),
    Weak { bound: Ty, ty: Ty },
}

impl RegionKind {
    fn ty(&self) -> Ty {
        match self {
            RegionKind::Strong(ty) => ty.clone(),
            RegionKind::Weak { ty, .. } => ty.clone(),
        }
    }

    fn ty_mut(&mut self) -> &mut Ty {
        match self {
            RegionKind::Strong(ty) => ty,
            RegionKind::Weak { ty, .. } => ty,
        }
    }
}

impl TyEnv {
    pub fn new() -> TyEnv {
        TyEnv {
            regions: DisjointSetsMap::new(),
        }
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.lookup_region(RVid::new(local.as_usize()))
    }

    pub fn lookup_region(&self, rvid: RVid) -> Ty {
        self.regions[rvid].ty()
    }

    pub fn lookup_place(&self, place: &ir::Place) -> Ty {
        let (_, ty) = self.walk_place(place);
        ty
    }

    pub fn update_region(&mut self, cursor: &mut Cursor, rvid: RVid, new_ty: Ty) {
        match &self.regions[rvid] {
            RegionKind::Strong(_) => self.regions[rvid] = RegionKind::Strong(new_ty),
            RegionKind::Weak { bound, .. } => {
                cursor.subtyping(new_ty, bound.clone());
            }
        }
    }

    pub fn get_region(&self, place: &ir::Place) -> Region {
        let (rvid, _) = self.walk_place(place);
        self.regions.set(rvid).collect()
    }

    pub fn move_place(&mut self, place: &ir::Place) -> Ty {
        let mut rvid = RVid::new(place.local.as_usize());
        let mut ty = self.lookup_region(rvid);
        self.regions[RVid::new(place.local.as_usize())] =
            RegionKind::Strong(TyKind::Uninit.intern());
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(region)) => {
                    self.regions[region[0]] = RegionKind::Strong(TyKind::Uninit.intern());
                    ty = self.lookup_region(region[0]);
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
            TyKind::Uninit | TyKind::Refine(..) | TyKind::Param(_) => {
                // TODO: debug check new_ty has the same "shape" as ty
                self.update_region(cursor, local, new_ty);
            }
            TyKind::MutRef(_) => {
                todo!("implement update of mutable references")
            }
            TyKind::Exists(..) => unreachable!("unpacked existential: `{:?}`", ty),
        }
    }

    fn walk_place(&self, place: &ir::Place) -> (RVid, Ty) {
        let mut rvid = RVid::new(place.local.as_usize());
        let mut ty = self.lookup_region(rvid);
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::MutRef(region)) => {
                    rvid = region[0];
                    ty = self.lookup_region(rvid);
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        (rvid, ty)
    }

    pub fn infer_bb_env(
        &self,
        cursor: &mut Cursor,
        shape: DisjointSetsMap<RVid, inference::Ty>,
    ) -> TyEnv {
        let regions = shape.map_values(|mut region, ty| {
            // We are assuming the region in self is a subset of the region in shape.
            let region_size = region.len();
            let rvid = region.next().unwrap();
            let ty = match &*ty {
                inference::TyS::Refine(_, _) => self.lookup_region(rvid),
                inference::TyS::Exists(bty) => {
                    let pred = cursor.fresh_kvar(bty.sort());
                    TyKind::Exists(*bty, pred).intern()
                }
                inference::TyS::Uninit => TyKind::Uninit.intern(),
                inference::TyS::MutRef(region) => TyKind::MutRef(region.clone()).intern(),
                inference::TyS::Param(param) => TyKind::Param(*param).intern(),
            };
            if region_size > 1 {
                RegionKind::Weak {
                    bound: ty.clone(),
                    ty,
                }
            } else {
                RegionKind::Strong(ty)
            }
        });
        TyEnv { regions }
    }

    pub fn iter(&self) -> impl Iterator<Item = (Set<RVid>, Ty)> + '_ {
        self.regions
            .iter()
            .map(|(region, region_kind)| (region, region_kind.ty()))
    }

    pub fn unpack(&mut self, cursor: &mut Cursor) {
        for region_kind in self.regions.values_mut() {
            *region_kind.ty_mut() = cursor.unpack(region_kind.ty());
        }
    }
}

impl fmt::Debug for TyEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.regions, f)
    }
}

impl fmt::Debug for RegionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegionKind::Strong(ty) => write!(f, "{:?}", ty),
            RegionKind::Weak { bound, ty } => {
                write!(f, "{:?} <: {:?}", ty, bound)
            }
        }
    }
}

impl From<DisjointSetsMap<Local, inference::Ty>> for TyEnv {
    fn from(map: DisjointSetsMap<Local, inference::Ty>) -> Self {
        todo!()
    }
}
