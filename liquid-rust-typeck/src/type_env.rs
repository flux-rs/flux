use crate::{
    constraint_builder::Cursor,
    ty::{BaseTy, Ty, TyKind},
};
use itertools::{izip, Itertools};
use liquid_rust_core::ir::{self, Local};
use liquid_rust_fixpoint::KVid;
use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;

use super::ty::{Loc, Pred, TyS};

#[derive(Clone)]
pub struct TypeEnv<'tcx> {
    tcx: TyCtxt<'tcx>,
    bindings: FxHashMap<Loc, Binding>,
}

pub struct TypeEnvShape(Vec<(Loc, Ty)>);

#[derive(Clone)]
pub enum Binding {
    Strong(Ty),
    Weak { bound: Ty, ty: Ty },
}

impl Binding {
    pub fn ty(&self) -> Ty {
        match self {
            Binding::Strong(ty) => ty.clone(),
            Binding::Weak { ty, .. } => ty.clone(),
        }
    }

    pub fn assert_strong(&self) -> Ty {
        match self {
            Binding::Strong(ty) => ty.clone(),
            Binding::Weak { .. } => panic!("expected strong binding"),
        }
    }

    fn ty_mut(&mut self) -> &mut Ty {
        match self {
            Binding::Strong(ty) => ty,
            Binding::Weak { ty, .. } => ty,
        }
    }
}

impl<'tcx> TypeEnv<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> TypeEnv<'tcx> {
        TypeEnv {
            tcx,
            bindings: FxHashMap::default(),
        }
    }

    pub fn into_shape(self) -> TypeEnvShape {
        TypeEnvShape(
            self.bindings
                .into_iter()
                .map(|(loc, binding)| (loc, binding.ty()))
                .collect(),
        )
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.lookup_loc(Loc::Local(local)).unwrap()
    }

    pub fn lookup_loc(&self, loc: Loc) -> Option<Ty> {
        self.bindings.get(&loc).map(|k| k.ty())
    }

    pub fn lookup_place(&self, place: &ir::Place) -> Ty {
        let (_, ty) = self.walk_place(place);
        ty
    }

    pub fn insert_loc(&mut self, loc: Loc, ty: Ty) {
        self.bindings.insert(loc, Binding::Strong(ty));
    }

    pub fn update_loc(&mut self, cursor: &mut Cursor, loc: Loc, new_ty: Ty) {
        let binding = self.bindings.get_mut(&loc).unwrap();
        match binding {
            Binding::Strong(_) => *binding = Binding::Strong(new_ty),
            Binding::Weak { bound, .. } => {
                cursor.subtyping(new_ty, bound.clone());
            }
        }
    }

    pub fn get_loc(&self, place: &ir::Place) -> Loc {
        let (loc, _) = self.walk_place(place);
        loc
    }

    pub fn move_place(&mut self, place: &ir::Place) -> Ty {
        assert!(place.projection.is_empty());
        let loc = Loc::Local(place.local);
        let ty = self.lookup_loc(loc).unwrap();
        self.bindings
            .insert(loc, Binding::Strong(TyKind::Uninit.intern()));
        ty
    }

    pub fn write_place(&mut self, cursor: &mut Cursor, place: &ir::Place, new_ty: Ty) {
        let (loc, ty) = self.walk_place(place);

        match ty.kind() {
            TyKind::Uninit | TyKind::Refine(..) | TyKind::Param(_) | TyKind::StrgRef(_) => {
                // TODO: debug check new_ty has the same "shape" as ty
                self.update_loc(cursor, loc, new_ty);
            }
            TyKind::Ref(_) => {
                todo!("implement updates of references inside references")
            }
            TyKind::Exists(..) => unreachable!("unpacked existential: `{:?}`", ty),
        }
    }

    fn walk_place(&self, place: &ir::Place) -> (Loc, Ty) {
        let mut loc = Loc::Local(place.local);
        let mut ty = self.lookup_loc(loc).unwrap();
        for elem in &place.projection {
            match (elem, ty.kind()) {
                (ir::PlaceElem::Deref, TyKind::StrgRef(referee)) => {
                    loc = *referee;
                    ty = self.lookup_loc(loc).unwrap();
                }
                (ir::PlaceElem::Deref, TyKind::Ref(_)) => {
                    todo!()
                }
                _ => {
                    unreachable!("unexpected type: {:?}", ty);
                }
            }
        }
        (loc, ty)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Loc, &Binding)> + '_ {
        self.bindings.iter()
    }

    pub fn unpack(&mut self, cursor: &mut Cursor) {
        for loc in self.bindings.keys().copied().collect_vec() {
            let binding = self.bindings.get_mut(&loc).unwrap();
            match binding.ty().kind() {
                TyKind::Exists(..) => {
                    *binding.ty_mut() = cursor.unpack(binding.ty());
                }
                TyKind::Ref(ty) => {
                    let fresh = Loc::Abstract(cursor.fresh_name());
                    *binding.ty_mut() = TyKind::StrgRef(fresh).intern();
                    self.bindings.insert(
                        fresh,
                        Binding::Weak {
                            bound: ty.clone(),
                            ty: cursor.unpack(ty.clone()),
                        },
                    );
                }
                _ => {}
            }
        }
    }

    pub fn transform_into(&mut self, cursor: &mut Cursor, other: &TypeEnv) {
        self.weakening(other);

        let levels = self.levels();

        for (loc, _) in levels.into_iter().sorted_by_key(|(_, level)| *level).rev() {
            let ty1 = self.bindings[&loc].assert_strong();
            let ty2 = other.bindings[&loc].assert_strong();
            match (ty1.kind(), ty2.kind()) {
                (TyKind::StrgRef(loc), TyKind::Ref(bound)) => {
                    self.ref_weak(cursor, *loc, bound.clone());
                }
                _ => {
                    cursor.subtyping(ty1, ty2.clone());
                }
            };
            self.insert_loc(loc, ty2.clone());
        }
    }

    pub fn infer_bb_env(&self, cursor: &mut Cursor, shape: TypeEnvShape) -> TypeEnv<'tcx> {
        // Collect all kvars and generate fresh ones in the right scope.
        let mut kvars = FxHashMap::default();
        for (_, ty) in &shape {
            ty.walk(&mut |ty| {
                if let TyKind::Exists(bty, Pred::KVar(kvid, _)) = ty.kind() {
                    kvars
                        .entry(*kvid)
                        .or_insert_with(|| cursor.fresh_kvar_at_last_scope(bty.sort()));
                }
            })
        }

        let mut locs = FxHashMap::default();
        for (loc, ty1) in &shape {
            let ty2 = self.lookup_loc(*loc);
            if let (TyKind::StrgRef(loc1), Some(TyKind::StrgRef(loc2))) =
                (ty1.kind(), ty2.as_ref().map(|ty| ty.kind()))
            {
                locs.insert(*loc1, *loc2);
            }
        }

        let mut env = TypeEnv::new(self.tcx);
        for (loc, ty1) in shape {
            let loc = locs.get(&loc).copied().unwrap_or(loc);
            let ty2 = self.bindings[&loc].ty();

            let ty = match (ty1.kind(), ty2.kind()) {
                (TyKind::Refine(_, _), TyKind::Refine(_, _))
                | (TyKind::StrgRef(_), TyKind::StrgRef(_))
                | (_, TyKind::Uninit) => ty2,
                _ => replace_kvars(&ty1, &kvars),
            };
            env.insert_loc(loc, ty);
        }
        env
    }

    fn levels(&self) -> FxHashMap<Loc, u32> {
        fn dfs(
            env: &TypeEnv,
            loc: Loc,
            binding: &Binding,
            levels: &mut FxHashMap<Loc, u32>,
        ) -> u32 {
            if levels.contains_key(&loc) {
                return levels[&loc];
            }
            let level = match binding.ty().kind() {
                TyKind::StrgRef(referee) => dfs(env, *referee, &env.bindings[referee], levels) + 1,
                _ => 0,
            };
            levels.insert(loc, level);
            level
        }
        let mut levels = FxHashMap::default();
        for (loc, binding) in &self.bindings {
            dfs(self, *loc, binding, &mut levels);
        }
        levels
    }

    pub fn join_with(&mut self, other: &TypeEnv, cursor: &mut Cursor) {
        self.weakening(other);

        let mut levels = self.levels();
        let levels_other = other.levels();
        for (loc, level) in &mut levels {
            *level = (*level).max(levels_other[loc]);
        }

        for (loc, _) in levels.into_iter().sorted_by_key(|(_, level)| *level) {
            let binding1 = self.bindings[&loc].clone();
            let binding2 = other.bindings[&loc].clone();
            if let (Binding::Strong(ty1), Binding::Strong(ty2)) = (binding1, binding2) {
                let ty = self.strg_ty_join(cursor, ty1, ty2);
                self.bindings.insert(loc, Binding::Strong(ty));
            }
        }
    }

    fn weakening(&mut self, other: &TypeEnv) {
        self.bindings.retain(|loc, binding| {
            if other.bindings.contains_key(loc) {
                if other.lookup_loc(*loc).unwrap().is_uninit() {
                    *binding = Binding::Strong(TyKind::Uninit.intern());
                }
                true
            } else {
                false
            }
        });
    }

    fn strg_ty_join(&mut self, cursor: &mut Cursor, ty1: Ty, ty2: Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (_, _) if ty1 == ty2 => ty1,
            (TyKind::Uninit, _) | (_, TyKind::Uninit) => TyKind::Uninit.intern(),
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) if e1 == e2 => {
                TyKind::Refine(self.bty_join(cursor, bty1, bty2), e1.clone()).intern()
            }
            (
                TyKind::Refine(bty1, ..) | TyKind::Exists(bty1, ..),
                TyKind::Refine(bty2, ..) | TyKind::Exists(bty2, ..),
            ) => {
                let bty = self.bty_join(cursor, bty1, bty2);
                let kvar = cursor.fresh_kvar(bty.sort());
                TyKind::Exists(bty, kvar).intern()
            }
            (TyKind::StrgRef(loc1), TyKind::StrgRef(loc2)) => {
                let ty = self.ref_weak_join(cursor, *loc1, *loc2);
                TyKind::Ref(ty).intern()
            }
            (TyKind::Ref(ty), TyKind::StrgRef(loc)) | (TyKind::StrgRef(loc), TyKind::Ref(ty)) => {
                self.ref_weak(cursor, *loc, ty.clone());
                ty.clone()
            }
            _ => todo!("{:?} {:?}", ty1, ty2),
        }
    }

    fn ref_weak(&mut self, cursor: &mut Cursor, loc: Loc, bound: Ty) {
        let ty = self.bindings[&loc].assert_strong();
        match (ty.kind(), bound.kind()) {
            (_, TyKind::Exists(..)) => {
                cursor.subtyping(ty, bound.clone());
                self.bindings.insert(loc, Binding::Strong(bound));
            }
            (TyKind::StrgRef(loc2), TyKind::Ref(bound2)) => {
                self.ref_weak(cursor, *loc2, bound2.clone());
                self.bindings.insert(loc, Binding::Strong(bound));
            }
            (TyKind::Ref(bound2), TyKind::Ref(bound3)) => {
                assert!(bound2 == bound3);
            }
            _ => todo!(),
        }
    }

    fn ref_weak_join(&mut self, cursor: &mut Cursor, loc1: Loc, loc2: Loc) -> Ty {
        let ty1 = self.bindings[&loc1].assert_strong();
        let ty2 = self.bindings[&loc2].assert_strong();
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(..) | TyKind::Exists(..), TyKind::Refine(..) | TyKind::Exists(..)) => {
                let ty_join = self.strg_ty_join(cursor, ty1.clone(), ty2.clone());
                self.bindings.insert(loc1, Binding::Strong(ty_join.clone()));
                self.bindings.insert(loc2, Binding::Strong(ty_join.clone()));
                ty_join
            }
            (TyKind::StrgRef(loc1_), TyKind::StrgRef(loc2_)) => {
                let ty_join = TyKind::Ref(self.ref_weak_join(cursor, *loc1_, *loc2_)).intern();
                self.bindings.insert(loc1, Binding::Strong(ty_join.clone()));
                self.bindings.insert(loc1, Binding::Strong(ty_join.clone()));
                ty_join
            }
            (TyKind::StrgRef(loc), TyKind::Ref(ty)) | (TyKind::Ref(ty), TyKind::StrgRef(loc)) => {
                self.ref_weak(cursor, *loc, ty.clone());
                self.bindings.insert(loc1, Binding::Strong(ty.clone()));
                ty.clone()
            }
            _ => {
                todo!()
            }
        }
    }

    fn bty_join(&mut self, cursor: &mut Cursor, bty1: &BaseTy, bty2: &BaseTy) -> BaseTy {
        match (bty1, bty2) {
            (BaseTy::Bool, BaseTy::Bool) => BaseTy::Bool,
            (BaseTy::Int(int_ty1), BaseTy::Int(int_ty2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
                BaseTy::Int(*int_ty1)
            }
            (BaseTy::Uint(uint_ty1), BaseTy::Uint(uint_ty2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
                BaseTy::Uint(*uint_ty1)
            }
            (BaseTy::Adt(did1, substs1), BaseTy::Adt(did2, substs2)) => {
                debug_assert_eq!(did1, did2);
                let variances = self.tcx.variances_of(*did1);
                let substs =
                    izip!(variances, substs1.iter(), substs2.iter()).map(|(variance, ty1, ty2)| {
                        assert!(matches!(variance, rustc_middle::ty::Variance::Covariant));
                        self.strg_ty_join(cursor, ty1.clone(), ty2.clone())
                    });
                BaseTy::adt(*did1, substs)
            }
            _ => todo!("{:?} {:?}", bty1, bty2),
        }
    }
}

impl<'a> IntoIterator for &'a TypeEnvShape {
    type Item = &'a (Loc, Ty);

    type IntoIter = std::slice::Iter<'a, (Loc, Ty)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl IntoIterator for TypeEnvShape {
    type Item = (Loc, Ty);

    type IntoIter = std::vec::IntoIter<(Loc, Ty)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

fn replace_kvars(ty: &TyS, kvars: &FxHashMap<KVid, Pred>) -> Ty {
    match ty.kind() {
        TyKind::Refine(bty, e) => TyKind::Refine(bty.clone(), e.clone()).intern(),
        TyKind::Exists(bty, Pred::KVar(kvid, _)) => {
            TyKind::Exists(replace_kvars_bty(bty, kvars), kvars[kvid].clone()).intern()
        }
        TyKind::Exists(bty, p) => TyKind::Exists(bty.clone(), p.clone()).intern(),
        TyKind::Uninit => TyKind::Uninit.intern(),
        TyKind::StrgRef(loc) => TyKind::StrgRef(*loc).intern(),
        TyKind::Ref(ty) => TyKind::Ref(replace_kvars(ty, kvars)).intern(),
        TyKind::Param(param_ty) => TyKind::Param(*param_ty).intern(),
    }
}

fn replace_kvars_bty(bty: &BaseTy, kvars: &FxHashMap<KVid, Pred>) -> BaseTy {
    match bty {
        BaseTy::Adt(did, substs) => {
            let substs = substs.iter().map(|ty| replace_kvars(ty, kvars));
            BaseTy::adt(*did, substs)
        }
        BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty.clone(),
    }
}

mod pretty {
    use super::*;
    use crate::pretty::*;
    use itertools::Itertools;
    use std::fmt;

    impl Pretty for TypeEnv<'_> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let bindings = self
                .iter()
                .filter(|(_, binding)| !binding.ty().is_uninit())
                .sorted_by(|(loc1, _), (loc2, _)| loc1.cmp(loc2))
                .collect_vec();

            w!("{{")?;
            for (i, (loc, binding)) in bindings.into_iter().enumerate() {
                if i > 0 {
                    w!(", ")?;
                }
                w!("{:?}: {:?}", loc, binding)?;
            }
            w!("}}")
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for TypeEnvShape {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let bindings = self
                .into_iter()
                .filter(|(_, ty)| !ty.is_uninit())
                .sorted_by(|(loc1, _), (loc2, _)| loc1.cmp(loc2))
                .collect_vec();

            w!("{{")?;
            for (i, (loc, binding)) in bindings.into_iter().enumerate() {
                if i > 0 {
                    w!(", ")?;
                }
                w!("{:?}: {:?}", loc, binding)?;
            }
            w!("}}")
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for Binding {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                Binding::Strong(ty) => w!("{:?}", ty),
                Binding::Weak { bound, ty } => {
                    w!("{:?} <: {:?}", ty, bound)
                }
            }
        }
    }

    impl_debug_with_default_cx!(TypeEnv<'_>, TypeEnvShape);
}
