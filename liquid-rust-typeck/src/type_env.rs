use crate::{
    pure_ctxt::Cursor,
    subst::Subst,
    ty::{BaseTy, ExprKind, Param, Ty, TyKind, Var},
};
use itertools::{izip, Itertools};
use liquid_rust_common::index::{Idx, IndexGen};
use liquid_rust_core::ir::{self, Local};
use liquid_rust_fixpoint::KVid;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;

use super::ty::{Loc, Name, Pred, Sort, TyS};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct TypeEnv {
    bindings: FxHashMap<Loc, Binding>,
    borrowed: FxHashSet<Loc>,
}

pub struct TypeEnvShape(Vec<(Loc, Ty)>, FxHashSet<Loc>);

pub struct BasicBlockEnv {
    pub params: Vec<Param>,
    pub bindings: Vec<(Loc, Ty)>,
    pub borrowed: FxHashSet<Loc>,
}

#[derive(Clone, PartialEq, Eq)]
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

    #[track_caller]
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

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv {
            bindings: FxHashMap::default(),
            borrowed: FxHashSet::default(),
        }
    }

    pub fn into_shape(self) -> TypeEnvShape {
        TypeEnvShape(
            self.bindings
                .into_iter()
                .map(|(loc, binding)| (loc, binding.ty()))
                .collect(),
            self.borrowed,
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

    pub fn has_loc(&self, loc: Loc) -> bool {
        self.bindings.contains_key(&loc)
    }

    pub fn insert_loc(&mut self, loc: Loc, ty: Ty) {
        self.bindings.insert(loc, Binding::Strong(ty));
    }

    pub fn update_loc(&mut self, tcx: TyCtxt, cursor: &mut Cursor, loc: Loc, new_ty: Ty) {
        let binding = self.bindings.get_mut(&loc).unwrap();
        match binding {
            Binding::Strong(_) => *binding = Binding::Strong(new_ty),
            Binding::Weak { bound, .. } => {
                cursor.subtyping(tcx, new_ty, bound.clone());
            }
        }
    }

    pub fn borrow(&mut self, place: &ir::Place) -> Ty {
        let (loc, _) = self.walk_place(place);
        self.borrowed.insert(loc);
        TyKind::StrgRef(loc).intern()
    }

    pub fn move_place(&mut self, place: &ir::Place) -> Ty {
        assert!(place.projection.is_empty());
        let loc = Loc::Local(place.local);
        let ty = self.lookup_loc(loc).unwrap();
        self.bindings
            .insert(loc, Binding::Strong(TyKind::Uninit.intern()));
        ty
    }

    pub fn write_place(&mut self, tcx: TyCtxt, cursor: &mut Cursor, place: &ir::Place, new_ty: Ty) {
        let (loc, ty) = self.walk_place(place);

        match ty.kind() {
            TyKind::Uninit | TyKind::Refine(..) | TyKind::Param(_) | TyKind::StrgRef(_) => {
                // TODO: debug check new_ty has the same "shape" as ty
                self.update_loc(tcx, cursor, loc, new_ty);
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

    pub fn unpack(&mut self, cursor: &mut Cursor, ty: Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(bty, p) => {
                let fresh =
                    cursor.push_binding(bty.sort(), |fresh| p.subst_bound_vars(Var::Free(fresh)));
                TyKind::Refine(bty.clone(), Var::Free(fresh).into()).intern()
            }
            TyKind::Ref(ty) => {
                let fresh = cursor.push_loc();
                let unpacked = self.unpack(cursor, ty.clone());
                self.bindings.insert(
                    fresh,
                    Binding::Weak {
                        bound: ty.clone(),
                        ty: unpacked,
                    },
                );
                TyKind::StrgRef(fresh).intern()
            }
            _ => ty,
        }
    }

    pub fn unpack_all(&mut self, cursor: &mut Cursor) {
        for loc in self.bindings.iter().map(|(loc, _)| *loc).collect_vec() {
            let ty = self.unpack(cursor, self.bindings[&loc].ty().clone());
            *self.bindings.get_mut(&loc).unwrap().ty_mut() = ty;
        }
    }

    pub fn transform_into(&mut self, tcx: TyCtxt, cursor: &mut Cursor, other: &TypeEnv) {
        let levels = self
            .levels()
            .into_iter()
            .sorted_by_key(|(_, level)| *level)
            .rev();

        for (loc, _) in levels {
            if !other.bindings.contains_key(&loc) {
                self.bindings.remove(&loc);
                continue;
            }
            let ty1 = self.bindings[&loc].assert_strong();
            let ty2 = other.bindings[&loc].assert_strong();
            match (ty1.kind(), ty2.kind()) {
                (TyKind::StrgRef(loc), TyKind::Ref(bound)) => {
                    self.ref_weak(tcx, cursor, *loc, bound.clone());
                }
                _ => {
                    cursor.subtyping(tcx, ty1, ty2.clone());
                }
            };
            self.insert_loc(loc, ty2.clone());
        }
        self.borrowed.extend(&other.borrowed);
        debug_assert_eq!(self, other);
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

    pub fn join(&mut self, tcx: TyCtxt, other: &mut TypeEnv) -> bool {
        let levels = self
            .levels()
            .into_iter()
            .sorted_by_key(|(_, level)| *level)
            .rev();

        let mut modified = false;
        for (loc, _) in levels {
            if !other.bindings.contains_key(&loc) {
                self.bindings.remove(&loc);
                modified = true;
                continue;
            }
            let ty1 = self.bindings[&loc].assert_strong();
            let ty2 = other.bindings[&loc].assert_strong();
            let ty = self.join_ty(tcx, other, ty1.clone(), ty2);
            modified |= ty1 != ty;
            self.bindings.insert(loc, Binding::Strong(ty));
        }
        let n = self.borrowed.len();
        self.borrowed.extend(&other.borrowed);
        modified |= n != self.borrowed.len();

        modified
    }

    fn join_ty(&mut self, tcx: TyCtxt, other: &mut TypeEnv, mut ty1: Ty, mut ty2: Ty) -> Ty {
        if ty1 == ty2 {
            return ty1;
        }

        if let TyKind::StrgRef(loc) = ty1.kind() {
            ty1 = self.weaken_ref_join(*loc);
        }

        if let TyKind::StrgRef(loc) = ty2.kind() {
            ty2 = other.weaken_ref_join(*loc);
        }

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Uninit, _) | (_, TyKind::Uninit) => TyKind::Uninit.intern(),
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) if e1 == e2 => {
                TyKind::Refine(self.join_bty(tcx, other, bty1, bty2), e1.clone()).intern()
            }
            (
                TyKind::Refine(bty1, ..) | TyKind::Exists(bty1, Pred::Expr(..)),
                TyKind::Refine(bty2, ..) | TyKind::Exists(bty2, ..),
            ) => {
                let bty = self.join_bty(tcx, other, bty1, bty2);
                TyKind::Exists(bty, Pred::kvar(KVid::new(0), [])).intern()
            }
            (
                TyKind::Exists(bty1, p @ Pred::KVar(..)),
                TyKind::Refine(bty2, ..) | TyKind::Exists(bty2, ..),
            ) => {
                let bty = self.join_bty(tcx, other, bty1, bty2);
                TyKind::Exists(bty, p.clone()).intern()
            }
            (TyKind::Ref(ty1), TyKind::Ref(ty2)) => {
                TyKind::Ref(self.join_ty(tcx, other, ty1.clone(), ty2.clone())).intern()
            }
            _ => todo!("{:?} {:?}", ty1, ty2),
        }
    }

    fn join_bty(
        &mut self,
        tcx: TyCtxt,
        other: &mut TypeEnv,
        bty1: &BaseTy,
        bty2: &BaseTy,
    ) -> BaseTy {
        match (bty1, bty2) {
            (BaseTy::Adt(did1, substs1), BaseTy::Adt(did2, substs2)) => {
                debug_assert_eq!(did1, did2);
                let variances = tcx.variances_of(*did1);
                let substs =
                    izip!(variances, substs1.iter(), substs2.iter()).map(|(variance, ty1, ty2)| {
                        assert!(matches!(variance, rustc_middle::ty::Variance::Covariant));
                        self.join_ty(tcx, other, ty1.clone(), ty2.clone())
                    });
                BaseTy::adt(*did1, substs)
            }
            _ => {
                debug_assert_eq!(bty1, bty2);
                bty1.clone()
            }
        }
    }

    fn weaken_ref_join(&mut self, loc: Loc) -> Ty {
        match self.bindings[&loc].clone() {
            Binding::Strong(ty) => {
                let ty = self.weaken_ty(ty);
                self.bindings.insert(loc, Binding::Strong(ty.clone()));
                TyKind::Ref(ty).intern()
            }
            Binding::Weak { bound, .. } => TyKind::Ref(bound).intern(),
        }
    }

    fn weaken_ty(&mut self, ty: Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(.., Pred::KVar(..)) | TyKind::Param(_) => ty,
            TyKind::Exists(bty, Pred::Expr(..)) | TyKind::Refine(bty, _) => {
                let bty = self.weaken_bty(bty);
                TyKind::Exists(bty, Pred::kvar(KVid::new(0), [])).intern()
            }
            TyKind::StrgRef(loc) => {
                let ty = self.bindings[loc].assert_strong();
                let ty = self.weaken_ty(ty);
                self.bindings.insert(*loc, Binding::Strong(ty.clone()));
                TyKind::Ref(ty).intern()
            }
            TyKind::Ref(_) | TyKind::Uninit => {
                unreachable!()
            }
        }
    }

    fn weaken_bty(&mut self, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(did, substs) => {
                let substs = substs.iter().map(|ty| self.weaken_ty(ty.clone()));
                BaseTy::adt(*did, substs)
            }
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty.clone(),
        }
    }

    fn ref_weak(&mut self, tcx: TyCtxt, cursor: &mut Cursor, loc: Loc, bound: Ty) {
        let ty = self.bindings[&loc].ty();
        match (ty.kind(), bound.kind()) {
            (_, TyKind::Exists(..)) => {
                cursor.subtyping(tcx, ty, bound.clone());
                self.bindings.insert(loc, Binding::Strong(bound));
            }
            (TyKind::StrgRef(loc2), TyKind::Ref(bound2)) => {
                self.ref_weak(tcx, cursor, *loc2, bound2.clone());
                self.bindings.insert(loc, Binding::Strong(bound));
            }
            (TyKind::Ref(bound2), TyKind::Ref(bound3)) => {
                assert!(bound2 == bound3);
            }
            _ => todo!(),
        }
    }
}

impl TypeEnvShape {
    pub fn into_bb_env(
        self,
        name_gen: &IndexGen<Name>,
        fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
        env: &TypeEnv,
    ) -> BasicBlockEnv {
        let mut subst = FxHashMap::default();
        for (loc, ty1) in &self {
            let ty2 = env.lookup_loc(*loc);
            if let (TyKind::StrgRef(loc1), Some(TyKind::StrgRef(loc2))) =
                (ty1.kind(), ty2.as_ref().map(|ty| ty.kind()))
            {
                subst.insert(*loc1, *loc2);
            }
        }

        let mut bindings = vec![];
        for (loc, ty1) in self.0 {
            let loc = subst.get(&loc).copied().unwrap_or(loc);
            let ty2 = env.bindings[&loc].ty();

            let ty = match (ty1.kind(), ty2.kind()) {
                (TyKind::Refine(_, _), TyKind::Refine(_, _))
                | (TyKind::StrgRef(_), TyKind::StrgRef(_))
                | (_, TyKind::Uninit) => ty2,
                _ => replace_kvars(&ty1, fresh_kvar),
            };
            bindings.push((loc, ty));
        }
        let mut bb_env = BasicBlockEnv {
            params: vec![],
            bindings,
            borrowed: self.1,
        };
        bb_env.generalize(name_gen, fresh_kvar);
        bb_env
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

impl BasicBlockEnv {
    fn generalize(
        &mut self,
        name_gen: &IndexGen<Name>,
        fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
    ) {
        // HACK: As a simple heuristic we only generalize kvars with only one ocurrence and in a
        // "top-level" type.

        // let mut count: FxHashMap<KVid, i32> = FxHashMap::default();
        // for (_, ty) in &self.bindings {
        //     ty.walk(&mut |ty| {
        //         if let TyKind::Exists(_, Pred::KVar(kvid, _)) = ty.kind() {
        //             *count.entry(*kvid).or_default() += 1;
        //         }
        //     })
        // }

        for (loc, ty) in &mut self.bindings {
            match ty.kind() {
                TyKind::Exists(bty, Pred::KVar(..)) if !self.borrowed.contains(loc) => {
                    let fresh = name_gen.fresh();
                    let param = Param {
                        name: fresh,
                        sort: bty.sort(),
                        pred: fresh_kvar(fresh.into(), bty.sort(), &self.params),
                    };
                    self.params.push(param);
                    let e = ExprKind::Var(fresh.into()).intern();
                    *ty = TyKind::Refine(bty.clone(), e).intern();
                }
                _ => {}
            };
        }
    }

    pub fn enter(&self, cursor: &mut Cursor) -> TypeEnv {
        let mut subst = Subst::empty();
        for param in &self.params {
            cursor.push_binding(param.sort, |fresh| {
                subst.insert_expr(Var::Free(param.name), Var::Free(fresh));
                subst.subst_pred(&param.pred)
            });
        }

        TypeEnv {
            bindings: self
                .bindings
                .iter()
                .map(|(loc, ty)| (*loc, Binding::Strong(subst.subst_ty(ty))))
                .collect(),
            borrowed: self.borrowed.clone(),
        }
    }

    pub fn subst(&self, subst: &Subst) -> TypeEnv {
        TypeEnv {
            bindings: self
                .bindings
                .iter()
                .map(|(loc, ty)| (*loc, Binding::Strong(subst.subst_ty(ty))))
                .collect(),
            borrowed: self.borrowed.clone(),
        }
    }
}

fn replace_kvars(ty: &TyS, fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred) -> Ty {
    match ty.kind() {
        TyKind::Refine(bty, e) => TyKind::Refine(bty.clone(), e.clone()).intern(),
        TyKind::Exists(bty, Pred::KVar(_, _)) => {
            let p = fresh_kvar(Var::Bound, bty.sort(), &[]);
            TyKind::Exists(replace_kvars_bty(bty, fresh_kvar), p).intern()
        }
        TyKind::Exists(bty, p) => TyKind::Exists(bty.clone(), p.clone()).intern(),
        TyKind::Uninit => TyKind::Uninit.intern(),
        TyKind::StrgRef(loc) => TyKind::StrgRef(*loc).intern(),
        TyKind::Ref(ty) => TyKind::Ref(replace_kvars(ty, fresh_kvar)).intern(),
        TyKind::Param(param_ty) => TyKind::Param(*param_ty).intern(),
    }
}

fn replace_kvars_bty(
    bty: &BaseTy,
    fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
) -> BaseTy {
    match bty {
        BaseTy::Adt(did, substs) => {
            let substs = substs.iter().map(|ty| replace_kvars(ty, fresh_kvar));
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

    impl Pretty for TypeEnv {
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

    impl Pretty for BasicBlockEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("∀ ")?;
            for (i, param) in self.params.iter().enumerate() {
                if i > 0 {
                    w!(", ")?;
                }
                w!("{:?}: {:?}{{{:?}}}", ^param.name, ^param.sort, &param.pred)?;
            }
            w!("\n")?;

            let bindings = self
                .bindings
                .iter()
                .filter(|(_, ty)| !ty.is_uninit())
                .sorted_by(|(loc1, _), (loc2, _)| loc1.cmp(loc2))
                .collect_vec();
            w!("  {{")?;
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

    impl_debug_with_default_cx!(TypeEnv, TypeEnvShape, BasicBlockEnv);
}
