use crate::{
    constraint_gen::ConstraintGen,
    global_env::GlobalEnv,
    pure_ctxt::{PureCtxt, Scope},
    subst::Subst,
    ty::{BaseTy, Expr, ExprKind, Param, ParamTy, Ty, TyKind, Var},
};
use itertools::{izip, Itertools};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ir::{self, Local};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;

use super::ty::{Loc, Name, Pred, Sort, TyS};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct TypeEnv {
    bindings: FxHashMap<Loc, Binding>,
    borrowed: FxHashSet<Loc>,
}

pub struct TypeEnvInfer {
    params: FxHashMap<Name, Sort>,
    name_gen: IndexGen<Name>,
    env: TypeEnv,
}

pub struct BasicBlockEnv {
    pub params: Vec<Param>,
    pub constrs: Vec<Pred>,
    pub env: TypeEnv,
}

#[derive(Clone, PartialEq, Eq)]
pub enum Binding {
    Strong(Ty),
    Weak { bound: Ty, ty: Ty },
}

impl Binding {
    pub fn ty(&self) -> Ty {
        match self {
            Binding::Strong(ty) | Binding::Weak { ty, .. } => ty.clone(),
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
        TypeEnv { bindings: FxHashMap::default(), borrowed: FxHashSet::default() }
    }

    pub fn into_infer(self, genv: &GlobalEnv, scope: &Scope) -> TypeEnvInfer {
        TypeEnvInfer::new(genv, scope, self)
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.lookup_loc(Loc::Local(local))
    }

    pub fn lookup_loc(&self, loc: Loc) -> Ty {
        self.bindings.get(&loc).unwrap().ty()
    }

    pub fn lookup_place(&self, place: &ir::Place) -> Ty {
        let ty = self.lookup_loc(Loc::Local(place.local()));
        match (place, ty.kind()) {
            (ir::Place::Local(_), _) => ty,
            (ir::Place::Deref(_), TyKind::ShrRef(ty) | TyKind::WeakRef(ty)) => ty.clone(),
            (ir::Place::Deref(_), TyKind::StrgRef(loc)) => self.lookup_loc(*loc),
            _ => unreachable!(""),
        }
    }

    pub fn insert_loc(&mut self, loc: Loc, ty: Ty) {
        self.bindings.insert(loc, Binding::Strong(ty));
    }

    pub fn update_loc(&mut self, gen: &mut ConstraintGen, loc: Loc, new_ty: Ty) {
        let binding = self.bindings.get_mut(&loc).unwrap();
        match binding {
            Binding::Strong(_) => *binding = Binding::Strong(new_ty),
            Binding::Weak { bound, .. } => {
                gen.subtyping(new_ty, bound.clone());
            }
        }
    }

    pub fn borrow_mut(&mut self, place: &ir::Place) -> Ty {
        let loc = Loc::Local(place.local());
        let ty = self.lookup_loc(loc);
        let loc = match (place, ty.kind()) {
            (ir::Place::Local(_), _) => loc,
            (ir::Place::Deref(_), TyKind::StrgRef(loc)) => *loc,
            (ir::Place::Deref(_), TyKind::WeakRef(_)) => {
                unreachable!("mutable borrow with unpacked weak ref")
            }
            (ir::Place::Deref(_), TyKind::ShrRef(_)) => {
                unreachable!("cannot borrow mutably from a shared ref")
            }
            _ => unreachable!("unxepected place `{place:?}`"),
        };
        self.borrowed.insert(loc);
        TyKind::StrgRef(loc).intern()
    }

    pub fn borrow_shr(&mut self, place: &ir::Place) -> Ty {
        let loc = Loc::Local(place.local());
        let ty = self.lookup_loc(loc);
        match (place, ty.kind()) {
            (ir::Place::Local(_), _) => {
                self.borrowed.insert(loc);
                TyKind::ShrRef(ty).intern()
            }
            (ir::Place::Deref(_), TyKind::StrgRef(loc)) => {
                self.borrowed.insert(*loc);
                let ty = self.lookup_loc(*loc);
                TyKind::ShrRef(ty).intern()
            }
            (ir::Place::Deref(_), TyKind::ShrRef(ty)) => TyKind::ShrRef(ty.clone()).intern(),
            (ir::Place::Deref(_), TyKind::WeakRef(_)) => {
                unreachable!("shared borrow with unpacked weak ref")
            }
            _ => unreachable!("unxepected place `{place:?}`"),
        }
    }

    pub fn move_place(&mut self, place: &ir::Place) -> Ty {
        match place {
            ir::Place::Local(local) => {
                let loc = Loc::Local(*local);
                let ty = self.lookup_loc(loc);
                self.bindings
                    .insert(loc, Binding::Strong(TyKind::Uninit.intern()));
                ty
            }
            ir::Place::Deref(_) => unreachable!("cannot move out from a dereference"),
        }
    }

    pub fn write_place(&mut self, gen: &mut ConstraintGen, place: &ir::Place, new_ty: Ty) {
        let loc = Loc::Local(place.local());
        let ty = self.lookup_loc(loc);
        let loc = match (place, ty.kind()) {
            (ir::Place::Local(_), _) => loc,
            (ir::Place::Deref(_), TyKind::StrgRef(loc)) => *loc,
            (ir::Place::Deref(_), TyKind::WeakRef(_)) => {
                unreachable!("update through unpacked weak ref")
            }
            (ir::Place::Deref(_), TyKind::ShrRef(_)) => {
                unreachable!("cannot update through a shared ref")
            }
            _ => unreachable!("unexpected place `{place:?}`"),
        };
        self.update_loc(gen, loc, new_ty);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Loc, &Binding)> + '_ {
        self.bindings.iter()
    }

    pub fn unpack(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(bty, p) => {
                let fresh =
                    pcx.push_binding(genv.sort(bty), |fresh| p.subst_bound_vars(Var::Free(fresh)));
                TyKind::Refine(bty.clone(), Var::Free(fresh).into()).intern()
            }
            TyKind::WeakRef(ty) => {
                let fresh = pcx.push_loc();
                let unpacked = self.unpack(genv, pcx, ty);
                self.bindings
                    .insert(fresh, Binding::Weak { bound: ty.clone(), ty: unpacked });
                TyKind::StrgRef(fresh).intern()
            }
            TyKind::ShrRef(ty) => {
                let ty = self.unpack(genv, pcx, ty);
                TyKind::ShrRef(ty).intern()
            }
            _ => ty.clone(),
        }
    }

    pub fn unpack_all(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt) {
        for loc in self.bindings.iter().map(|(loc, _)| *loc).collect_vec() {
            let ty = self.unpack(genv, pcx, &self.bindings[&loc].ty());
            *self.bindings.get_mut(&loc).unwrap().ty_mut() = ty;
        }
    }

    pub fn pack_refs(&mut self, scope: &Scope) {
        let references = self
            .bindings
            .iter()
            .filter_map(|(loc, ty)| {
                match ty.ty().kind() {
                    TyKind::StrgRef(ref_loc @ Loc::Abstract(name)) if !scope.contains(*name) => {
                        Some((*ref_loc, *loc))
                    }
                    _ => None,
                }
            })
            .into_group_map();

        for (ref_loc, locs) in references {
            let bound = if let Binding::Weak { bound, .. } = &self.bindings[&ref_loc] {
                bound.clone()
            } else {
                unreachable!("non-weak out-of-scope location")
            };
            for loc in locs {
                let ty = TyKind::WeakRef(bound.clone()).intern();
                *self.bindings.get_mut(&loc).unwrap().ty_mut() = ty;
            }
            self.bindings.remove(&ref_loc);
        }
    }

    pub fn transform_into(&mut self, gen: &mut ConstraintGen, other: &TypeEnv) {
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
            let (ty1, ty2) = match (self.bindings[&loc].clone(), other.bindings[&loc].clone()) {
                (Binding::Strong(ty1), Binding::Strong(ty2)) => (ty1, ty2),
                (
                    Binding::Weak { bound: bound1, ty: ty1 },
                    Binding::Weak { bound: bound2, ty: ty2 },
                ) => {
                    assert_eq!(bound1, bound2);
                    (ty1, ty2)
                }
                (binding1, binding2) => todo!("{loc:?}: `{binding1:?}` `{binding2:?}`"),
            };
            match (ty1.kind(), ty2.kind()) {
                (TyKind::StrgRef(loc), TyKind::WeakRef(bound)) => {
                    self.weaken_ref(gen, *loc, bound.clone());
                }
                _ => {
                    gen.subtyping(ty1, ty2.clone());
                }
            };
            *self.bindings.get_mut(&loc).unwrap().ty_mut() = ty2;
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

    fn weaken_ref(&mut self, gen: &mut ConstraintGen, loc: Loc, bound: Ty) {
        let ty = match &self.bindings[&loc] {
            Binding::Weak { bound: bound2, ty } => {
                gen.subtyping(bound.clone(), bound2.clone());
                ty.clone()
            }
            Binding::Strong(ty) => ty.clone(),
        };
        match (ty.kind(), bound.kind()) {
            (_, TyKind::Exists(..)) => {
                gen.subtyping(ty, bound.clone());
                *self.bindings.get_mut(&loc).unwrap().ty_mut() = bound;
            }
            _ => todo!(),
        }
    }
}

#[derive(Debug)]
enum JoinKind {
    Packed(BaseTy, Expr, Name),
    Refine(BaseTy, Expr),
    Exists(BaseTy, Pred),
    Uninit,
    StrgRef(Loc),
    WeakRef(Ty),
    ShrRef(Ty),
    Param(ParamTy),
}

impl TypeEnvInfer {
    pub fn enter(&self, pcx: &mut PureCtxt) -> TypeEnv {
        let mut subst = Subst::empty();
        for (name, sort) in self.params.iter() {
            let fresh = pcx.push_binding(sort.clone(), |_| Pred::tt());
            subst.insert_param(&Param { name: *name, sort: sort.clone() }, fresh);
        }
        TypeEnv {
            bindings: self
                .env
                .bindings
                .iter()
                .map(|(loc, binding)| (*loc, subst_binding(binding, &subst)))
                .collect(),
            borrowed: self.env.borrowed.clone(),
        }
    }

    fn join_kind(&self, ty: &Ty) -> JoinKind {
        match ty.kind() {
            TyKind::Refine(bty, e) => {
                match e.kind() {
                    ExprKind::Var(Var::Free(name)) if self.params.contains_key(name) => {
                        JoinKind::Packed(bty.clone(), e.clone(), *name)
                    }
                    _ => JoinKind::Refine(bty.clone(), e.clone()),
                }
            }
            TyKind::Exists(bty, p) => JoinKind::Exists(bty.clone(), p.clone()),
            TyKind::Uninit => JoinKind::Uninit,
            TyKind::StrgRef(loc) => JoinKind::StrgRef(*loc),
            TyKind::WeakRef(ty) => JoinKind::WeakRef(ty.clone()),
            TyKind::ShrRef(ty) => JoinKind::ShrRef(ty.clone()),
            TyKind::Param(param_ty) => JoinKind::Param(*param_ty),
        }
    }

    fn new(genv: &GlobalEnv, scope: &Scope, mut env: TypeEnv) -> TypeEnvInfer {
        let name_gen = scope.name_gen();
        let mut params = FxHashMap::default();
        for loc in env.bindings.keys().copied().collect_vec() {
            // TODO(nilehmann) Figure out what to do with bounds in weak locations.
            let ty = env.lookup_loc(loc);
            *env.bindings.get_mut(&loc).unwrap().ty_mut() =
                TypeEnvInfer::pack_ty(&mut params, genv, scope, &name_gen, &ty);
        }
        TypeEnvInfer { params, name_gen, env }
    }

    fn pack_ty(
        params: &mut FxHashMap<Name, Sort>,
        genv: &GlobalEnv,
        scope: &Scope,
        name_gen: &IndexGen<Name>,
        ty: &Ty,
    ) -> Ty {
        match ty.kind() {
            TyKind::Refine(bty, e) => {
                let has_free_vars = e.vars().into_iter().any(|name| !scope.contains(name));
                let e = if has_free_vars {
                    let fresh = name_gen.fresh();
                    params.insert(fresh, genv.sort(bty));
                    ExprKind::Var(fresh.into()).intern()
                } else {
                    e.clone()
                };
                let bty = TypeEnvInfer::pack_bty(params, genv, scope, name_gen, bty);
                TyKind::Refine(bty, e).intern()
            }
            // TODO(nilehmann) [`TyKind::Exists`] and [`TyKind::StrRef`] could also have free variables.
            // Figure out what to do in those cases. Currently [`TyKind::StrgRef`] is handled by pack_refs
            TyKind::Exists(_, _)
            | TyKind::Uninit
            | TyKind::StrgRef(_)
            | TyKind::WeakRef(_)
            | TyKind::ShrRef(_)
            | TyKind::Param(_) => ty.clone(),
        }
    }

    fn pack_bty(
        params: &mut FxHashMap<Name, Sort>,
        genv: &GlobalEnv,
        scope: &Scope,
        name_gen: &IndexGen<Name>,
        bty: &BaseTy,
    ) -> BaseTy {
        match bty {
            BaseTy::Adt(did, substs) => {
                let substs = substs
                    .iter()
                    .map(|ty| Self::pack_ty(params, genv, scope, name_gen, ty));
                BaseTy::adt(*did, substs)
            }
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty.clone(),
        }
    }

    pub fn join(&mut self, genv: &GlobalEnv, mut other: TypeEnvInfer) -> bool {
        let levels = self
            .env
            .levels()
            .into_iter()
            .sorted_by_key(|(_, level)| *level)
            .rev();

        let mut modified = false;
        for (loc, _) in levels {
            let (ty1, ty2) =
                match (self.env.bindings[&loc].clone(), other.env.bindings[&loc].clone()) {
                    (Binding::Strong(ty1), Binding::Strong(ty2)) => (ty1, ty2),
                    (
                        Binding::Weak { bound: bound1, ty: ty1 },
                        Binding::Weak { bound: bound2, ty: ty2 },
                    ) => {
                        assert_eq!(bound1, bound2);
                        (ty1, ty2)
                    }
                    _ => todo!(),
                };
            let ty = self.join_ty(genv, &mut other, ty1.clone(), ty2);
            modified |= ty1 != ty;
            *self.env.bindings.get_mut(&loc).unwrap().ty_mut() = ty.clone();
        }
        let n = self.env.borrowed.len();
        self.env.borrowed.extend(&other.env.borrowed);
        modified |= n != self.env.borrowed.len();

        modified
    }

    fn join_ty(
        &mut self,
        genv: &GlobalEnv,
        other: &mut TypeEnvInfer,
        mut ty1: Ty,
        mut ty2: Ty,
    ) -> Ty {
        use JoinKind::*;

        if ty1 == ty2 {
            return ty1;
        }

        if let TyKind::StrgRef(loc) = ty1.kind() {
            ty1 = self.weaken_ref(*loc);
        }

        if let TyKind::StrgRef(loc) = ty2.kind() {
            ty2 = other.weaken_ref(*loc);
        }

        match (self.join_kind(&ty1), other.join_kind(&ty2)) {
            (Uninit, _) | (_, Uninit) => TyKind::Uninit.intern(),
            (Refine(bty1, e1), Refine(bty2, e2)) if e1 == e2 => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                TyKind::Refine(bty, e1).intern()
            }
            (Packed(bty1, _, name1), Exists(bty2, _)) => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                self.params.remove(&name1);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            (Refine(bty1, _), Packed(bty2, _, _) | Refine(bty2, _)) => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                let fresh = self.name_gen.fresh();
                let sort = genv.sort(&bty);
                self.params.insert(fresh, sort);
                let e = ExprKind::Var(fresh.into()).intern();
                TyKind::Refine(bty, e).intern()
            }
            (
                Refine(bty1, _) | Exists(bty1, _),
                Exists(bty2, _) | Refine(bty2, _) | Packed(bty2, ..),
            ) => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            (Packed(bty1, e1, _), Refine(bty2, _) | Packed(bty2, ..)) => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                TyKind::Refine(bty, e1).intern()
            }
            (WeakRef(ty1), WeakRef(ty2)) => {
                TyKind::WeakRef(self.join_ty(genv, other, ty1.clone(), ty2.clone())).intern()
            }
            (ShrRef(ty1), ShrRef(ty2)) => {
                TyKind::ShrRef(self.join_ty(genv, other, ty1.clone(), ty2.clone())).intern()
            }
            (k1, k2) => todo!("`{k1:?}` -- `{k2:?}"),
        }
    }

    fn join_bty(
        &mut self,
        genv: &GlobalEnv,
        other: &mut TypeEnvInfer,
        bty1: &BaseTy,
        bty2: &BaseTy,
    ) -> BaseTy {
        if let (BaseTy::Adt(did1, substs1), BaseTy::Adt(did2, substs2)) = (bty1, bty2) {
            debug_assert_eq!(did1, did2);
            let variances = genv.variances_of(*did1);
            let substs =
                izip!(variances, substs1.iter(), substs2.iter()).map(|(variance, ty1, ty2)| {
                    assert!(matches!(variance, rustc_middle::ty::Variance::Covariant));
                    self.join_ty(genv, other, ty1.clone(), ty2.clone())
                });
            BaseTy::adt(*did1, substs)
        } else {
            debug_assert_eq!(bty1, bty2);
            bty1.clone()
        }
    }

    fn weaken_ref(&mut self, loc: Loc) -> Ty {
        match self.env.bindings[&loc].clone() {
            Binding::Strong(ty) => {
                let ty = self.weaken_ty(ty);
                self.env.bindings.insert(loc, Binding::Strong(ty.clone()));
                TyKind::WeakRef(ty).intern()
            }
            Binding::Weak { bound, .. } => TyKind::WeakRef(bound).intern(),
        }
    }

    fn weaken_ty(&mut self, ty: Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(.., Pred::KVar(..)) | TyKind::Param(_) => ty,
            TyKind::Exists(bty, Pred::Expr(..)) | TyKind::Refine(bty, _) => {
                let bty = self.weaken_bty(bty);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            TyKind::StrgRef(loc) => {
                let ty = self.env.bindings[loc].assert_strong();
                let ty = self.weaken_ty(ty);
                self.env.bindings.insert(*loc, Binding::Strong(ty.clone()));
                TyKind::WeakRef(ty).intern()
            }
            TyKind::ShrRef(_) | TyKind::WeakRef(_) => todo!(),
            TyKind::Uninit => {
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

    // pub fn into_bb_env(
    //     self,
    //     genv: &GlobalEnv,
    //     name_gen: &IndexGen<Name>,
    //     fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
    //     env: &TypeEnv,
    // ) -> BasicBlockEnv {
    //     let mut params = vec![];
    //     let mut constrs = vec![];
    //     let mut bindings = FxHashMap::default();
    //     for (loc, binding) in &self.env.bindings {
    //         if let Binding::Strong(ty) = binding {
    //             match ty.kind() {
    //                 TyKind::Exists(bty, Pred::KVar(..)) if !self.env.borrowed.contains(loc) => {
    //                     let fresh = name_gen.fresh();
    //                     let sort = genv.sort(bty);
    //                     constrs.push(fresh_kvar(fresh.into(), sort.clone(), &params));
    //                     let param = Param { name: fresh, sort };
    //                     params.push(param);
    //                     let e = ExprKind::Var(fresh.into()).intern();
    //                     let ty = TyKind::Refine(bty.clone(), e).intern();
    //                     bindings.insert(*loc, Binding::Strong(ty));
    //                 }
    //                 _ => {}
    //             };
    //         }
    //     }

    //     let fresh_kvar = &mut |var, sort| fresh_kvar(var, sort, &params);
    //     for (loc, binding1) in self.env.bindings {
    //         if bindings.contains_key(&loc) {
    //             continue;
    //         }
    //         let binding2 = &env.bindings[&loc];
    //         let binding = match (binding1, binding2) {
    //             (Binding::Strong(ty1), Binding::Strong(ty2)) => {
    //                 let ty = replace_kvars(genv, &ty1, fresh_kvar);
    //                 Binding::Strong(TypeEnvInfer::fix_ty(&ty, ty2))
    //             }
    //             (Binding::Weak { ty: ty1, .. }, Binding::Weak { ty: ty2, bound, .. }) => {
    //                 // HACK(nilehmann) The current inference algorithm cannot distinguish when a bound
    //                 // in a weak binding is preserved through a join point. To avoid generating extra kvars
    //                 // we keep the bound of the first environment jumping to the block. This could lose precision in
    //                 // cases where the bound does need to be strengthened.
    //                 let ty = replace_kvars(genv, &ty1, fresh_kvar);
    //                 Binding::Weak { ty: TypeEnvInfer::fix_ty(&ty, ty2), bound: bound.clone() }
    //             }
    //             _ => {
    //                 todo!()
    //             }
    //         };
    //         bindings.insert(loc, binding);
    //     }
    //     BasicBlockEnv { params, constrs, env: TypeEnv { bindings, borrowed: self.env.borrowed } }
    // }

    pub fn into_bb_env(
        self,
        genv: &GlobalEnv,
        fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
        env: &TypeEnv,
    ) -> BasicBlockEnv {
        // TODO(nilehmann) maybe sort by name here
        let mut params = vec![];
        let mut constrs = vec![];
        for (name, sort) in self.params {
            constrs.push(fresh_kvar(name.into(), sort.clone(), &params));
            params.push(Param { name, sort });
        }

        let mut bindings = FxHashMap::default();
        let fresh_kvar = &mut |var, sort| fresh_kvar(var, sort, &params);
        for (loc, binding1) in self.env.bindings {
            let binding2 = &env.bindings[&loc];
            let binding = match (binding1, binding2) {
                (Binding::Strong(ty1), Binding::Strong(_)) => {
                    Binding::Strong(replace_kvars(genv, &ty1, fresh_kvar))
                }
                (Binding::Weak { ty, .. }, Binding::Weak { bound, .. }) => {
                    // HACK(nilehmann) The current inference algorithm cannot distinguish when a bound
                    // in a weak binding is preserved through a join point. To avoid generating extra kvars
                    // we keep the bound of the first environment jumping to the block. This could lose precision in
                    // cases where the bound does need to be strengthened.
                    let ty = replace_kvars(genv, &ty, fresh_kvar);
                    Binding::Weak { ty, bound: bound.clone() }
                }
                _ => {
                    todo!()
                }
            };
            bindings.insert(loc, binding);
        }
        BasicBlockEnv { params, constrs, env: TypeEnv { bindings, borrowed: self.env.borrowed } }
    }
}

impl BasicBlockEnv {
    pub fn enter(&self, pcx: &mut PureCtxt) -> TypeEnv {
        let mut subst = Subst::empty();
        for (param, constr) in self.params.iter().zip(&self.constrs) {
            pcx.push_binding(param.sort.clone(), |fresh| {
                subst.insert_param(param, fresh);
                subst.subst_pred(constr)
            });
        }

        TypeEnv {
            bindings: self
                .env
                .bindings
                .iter()
                .map(|(loc, binding)| (*loc, subst_binding(binding, &subst)))
                .collect(),
            borrowed: self.env.borrowed.clone(),
        }
    }

    pub fn subst(&self, subst: &Subst) -> TypeEnv {
        TypeEnv {
            bindings: self
                .env
                .bindings
                .iter()
                .map(|(loc, binding)| (*loc, subst_binding(binding, subst)))
                .collect(),
            borrowed: self.env.borrowed.clone(),
        }
    }
}

fn subst_binding(binding: &Binding, subst: &Subst) -> Binding {
    match binding {
        Binding::Weak { bound, ty } => {
            Binding::Weak { bound: subst.subst_ty(bound), ty: subst.subst_ty(ty) }
        }
        Binding::Strong(ty) => Binding::Strong(subst.subst_ty(ty)),
    }
}

fn replace_kvars(genv: &GlobalEnv, ty: &TyS, fresh_kvar: &mut impl FnMut(Var, Sort) -> Pred) -> Ty {
    match ty.kind() {
        TyKind::Refine(bty, e) => {
            TyKind::Refine(replace_kvars_bty(genv, bty, fresh_kvar), e.clone()).intern()
        }
        TyKind::Exists(bty, Pred::KVar(_, _)) => {
            let p = fresh_kvar(Var::Bound, genv.sort(bty));
            TyKind::Exists(replace_kvars_bty(genv, bty, fresh_kvar), p).intern()
        }
        TyKind::Exists(bty, p) => TyKind::Exists(bty.clone(), p.clone()).intern(),
        TyKind::Uninit => TyKind::Uninit.intern(),
        TyKind::StrgRef(loc) => TyKind::StrgRef(*loc).intern(),
        TyKind::WeakRef(ty) => TyKind::WeakRef(replace_kvars(genv, ty, fresh_kvar)).intern(),
        TyKind::ShrRef(ty) => TyKind::ShrRef(replace_kvars(genv, ty, fresh_kvar)).intern(),
        TyKind::Param(param_ty) => TyKind::Param(*param_ty).intern(),
    }
}

fn replace_kvars_bty(
    genv: &GlobalEnv,
    bty: &BaseTy,
    fresh_kvar: &mut impl FnMut(Var, Sort) -> Pred,
) -> BaseTy {
    match bty {
        BaseTy::Adt(did, substs) => {
            let substs = substs.iter().map(|ty| replace_kvars(genv, ty, fresh_kvar));
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
            // PPrintCx::default(tcx).kvar_args(Visibility::Hide)
            PPrintCx::default(tcx).kvar_args(Visibility::Show)
        }
    }

    impl Pretty for TypeEnvInfer {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "∃ {}.\n  {:?}",
                ^self.params
                    .iter()
                    .format_with(", ", |(name, sort), f| f(&format_args_cx!("{:?}: {:?}", ^name, ^sort))),
                &self.env
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for BasicBlockEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "∃ {}.\n  {:?}",
                ^self.params
                    .iter()
                    .format_with(", ", |param, f| f(&format_args_cx!("{:?}: {:?}", ^param.name, ^param.sort))),
                &self.env
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            // PPrintCx::default(tcx).kvar_args(Visibility::Hide)
            PPrintCx::default(tcx).kvar_args(Visibility::Show)
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

    impl_debug_with_default_cx!(TypeEnv, TypeEnvInfer, BasicBlockEnv, Binding);
}
