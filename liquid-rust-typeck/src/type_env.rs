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
use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;

use super::ty::{Loc, Name, Pred, Sort, TyS};

#[derive(Clone, Default, PartialEq, Eq)]
pub struct TypeEnv {
    bindings: FxHashMap<Loc, Ty>,
    pledges: FxHashMap<Loc, Ty>,
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

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv { bindings: FxHashMap::default(), pledges: FxHashMap::default() }
    }

    pub fn into_infer(self, genv: &GlobalEnv, scope: &Scope) -> TypeEnvInfer {
        TypeEnvInfer::new(genv, scope, self)
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.lookup_loc(Loc::Local(local))
    }

    pub fn lookup_loc(&self, loc: Loc) -> Ty {
        self.bindings.get(&loc).unwrap().clone()
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
        self.bindings.insert(loc, ty);
    }

    pub fn update_loc(&mut self, gen: &mut ConstraintGen, loc: Loc, new_ty: Ty) {
        self.bindings.insert(loc, new_ty.clone());
        if let Some(pledge) = self.pledges.get(&loc) {
            gen.subtyping(new_ty, pledge.clone());
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
        TyKind::StrgRef(loc).intern()
    }

    pub fn borrow_shr(&mut self, place: &ir::Place) -> Ty {
        let loc = Loc::Local(place.local());
        let ty = self.lookup_loc(loc);
        match (place, ty.kind()) {
            (ir::Place::Local(_), _) => TyKind::ShrRef(ty).intern(),
            (ir::Place::Deref(_), TyKind::StrgRef(loc)) => {
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
                self.bindings.insert(loc, TyKind::Uninit.intern());
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

    pub fn iter(&self) -> impl Iterator<Item = (&Loc, &Ty)> + '_ {
        self.bindings.iter()
    }

    pub fn unpack_ty(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(bty, p) => {
                let fresh =
                    pcx.push_binding(genv.sort(bty), |fresh| p.subst_bound_vars(Var::Free(fresh)));
                TyKind::Refine(bty.clone(), Var::Free(fresh).into()).intern()
            }
            TyKind::WeakRef(pledge) => {
                let fresh = pcx.push_loc();
                let ty = self.unpack_ty(genv, pcx, pledge);
                self.bindings.insert(fresh, ty);
                self.pledges.insert(fresh, pledge.clone());
                TyKind::StrgRef(fresh).intern()
            }
            TyKind::ShrRef(ty) => {
                let ty = self.unpack_ty(genv, pcx, ty);
                TyKind::ShrRef(ty).intern()
            }
            _ => ty.clone(),
        }
    }

    pub fn unpack(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt) {
        for loc in self.bindings.iter().map(|(loc, _)| *loc).collect_vec() {
            let ty = self.bindings[&loc].clone();
            let ty = self.unpack_ty(genv, pcx, &ty);
            self.bindings.insert(loc, ty);
        }
    }

    pub fn pack_refs(&mut self, scope: &Scope) {
        let references = self
            .bindings
            .iter()
            .filter_map(|(loc, ty)| {
                match ty.kind() {
                    TyKind::StrgRef(ref_loc @ Loc::Abstract(name)) if !scope.contains(*name) => {
                        Some((*ref_loc, *loc))
                    }
                    _ => None,
                }
            })
            .into_group_map();

        for (ref_loc, locs) in references {
            let pledge = &self.pledges[&ref_loc];
            for loc in locs {
                self.bindings
                    .insert(loc, TyKind::WeakRef(pledge.clone()).intern());
            }
            self.pledges.remove(&ref_loc);
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
            let ty1 = self.bindings[&loc].clone();
            let ty2 = other.bindings[&loc].clone();
            match (ty1.kind(), ty2.kind()) {
                (TyKind::StrgRef(loc), TyKind::WeakRef(bound)) => {
                    self.weaken_ref(gen, *loc, bound.clone());
                }
                _ => {
                    gen.subtyping(ty1, ty2.clone());
                }
            };
            self.bindings.insert(loc, ty2);
        }
        // TODO(nilehmann) we should also join pledges
        assert_eq!(self, other);
    }

    fn levels(&self) -> FxHashMap<Loc, u32> {
        fn dfs(env: &TypeEnv, loc: Loc, binding: &Ty, levels: &mut FxHashMap<Loc, u32>) -> u32 {
            if levels.contains_key(&loc) {
                return levels[&loc];
            }
            let level = match binding.kind() {
                TyKind::StrgRef(referee) => dfs(env, *referee, &env.bindings[referee], levels) + 1,
                _ => 0,
            };
            levels.insert(loc, level);
            level
        }
        let mut levels = FxHashMap::default();
        for (loc, ty) in &self.bindings {
            dfs(self, *loc, ty, &mut levels);
        }
        levels
    }

    fn weaken_ref(&mut self, gen: &mut ConstraintGen, loc: Loc, bound: Ty) {
        let ty = &self.bindings[&loc];
        match (ty.kind(), bound.kind()) {
            (_, TyKind::Exists(..)) => {
                gen.subtyping(ty.clone(), bound.clone());
                self.bindings.insert(loc, bound);
            }
            _ => todo!(),
        }
    }
}

#[derive(Debug)]
enum TyKindJoin {
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
        // HACK(nilehmann) it is crucial that the order in this iteration is the same than
        // [`TypeEnvInfer::into_bb_env`] otherwise names will be out of order in the checking phase.
        for (name, sort) in self.params.iter() {
            let fresh = pcx.push_binding(sort.clone(), |_| Pred::tt());
            subst.insert_param(&Param { name: *name, sort: sort.clone() }, fresh);
        }
        TypeEnv {
            bindings: self
                .env
                .bindings
                .iter()
                .map(|(loc, ty)| (subst.subst_loc(*loc), subst.subst_ty(ty)))
                .collect(),
            pledges: self
                .env
                .pledges
                .iter()
                .map(|(loc, ty)| (subst.subst_loc(*loc), subst.subst_ty(ty)))
                .collect(),
        }
    }

    fn join_kind(&self, ty: &Ty) -> TyKindJoin {
        match ty.kind() {
            TyKind::Refine(bty, e) => {
                match e.kind() {
                    ExprKind::Var(Var::Free(name)) if self.params.contains_key(name) => {
                        TyKindJoin::Packed(bty.clone(), e.clone(), *name)
                    }
                    _ => TyKindJoin::Refine(bty.clone(), e.clone()),
                }
            }
            TyKind::Exists(bty, p) => TyKindJoin::Exists(bty.clone(), p.clone()),
            TyKind::Uninit => TyKindJoin::Uninit,
            TyKind::StrgRef(loc) => TyKindJoin::StrgRef(*loc),
            TyKind::WeakRef(ty) => TyKindJoin::WeakRef(ty.clone()),
            TyKind::ShrRef(ty) => TyKindJoin::ShrRef(ty.clone()),
            TyKind::Param(param_ty) => TyKindJoin::Param(*param_ty),
        }
    }

    fn new(genv: &GlobalEnv, scope: &Scope, mut env: TypeEnv) -> TypeEnvInfer {
        let name_gen = scope.name_gen();
        let mut params = FxHashMap::default();
        for loc in env.bindings.keys().copied().collect_vec() {
            // TODO(nilehmann) Figure out what to do with pledges
            let ty = env.lookup_loc(loc);
            env.bindings
                .insert(loc, TypeEnvInfer::pack_ty(&mut params, genv, scope, &name_gen, &ty));
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
            // TyKind::StrgRef(Loc::Abstract(loc)) if !scope.contains(*loc) => {

            // }
            // TODO(nilehmann) [`TyKind::Exists`] could also in theory contains free variables.
            TyKind::Exists(_, _)
            | TyKind::StrgRef(_)
            | TyKind::Uninit
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
            let ty1 = self.env.bindings[&loc].clone();
            let ty2 = other.env.bindings[&loc].clone();
            let ty = self.join_ty(genv, &mut other, ty1.clone(), ty2);
            modified |= ty1 != ty;
            self.env.bindings.insert(loc, ty);
        }
        // TODO(nilehmann) we also have to join pledges

        modified
    }

    fn join_ty(&mut self, genv: &GlobalEnv, other: &mut TypeEnvInfer, ty1: Ty, ty2: Ty) -> Ty {
        use TyKindJoin::*;

        // TODO(nilehmann) types can be equal but with different scopes
        if ty1 == ty2 {
            return ty1;
        }

        // if let TyKind::StrgRef(loc) = ty1.kind() {
        //     ty1 = self.borrow_weakly(*loc);
        // }

        // if let TyKind::StrgRef(loc) = ty2.kind() {
        //     ty2 = other.borrow_weakly(*loc);
        // }

        match (self.join_kind(&ty1), other.join_kind(&ty2)) {
            (Uninit, _) | (_, Uninit) => TyKind::Uninit.intern(),
            (StrgRef(loc1), StrgRef(loc2)) if loc1 != loc2 => {
                let ty = self.borrow_weakly(loc1);
                other.borrow_weakly(loc2);
                ty
            }
            (Refine(bty1, e1), Refine(bty2, e2)) if e1 == e2 => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                TyKind::Refine(bty, e1).intern()
            }
            (Packed(bty1, e1, _), Refine(bty2, _) | Packed(bty2, ..)) => {
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
            (Exists(bty1, _), Packed(bty2, ..) | Exists(bty2, ..) | Refine(bty2, ..)) => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            (Refine(bty1, _), Exists(bty2, _)) => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            (WeakRef(ty1), WeakRef(ty2)) => {
                TyKind::WeakRef(self.join_ty(genv, other, ty1, ty2)).intern()
            }
            (ShrRef(ty1), ShrRef(ty2)) => {
                TyKind::ShrRef(self.join_ty(genv, other, ty1, ty2)).intern()
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

    fn fresh(&mut self, sort: Sort) -> Name {
        let fresh = self.name_gen.fresh();
        self.params.insert(fresh, sort);
        fresh
    }

    fn weaken_ref(&mut self, loc: Loc) -> Ty {
        let ty = self.env.bindings[&loc].clone();
        let ty = self.weaken_ty(ty);
        self.env.bindings.insert(loc, ty.clone());
        TyKind::WeakRef(ty).intern()
    }

    fn borrow_weakly(&mut self, loc: Loc) -> Ty {
        // TODO(nilehmann) this should introduce a pledge on fresh
        let fresh = self.fresh(Sort::loc());
        let ty = self.env.bindings[&loc].clone();
        let ty = self.weaken_ty(ty);
        self.env.bindings.insert(loc, ty.clone());
        self.env.bindings.insert(Loc::Abstract(fresh), ty);
        TyKind::StrgRef(Loc::Abstract(fresh)).intern()
    }

    fn weaken_ty(&mut self, ty: Ty) -> Ty {
        use TyKindJoin::*;
        match self.join_kind(&ty) {
            Param(_) => ty,
            Packed(bty, _, name) => {
                self.params.remove(&name);
                let bty = self.weaken_bty(&bty);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            Exists(bty, _) | Refine(bty, _) => {
                let bty = self.weaken_bty(&bty);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            StrgRef(loc) => {
                let ty = self.env.bindings[&loc].clone();
                let ty = self.weaken_ty(ty);
                self.env.bindings.insert(loc, ty.clone());
                TyKind::WeakRef(ty).intern()
            }
            ShrRef(_) | WeakRef(_) => todo!(),
            Uninit => {
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

    pub fn into_bb_env(
        self,
        genv: &GlobalEnv,
        fresh_kvar: &mut impl FnMut(Var, Sort, &[Param]) -> Pred,
        env: &TypeEnv,
    ) -> BasicBlockEnv {
        let mut params = vec![];
        let mut constrs = vec![];
        // HACK(nilehmann) it is crucial that the order in this iteration is the same than
        // [`TypeEnvInfer::enter`] otherwise names will be out of order in the checking phase.
        for (name, sort) in self.params {
            constrs.push(fresh_kvar(name.into(), sort.clone(), &params));
            params.push(Param { name, sort });
        }

        let fresh_kvar = &mut |var, sort| fresh_kvar(var, sort, &params);
        let bindings = self
            .env
            .bindings
            .into_iter()
            .map(|(loc, ty)| (loc, replace_kvars(genv, &ty, fresh_kvar)))
            .collect();

        // HACK(nilehmann) the inference algorithm doesn't track pledges so we keep the pledges from
        // the first environment we are jumping from.
        let pledges = env
            .pledges
            .iter()
            .map(|(loc, pledge)| (*loc, replace_kvars(genv, pledge, fresh_kvar)))
            .collect();
        BasicBlockEnv { params, constrs, env: TypeEnv { bindings, pledges } }
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
        self.subst(&subst)
    }

    pub fn subst(&self, subst: &Subst) -> TypeEnv {
        TypeEnv {
            bindings: self
                .env
                .bindings
                .iter()
                .map(|(loc, ty)| (subst.subst_loc(*loc), subst.subst_ty(ty)))
                .collect(),
            pledges: self
                .env
                .pledges
                .iter()
                .map(|(loc, pledge)| (subst.subst_loc(*loc), subst.subst_ty(pledge)))
                .collect(),
        }
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
                .bindings
                .iter()
                .filter(|(_, ty)| !ty.is_uninit())
                .sorted_by(|(loc1, _), (loc2, _)| loc1.cmp(loc2))
                .collect_vec();

            let pledges = self
                .pledges
                .iter()
                .filter(|(_, ty)| !ty.is_uninit())
                .sorted_by(|(loc1, _), (loc2, _)| loc1.cmp(loc2))
                .collect_vec();

            w!(
                "{{{}}}",
                ^bindings
                    .into_iter()
                    .format_with(", ", |(loc, ty), f| f(&format_args_cx!("{:?}: {:?}", loc, ty)))
            )?;
            if !pledges.is_empty() {
                w!(
                    " [{}]",
                    ^pledges
                        .into_iter()
                        .format_with(", ", |(loc, ty), f| f(&format_args_cx!("{:?}: {:?}", loc, ty)))
                )?;
            }
            Ok(())
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
                "∃ {}.  {:?}",
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
                "∃ {}.  {:?}",
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

    impl_debug_with_default_cx!(TypeEnv, TypeEnvInfer, BasicBlockEnv);
}
