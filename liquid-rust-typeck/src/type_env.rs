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
    pledges: FxHashMap<Loc, Vec<Ty>>,
}

pub struct TypeEnvInfer {
    params: FxHashMap<Name, Sort>,
    scope: Scope,
    name_gen: IndexGen<Name>,
    env: TypeEnv,
}

pub struct BasicBlockEnv {
    pub params: Vec<Param>,
    constrs: Vec<Option<Pred>>,
    pub env: TypeEnv,
}

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv { bindings: FxHashMap::default(), pledges: FxHashMap::default() }
    }

    pub fn into_infer(self, genv: &GlobalEnv, scope: Scope) -> TypeEnvInfer {
        TypeEnvInfer::new(genv, scope, self)
    }

    pub fn lookup_local(&self, local: Local) -> Ty {
        self.lookup_loc(Loc::Local(local))
    }

    #[track_caller]
    pub fn lookup_loc(&self, loc: Loc) -> Ty {
        self.bindings
            .get(&loc)
            .unwrap_or_else(|| panic!("loc not found: `{loc:?}`"))
            .clone()
    }

    pub fn has_loc(&self, loc: Loc) -> bool {
        self.bindings.contains_key(&loc)
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
        for pledge in self.pledges.get(&loc).iter().flat_map(|v| v.iter()) {
            gen.subtyping(new_ty.clone(), pledge.clone());
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
                self.pledges.insert(fresh, vec![pledge.clone()]);
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
        for (loc, pledges) in self.pledges.iter_mut() {
            pledges.extend(
                other
                    .pledges
                    .get(loc)
                    .iter()
                    .flat_map(|v| v.iter().cloned()),
            );
        }

        // TODO(nilehmann) we should also join pledges
        debug_assert_eq!(self.bindings, other.bindings);
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

    pub fn subst(self, subst: &Subst) -> TypeEnv {
        TypeEnv {
            bindings: self
                .bindings
                .into_iter()
                .map(|(loc, ty)| (subst.subst_loc(loc), subst.subst_ty(&ty)))
                .collect(),
            pledges: self
                .pledges
                .into_iter()
                .map(|(loc, pledges)| {
                    let loc = subst.subst_loc(loc);
                    let pledges = pledges.into_iter().map(|ty| subst.subst_ty(&ty)).collect();
                    (loc, pledges)
                })
                .collect(),
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
        self.env.clone().subst(&subst)
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

    fn new(genv: &GlobalEnv, scope: Scope, env: TypeEnv) -> TypeEnvInfer {
        let name_gen = scope.name_gen();
        let mut params = FxHashMap::default();
        let mut env = TypeEnvInfer::pack_refs(&mut params, &scope, &name_gen, env);
        for loc in env.bindings.keys().copied().collect_vec() {
            // TODO(nilehmann) Figure out what to do with pledges
            let ty = env.lookup_loc(loc);
            env.bindings
                .insert(loc, TypeEnvInfer::pack_ty(&mut params, genv, &scope, &name_gen, &ty));
        }
        TypeEnvInfer { params, name_gen, env, scope }
    }

    fn pack_refs(
        params: &mut FxHashMap<Name, Sort>,
        scope: &Scope,
        name_gen: &IndexGen<Name>,
        env: TypeEnv,
    ) -> TypeEnv {
        let mut subst = Subst::empty();
        for loc in env.bindings.keys() {
            if let Loc::Abstract(loc) = loc {
                if !scope.contains(*loc) {
                    let fresh = name_gen.fresh();
                    params.insert(fresh, Sort::loc());
                    subst.insert_name_subst(*loc, Sort::loc(), fresh);
                }
            }
        }
        env.subst(&subst)
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
                let e = if e.has_free_vars(scope) {
                    let fresh = name_gen.fresh();
                    params.insert(fresh, genv.sort(bty));
                    ExprKind::Var(fresh.into()).intern()
                } else {
                    e.clone()
                };
                let bty = TypeEnvInfer::pack_bty(params, genv, scope, name_gen, bty);
                TyKind::Refine(bty, e).intern()
            }
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

    pub fn join(&mut self, genv: &GlobalEnv, other: TypeEnv) -> bool {
        let mut subst = Subst::empty();
        for loc in self.env.bindings.keys() {
            if !loc.has_free_vars(&self.scope) {
                let ty1 = self.env.lookup_loc(*loc);
                let ty2 = other.lookup_loc(*loc);
                match (ty1.kind(), ty2.kind()) {
                    (TyKind::StrgRef(loc1), TyKind::StrgRef(Loc::Abstract(loc2)))
                        if self.is_packed_loc(*loc1) && !self.scope.contains(*loc2) =>
                    {
                        subst.insert_loc_subst(*loc2, *loc1);
                    }
                    _ => {}
                }
            }
        }
        println!("\n{self:?}\n{other:?}\n{subst:?}");
        let mut other = other.subst(&subst);

        let levels = self
            .env
            .levels()
            .into_iter()
            .sorted_by_key(|(_, level)| *level)
            .rev();

        let mut modified = false;
        for (loc, _) in levels {
            if !other.has_loc(loc) {
                continue;
            }
            let ty1 = self.env.lookup_loc(loc);
            let ty2 = other.lookup_loc(loc);
            let ty = self.join_ty(genv, &mut other, &ty1, &ty2);
            modified |= ty1 != ty;
            self.env.bindings.insert(loc, ty);
        }

        modified
    }

    fn join_ty(&mut self, genv: &GlobalEnv, other: &mut TypeEnv, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Uninit, _) | (_, TyKind::Uninit) => TyKind::Uninit.intern(),
            (TyKind::StrgRef(loc1), TyKind::StrgRef(loc2)) => {
                if loc1 == loc2 {
                    TyKind::StrgRef(*loc1).intern()
                } else {
                    let (fresh, pledge) = self.borrow_weakly(*loc1);
                    other.bindings.insert(*loc2, pledge.clone());
                    TyKind::StrgRef(fresh.into()).intern()
                }
            }
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                let bty = self.join_bty(genv, other, &bty1, bty2);
                let e = if !self.is_packed_expr(e1) && (e2.has_free_vars(&self.scope) || e1 != e2) {
                    ExprKind::Var(self.fresh(genv.sort(&bty)).into()).intern()
                } else {
                    e1.clone()
                };
                TyKind::Refine(bty, e).intern()
            }
            (TyKind::Exists(bty1, _), TyKind::Refine(bty2, ..) | TyKind::Exists(bty2, ..))
            | (TyKind::Refine(bty1, _), TyKind::Exists(bty2, ..)) => {
                let bty = self.join_bty(genv, other, &bty1, &bty2);
                TyKind::Exists(bty, Pred::dummy_kvar()).intern()
            }
            (TyKind::WeakRef(ty1), TyKind::WeakRef(ty2)) => {
                TyKind::WeakRef(self.join_ty(genv, other, &ty1, ty2)).intern()
            }
            (TyKind::ShrRef(ty1), TyKind::ShrRef(ty2)) => {
                TyKind::ShrRef(self.join_ty(genv, other, &ty1, ty2)).intern()
            }
            _ => todo!("`{ty1:?}` -- `{ty2:?}`"),
        }
    }

    fn join_bty(
        &mut self,
        genv: &GlobalEnv,
        other: &mut TypeEnv,
        bty1: &BaseTy,
        bty2: &BaseTy,
    ) -> BaseTy {
        if let (BaseTy::Adt(did1, substs1), BaseTy::Adt(did2, substs2)) = (bty1, bty2) {
            debug_assert_eq!(did1, did2);
            let variances = genv.variances_of(*did1);
            let substs =
                izip!(variances, substs1.iter(), substs2.iter()).map(|(variance, ty1, ty2)| {
                    assert!(matches!(variance, rustc_middle::ty::Variance::Covariant));
                    self.join_ty(genv, other, ty1, ty2)
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

    fn borrow_weakly(&mut self, loc: Loc) -> (Name, Ty) {
        // TODO(nilehmann) this should introduce a pledge on fresh
        let fresh = self.fresh(Sort::loc());
        let ty = self.env.bindings[&loc].clone();
        let pledge = self.weaken_ty(ty);
        self.env.bindings.insert(loc, pledge.clone());
        self.env
            .bindings
            .insert(Loc::Abstract(fresh), pledge.clone());
        (fresh, pledge)
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
            if sort != Sort::loc() {
                constrs.push(Some(fresh_kvar(name.into(), sort.clone(), &params)));
            } else {
                constrs.push(None)
            }
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
        let pledges = env.pledges.clone();

        BasicBlockEnv { params, constrs, env: TypeEnv { bindings, pledges } }
    }

    fn is_packed_expr(&self, expr: &Expr) -> bool {
        matches!(expr.kind(), ExprKind::Var(Var::Free(name)) if self.params.contains_key(name))
    }

    fn is_packed_loc(&self, loc: Loc) -> bool {
        matches!(loc, Loc::Abstract(name) if self.params.contains_key(&name))
    }
}

impl BasicBlockEnv {
    pub fn enter(&self, pcx: &mut PureCtxt) -> TypeEnv {
        let mut subst = Subst::empty();
        for (param, constr) in self.params.iter().zip(&self.constrs) {
            pcx.push_binding(param.sort.clone(), |fresh| {
                subst.insert_param(param, fresh);
                constr
                    .as_ref()
                    .map(|p| subst.subst_pred(p))
                    .unwrap_or_else(|| Pred::tt())
            });
        }
        self.env.clone().subst(&subst)
    }

    pub fn constrs(&self) -> impl Iterator<Item = &Pred> {
        self.constrs.iter().filter_map(|c| c.as_ref())
    }

    // TODO(nilehmann) this is weird beause it's skipping the parameters
    pub fn subst(&self, subst: &Subst) -> TypeEnv {
        self.env.clone().subst(subst)
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
                .filter(|(_, pledges)| !pledges.is_empty())
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
                    " ~ {{{}}}",
                    ^pledges
                        .into_iter()
                        .format_with(", ", |(loc, pledges), f| {
                            f(&format_args_cx!("{:?}: [{:?}]", loc, join!(", ", pledges.iter().filter(|ty| !ty.is_uninit()))))
                        })
                )?;
            }
            Ok(())
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for TypeEnvInfer {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "{:?} ∃ {}. {:?}",
                &self.scope,
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
                "∃ {}, {:?}. {:?}",
                ^self.params
                    .iter()
                    .format_with(", ", |param, f| f(&format_args_cx!("{:?}: {:?}", ^param.name, ^param.sort))),
                join!(", ", self.constrs.iter().filter_map(|c| c.as_ref())),
                &self.env
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl_debug_with_default_cx!(TypeEnv => "type_env", TypeEnvInfer => "type_env_infer", BasicBlockEnv => "basic_block_env");
}
