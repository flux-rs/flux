pub mod paths_tree;

use std::iter;

use crate::{
    constraint_gen::ConstraintGen,
    global_env::GlobalEnv,
    pure_ctxt::{PureCtxt, Scope},
    subst::Subst,
    ty::{BaseTy, Expr, ExprKind, Param, Path, Ty, TyKind, Var},
};
use itertools::{izip, Itertools};
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::{ir, ty::Layout};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;

use self::paths_tree::{PathsTree, Read, Write};

use super::ty::{Loc, Name, Pred, Sort};

#[derive(Clone, Default)]
pub struct TypeEnv {
    bindings: PathsTree,
    pledges: Pledges,
    layouts: FxHashMap<Loc, Layout>,
}

#[derive(Clone, Default)]
struct Pledges {
    map: FxHashMap<Loc, Vec<Ty>>,
}

pub struct TypeEnvInfer {
    params: FxHashMap<Name, Sort>,
    scope: Scope,
    name_gen: IndexGen<Name>,
    env: TypeEnv,
}

pub struct BasicBlockEnv {
    pub params: Vec<Param>,
    constrs: Vec<Pred>,
    scope: Scope,
    pub env: TypeEnv,
}

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv {
            bindings: PathsTree::default(),
            pledges: Pledges::default(),
            layouts: FxHashMap::default(),
        }
    }

    pub fn alloc_with_ty(&mut self, loc: impl Into<Loc>, ty: Ty) {
        let loc = loc.into();
        self.layouts.insert(loc, ty.layout());
        self.bindings.insert(loc, ty);
    }

    pub fn alloc(&mut self, loc: impl Into<Loc>, layout: Layout) {
        let loc = loc.into();
        self.layouts.insert(loc, layout);
        self.bindings.insert(loc, Ty::uninit(layout));
    }

    pub fn into_infer(self, genv: &GlobalEnv, scope: Scope) -> TypeEnvInfer {
        TypeEnvInfer::new(genv, scope, self)
    }

    fn remove(&mut self, loc: Loc) {
        self.bindings.remove(loc);
        self.pledges.remove(loc);
    }

    pub fn lookup_place(&mut self, genv: &GlobalEnv, place: &ir::Place) -> Ty {
        self.bindings.lookup_place(Read, genv, place, |_, ty| ty)
    }

    pub fn lookup_path(&self, path: &Path) -> Ty {
        self.bindings[path].clone()
    }

    pub fn update_path(&mut self, gen: &mut ConstraintGen, path: &Path, new_ty: Ty) {
        self.pledges.check(gen, path, &new_ty);
        self.bindings[path] = new_ty;
    }

    pub fn borrow_mut(&mut self, place: &ir::Place) -> Ty {
        let loc = Loc::Local(place.local);
        let ty = &self.bindings[&Path::new(loc, vec![])];
        let loc = match (&place.projection[..], ty.kind()) {
            ([], _) => loc,
            ([ir::PlaceElem::Deref], TyKind::StrgRef(loc)) => *loc,
            ([ir::PlaceElem::Deref], TyKind::WeakRef(_)) => {
                unreachable!("mutable borrow with unpacked weak ref")
            }
            ([ir::PlaceElem::Deref], TyKind::ShrRef(_)) => {
                unreachable!("cannot borrow mutably from a shared ref")
            }
            _ => unreachable!("unxepected place `{place:?}`"),
        };
        Ty::strg_ref(loc)
    }

    pub fn borrow_shr(&mut self, place: &ir::Place) -> Ty {
        let loc = Loc::Local(place.local);
        let ty = self.bindings[&Path::new(loc, vec![])].clone();
        match (&place.projection[..], ty.kind()) {
            ([], _) => Ty::shr_ref(ty),
            ([ir::PlaceElem::Deref], TyKind::StrgRef(loc)) => {
                let ty = self.bindings[&Path::new(*loc, vec![])].clone();
                Ty::shr_ref(ty)
            }
            ([ir::PlaceElem::Deref], TyKind::ShrRef(ty)) => Ty::shr_ref(ty.clone()),
            ([ir::PlaceElem::Deref], TyKind::WeakRef(_)) => {
                unreachable!("shared borrow with unpacked weak ref")
            }
            _ => unreachable!("unxepected place `{place:?}`"),
        }
    }

    pub fn write_place(&mut self, gen: &mut ConstraintGen, place: &ir::Place, new_ty: Ty) {
        self.bindings
            .lookup_place(Write, gen.genv, place, |path, ty| {
                self.pledges.check(gen, &path, &new_ty);
                *ty = new_ty;
            });
    }

    pub fn move_place(&mut self, genv: &GlobalEnv, place: &ir::Place) -> Ty {
        self.bindings.lookup_place(Write, genv, place, |_, ty| {
            let old = ty.clone();
            *ty = Ty::uninit(ty.layout());
            old
        })
    }

    pub fn unpack_ty(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(bty, p) => {
                let exprs = pcx.push_bindings(&genv.sorts(bty), p);
                Ty::refine(bty.clone(), exprs)
            }
            TyKind::WeakRef(pledge) => {
                let fresh = pcx.push_loc();
                let ty = self.unpack_ty(genv, pcx, pledge);
                self.bindings.insert(fresh, ty);
                self.pledges.insert(fresh, pledge.clone());
                Ty::strg_ref(fresh)
            }
            TyKind::ShrRef(ty) => {
                let ty = self.unpack_ty(genv, pcx, ty);
                Ty::shr_ref(ty)
            }
            _ => ty.clone(),
        }
    }

    pub fn unpack(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt) {
        for path in self.bindings.paths().collect_vec() {
            let ty = self.bindings[&path].clone();
            let ty = self.unpack_ty(genv, pcx, &ty);
            self.bindings[&path] = ty;
        }
    }

    fn infer_subst_for_bb_env(&self, bb_env: &BasicBlockEnv) -> Subst {
        let params = bb_env.params.iter().map(|param| param.name).collect();
        let mut subst = Subst::empty();
        for (path, ty1) in self.bindings.iter() {
            if bb_env.env.bindings.contains_loc(path.loc) {
                let ty2 = &bb_env.env.bindings[&path];
                self.infer_subst_for_bb_env_tys(bb_env, &params, ty1, ty2, &mut subst);
            }
        }
        assert!(subst
            .check_inference(
                bb_env
                    .params
                    .iter()
                    .filter(|param| !param.sort.is_loc())
                    .map(|param| param.name)
            )
            .is_ok());
        subst
    }

    fn infer_subst_for_bb_env_tys(
        &self,
        bb_env: &BasicBlockEnv,
        params: &FxHashSet<Name>,
        ty1: &Ty,
        ty2: &Ty,
        subst: &mut Subst,
    ) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(_, exprs1), TyKind::Refine(_, exprs2)) => {
                for (e1, e2) in iter::zip(exprs1, exprs2) {
                    subst.infer_from_exprs(params, e1, e2);
                }
            }
            (TyKind::StrgRef(Loc::Abstract(loc1)), TyKind::StrgRef(Loc::Abstract(loc2)))
                if !bb_env.scope.contains(*loc1) && !bb_env.scope.contains(*loc2) =>
            {
                subst.insert_loc_subst(*loc2, *loc1);
                let ty1 = &self.bindings[&Path::new(Loc::Abstract(*loc1), vec![])];
                let ty2 = &bb_env.env.bindings[&Path::new(Loc::Abstract(*loc2), vec![])];
                self.infer_subst_for_bb_env_tys(bb_env, params, ty1, ty2, subst);
            }
            (TyKind::ShrRef(ty1), TyKind::ShrRef(ty2)) => {
                self.infer_subst_for_bb_env_tys(bb_env, params, ty1, ty2, subst);
            }
            _ => {}
        }
    }

    pub fn check_goto(mut self, gen: &mut ConstraintGen, bb_env: &mut BasicBlockEnv) {
        self.bindings
            .fold_unfold_to_match(gen.genv, &bb_env.env.bindings);

        // Infer subst
        let subst = self.infer_subst_for_bb_env(bb_env);

        // Check constraints
        for (param, constr) in iter::zip(&bb_env.params, &bb_env.constrs) {
            gen.check_pred(subst.subst_pred(&constr.subst_bound_vars(&[Expr::var(param.name)])));
        }

        let goto_env = bb_env.env.clone().subst(&subst);

        // Weakening
        let locs = self
            .bindings
            .locs()
            .filter(|loc| !goto_env.bindings.contains_loc(*loc))
            .collect_vec();
        for loc in locs {
            self.remove(loc);
        }

        // Create pledged borrows
        for path in self.bindings.paths().collect_vec() {
            let ty1 = &self.bindings[&path];
            let ty2 = &goto_env.bindings[&path];
            match (ty1.kind(), ty2.kind()) {
                (&TyKind::StrgRef(loc1), &TyKind::StrgRef(loc2)) if loc1 != loc2 => {
                    let pledge = goto_env.bindings[&Path::new(loc2, vec![])].clone();
                    let fresh = self.pledged_borrow(gen, loc1, pledge);
                    self.bindings[&path] = Ty::strg_ref(fresh);
                }
                _ => {}
            }
        }

        // Check subtyping
        for (path, ty1) in self.bindings.iter_mut() {
            let ty2 = goto_env.bindings[&path].clone();
            gen.subtyping(ty1, &ty2);
            *ty1 = ty2;
        }

        // HACK(nilehmann) the inference algorithm doesn't track pledges so we insert
        // the pledges from all the environements we jump from.
        bb_env.env.pledges.merge_with(self.pledges);

        debug_assert_eq!(self.bindings, goto_env.bindings);
    }

    fn pledged_borrow(&mut self, gen: &mut ConstraintGen, loc: Loc, pledge: Ty) -> Loc {
        let fresh = gen.push_loc();
        let ty = &self.bindings[&Path::new(loc, vec![])];
        gen.subtyping(ty, &pledge);
        self.bindings[&Path::new(loc, vec![])] = pledge.clone();
        self.bindings.insert(fresh, pledge.clone());
        self.pledges.insert(fresh, pledge);
        fresh
    }

    pub fn subst(self, subst: &Subst) -> TypeEnv {
        TypeEnv {
            bindings: self.bindings.subst(subst),
            pledges: self.pledges.subst(subst),
            layouts: self.layouts,
        }
    }
}

impl Pledges {
    fn remove(&mut self, loc: Loc) {
        self.map.remove(&loc);
    }

    fn insert(&mut self, loc: Loc, pledge: Ty) {
        self.map.insert(loc, vec![pledge]);
    }

    fn check(&self, gen: &mut ConstraintGen, path: &Path, ty: &Ty) {
        if let Some(pledges) = self.map.get(&path.loc) {
            assert!(path.projection().is_empty());
            for pledge in pledges.iter() {
                gen.subtyping(ty, pledge);
            }
        }
    }

    fn subst(self, subst: &Subst) -> Pledges {
        Pledges {
            map: self
                .map
                .into_iter()
                .map(|(loc, pledges)| {
                    let loc = subst.subst_loc(loc);
                    let pledges = pledges.into_iter().map(|ty| subst.subst_ty(&ty)).collect();
                    (loc, pledges)
                })
                .collect(),
        }
    }

    fn merge_with(&mut self, other: Pledges) {
        for (loc, pledges) in other.map {
            self.map.entry(loc).or_default().extend(pledges);
        }
    }
}

impl TypeEnvInfer {
    pub fn enter(&self, pcx: &mut PureCtxt) -> TypeEnv {
        let mut subst = Subst::empty();
        // HACK(nilehmann) it is crucial that the order in this iteration is the same than
        // [`TypeEnvInfer::into_bb_env`] otherwise names will be out of order in the checking phase.
        for (name, sort) in self.params.iter() {
            let mut exprs = pcx.push_bindings(&[sort.clone()], &Pred::tt());
            subst.insert(*name, sort, exprs.pop().unwrap());
        }
        self.env.clone().subst(&subst)
    }

    fn new(genv: &GlobalEnv, scope: Scope, env: TypeEnv) -> TypeEnvInfer {
        let name_gen = scope.name_gen();
        let mut params = FxHashMap::default();
        let mut env = TypeEnvInfer::pack_refs(&mut params, &scope, &name_gen, env);
        for ty in env.bindings.values_mut() {
            *ty = TypeEnvInfer::pack_ty(&mut params, genv, &scope, &name_gen, ty);
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

        for loc in env.bindings.locs() {
            if let Loc::Abstract(loc) = loc {
                if !scope.contains(loc) {
                    let fresh = name_gen.fresh();
                    params.insert(fresh, Sort::loc());
                    subst.insert_loc_subst(loc, fresh);
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
            TyKind::Refine(bty, exprs) => {
                let sorts = genv.sorts(bty);
                let exprs = exprs
                    .iter()
                    .zip(sorts)
                    .map(|(e, sort)| {
                        if e.has_free_vars(scope) {
                            let fresh = name_gen.fresh();
                            params.insert(fresh, sort);
                            Expr::var(fresh)
                        } else {
                            e.clone()
                        }
                    })
                    .collect_vec();
                let bty = TypeEnvInfer::pack_bty(params, genv, scope, name_gen, bty);
                Ty::refine(bty, exprs)
            }
            // TODO(nilehmann) [`TyKind::Exists`] could also in theory contains free variables.
            TyKind::Exists(_, _)
            | TyKind::Float(_)
            | TyKind::StrgRef(_)
            | TyKind::Uninit(_)
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

    pub fn join(&mut self, genv: &GlobalEnv, mut other: TypeEnv) -> bool {
        // Unfold
        self.env.bindings.unfold_with(genv, &mut other.bindings);

        // Infer subst
        let mut subst = Subst::empty();
        for (path, ty1) in self.env.bindings.iter() {
            if other.bindings.contains_loc(path.loc) {
                let ty2 = &other.bindings[&path];
                match (ty1.kind(), ty2.kind()) {
                    (TyKind::StrgRef(loc1), TyKind::StrgRef(Loc::Abstract(loc2)))
                        if self.packed_loc(*loc1).is_some() && !self.scope.contains(*loc2) =>
                    {
                        subst.insert_loc_subst(*loc2, *loc1);
                    }
                    _ => {}
                }
            }
        }

        let mut other = other.subst(&subst);

        // Weakening
        let locs = self
            .env
            .bindings
            .locs()
            .filter(|loc| !other.bindings.contains_loc(*loc))
            .collect_vec();
        for loc in locs {
            if let Some(loc) = self.packed_loc(loc) {
                self.params.remove(&loc);
            }
            self.env.remove(loc);
        }

        let paths = self.env.bindings.paths().collect_vec();

        // Create pledged borrows
        for path in &paths {
            let ty1 = &self.env.bindings[path];
            let ty2 = &other.bindings[path];
            match (ty1.kind(), ty2.kind()) {
                (&TyKind::StrgRef(loc1), &TyKind::StrgRef(loc2)) if loc1 != loc2 => {
                    let (fresh, pledge) = self.pledged_borrow(genv, loc1);
                    self.env.bindings[path] = Ty::strg_ref(fresh);
                    other.bindings[path] = Ty::strg_ref(fresh);
                    other.bindings[&Path::new(loc2, vec![])] = pledge.clone();
                    other.bindings.insert(fresh, pledge);
                }
                _ => {}
            }
        }

        // Join types
        let mut modified = false;
        for path in &paths {
            let ty1 = self.env.bindings[path].clone();
            let ty2 = other.bindings[path].clone();
            let ty = self.join_ty(genv, &mut other, &ty1, &ty2);
            modified |= ty1 != ty;
            self.env.bindings[path] = ty;
        }

        modified
    }

    fn join_ty(&mut self, genv: &GlobalEnv, other: &mut TypeEnv, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Uninit(layout), _) => {
                debug_assert_eq!(layout, &ty2.layout());
                Ty::uninit(*layout)
            }
            (_, TyKind::Uninit(layout)) => {
                debug_assert_eq!(layout, &ty1.layout());
                Ty::uninit(*layout)
            }
            (TyKind::StrgRef(loc1), TyKind::StrgRef(loc2)) => {
                debug_assert_eq!(loc1, loc2);
                Ty::strg_ref(*loc1)
            }
            (TyKind::Refine(bty1, exprs1), TyKind::Refine(bty2, exprs2)) => {
                let bty = self.join_bty(genv, other, bty1, bty2);
                let exprs = izip!(exprs1, exprs2, genv.sorts(&bty))
                    .map(|(e1, e2, sort)| {
                        if !self.is_packed_expr(e1) && (e2.has_free_vars(&self.scope) || e1 != e2) {
                            Expr::var(self.fresh(sort))
                        } else {
                            e1.clone()
                        }
                    })
                    .collect_vec();
                Ty::refine(bty, exprs)
            }
            (TyKind::Exists(bty1, _), TyKind::Refine(bty2, ..) | TyKind::Exists(bty2, ..))
            | (TyKind::Refine(bty1, _), TyKind::Exists(bty2, ..)) => {
                let bty = self.join_bty(genv, other, bty1, bty2);
                let sorts = genv.sorts(&bty);
                Ty::exists(bty, Pred::dummy_infer(&sorts))
            }
            (TyKind::WeakRef(ty1), TyKind::WeakRef(ty2)) => {
                Ty::weak_ref(self.join_ty(genv, other, ty1, ty2))
            }
            (TyKind::ShrRef(ty1), TyKind::ShrRef(ty2)) => {
                Ty::shr_ref(self.join_ty(genv, other, ty1, ty2))
            }
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ty::float(*float_ty1)
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
                Ty::param(*param_ty1)
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
            let substs = izip!(variances, substs1, substs2).map(|(variance, ty1, ty2)| {
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

    fn pledged_borrow(&mut self, genv: &GlobalEnv, loc: Loc) -> (Loc, Ty) {
        let fresh = Loc::Abstract(self.fresh(Sort::loc()));
        let ty = self.env.bindings[&Path::new(loc, vec![])].clone();
        let pledge = self.weaken_ty(genv, &ty);
        self.env.bindings.insert(loc, pledge.clone());
        self.env.bindings.insert(fresh, pledge.clone());
        (fresh, pledge)
    }

    fn weaken_ty(&mut self, genv: &GlobalEnv, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Param(_) | TyKind::Float(_) => ty.clone(),
            TyKind::Exists(bty, _) => {
                let bty = self.weaken_bty(genv, bty);
                let sorts = genv.sorts(&bty);
                Ty::exists(bty, Pred::dummy_infer(&sorts))
            }
            TyKind::Refine(bty, exprs) => {
                for e in exprs {
                    match e.kind() {
                        ExprKind::Var(Var::Free(name)) if self.params.contains_key(name) => {
                            self.params.remove(name);
                        }
                        _ => {}
                    }
                }
                let bty = self.weaken_bty(genv, bty);
                let sort = genv.sorts(&bty);
                Ty::exists(bty, Pred::dummy_infer(&sort))
            }
            TyKind::StrgRef(loc) => {
                let ty = self.env.bindings[&Path::new(*loc, vec![])].clone();
                let ty = self.weaken_ty(genv, &ty);
                self.env.bindings.insert(*loc, ty.clone());
                Ty::weak_ref(ty)
            }
            TyKind::ShrRef(_) | TyKind::WeakRef(_) => todo!(),
            TyKind::Uninit(_) => {
                unreachable!()
            }
        }
    }

    fn weaken_bty(&mut self, genv: &GlobalEnv, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(did, substs) => {
                let substs = substs.iter().map(|ty| self.weaken_ty(genv, ty));
                BaseTy::adt(*did, substs)
            }
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty.clone(),
        }
    }

    pub fn into_bb_env(
        self,
        genv: &GlobalEnv,
        fresh_kvar: &mut impl FnMut(&[Sort], &[Param]) -> Pred,
        env: &TypeEnv,
    ) -> BasicBlockEnv {
        let mut params = vec![];
        let mut constrs = vec![];
        // HACK(nilehmann) it is crucial that the order in this iteration is the same than
        // [`TypeEnvInfer::enter`] otherwise names will be out of order in the checking phase.
        for (name, sort) in self.params {
            if sort != Sort::loc() {
                constrs.push(fresh_kvar(&[sort.clone()], &params));
            } else {
                constrs.push(Pred::tt())
            }
            params.push(Param { name, sort });
        }

        let fresh_kvar = &mut |sorts: &[Sort]| fresh_kvar(sorts, &params);

        let mut bindings = self.env.bindings;
        for ty in bindings.values_mut() {
            *ty = replace_dummy_kvars(genv, ty, fresh_kvar);
        }

        // HACK(nilehmann) the inference algorithm doesn't track pledges so we insert
        // the pledges from all the environements we jump from.
        let pledges = env.pledges.clone();

        let layouts = self.env.layouts;

        BasicBlockEnv {
            params,
            constrs,
            env: TypeEnv { bindings, pledges, layouts },
            scope: self.scope,
        }
    }

    fn is_packed_expr(&self, expr: &Expr) -> bool {
        matches!(expr.kind(), ExprKind::Var(Var::Free(name)) if self.params.contains_key(name))
    }

    fn packed_loc(&self, loc: Loc) -> Option<Name> {
        match loc {
            Loc::Abstract(name) if self.params.contains_key(&name) => Some(name),
            _ => None,
        }
    }
}

impl BasicBlockEnv {
    pub fn enter(&self, pcx: &mut PureCtxt) -> TypeEnv {
        let mut subst = Subst::empty();
        for (param, constr) in self.params.iter().zip(&self.constrs) {
            let mut exprs = pcx.push_bindings(&[param.sort.clone()], &subst.subst_pred(constr));
            subst.insert(param.name, &param.sort, exprs.pop().unwrap());
        }
        self.env.clone().subst(&subst)
    }
}

fn replace_dummy_kvars(
    genv: &GlobalEnv,
    ty: &Ty,
    fresh_kvar: &mut impl FnMut(&[Sort]) -> Pred,
) -> Ty {
    match ty.kind() {
        TyKind::Refine(bty, e) => {
            Ty::refine(replace_dummy_kvars_bty(genv, bty, fresh_kvar), e.clone())
        }
        TyKind::Exists(bty, p) => {
            let p = match p {
                Pred::Infer(_) => fresh_kvar(&genv.sorts(bty)),
                Pred::Expr(e) => Pred::Expr(e.clone()),
            };
            Ty::exists(replace_dummy_kvars_bty(genv, bty, fresh_kvar), p)
        }
        TyKind::WeakRef(ty) => Ty::weak_ref(replace_dummy_kvars(genv, ty, fresh_kvar)),
        TyKind::ShrRef(ty) => Ty::shr_ref(replace_dummy_kvars(genv, ty, fresh_kvar)),
        TyKind::StrgRef(_) | TyKind::Param(_) | TyKind::Uninit(_) | TyKind::Float(_) => ty.clone(),
    }
}

fn replace_dummy_kvars_bty(
    genv: &GlobalEnv,
    bty: &BaseTy,
    fresh_kvar: &mut impl FnMut(&[Sort]) -> Pred,
) -> BaseTy {
    match bty {
        BaseTy::Adt(did, substs) => {
            let substs = substs
                .iter()
                .map(|ty| replace_dummy_kvars(genv, ty, fresh_kvar));
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
                .filter(|(_, ty)| !cx.hide_uninit || !ty.is_uninit())
                .collect_vec();

            let pledges = self
                .pledges
                .map
                .iter()
                .filter(|(_, pledges)| !pledges.is_empty())
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
                            f(&format_args_cx!("{:?}: [{:?}]", loc, join!(", ", pledges)))
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
                "∃ {}. {:?}",
                ^self.params
                    .iter()
                    .zip(&self.constrs)
                    .format_with(", ", |(param, constr), f| {
                        if constr.is_true() {
                            f(&format_args_cx!("{:?}: {:?}", ^param.name, ^param.sort))
                        } else {
                            f(&format_args_cx!("{:?}: {:?}{{{:?}}}", ^param.name, ^param.sort, constr))
                        }
                    }),
                &self.env
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl_debug_with_default_cx!(TypeEnv => "type_env", TypeEnvInfer => "type_env_infer", BasicBlockEnv => "basic_block_env");
}
