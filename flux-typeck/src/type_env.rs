pub mod paths_tree;

use std::iter;

use flux_common::index::IndexGen;
use flux_middle::{
    global_env::OpaqueStructErr,
    intern::List,
    rty::{
        box_args, fold::TypeFoldable, subst::FVarSubst, BaseTy, Binders, Expr, GenericArg, Index,
        Path, RefKind, Ty, TyKind,
    },
    rustc::mir::{Local, Place, PlaceElem},
};
use itertools::Itertools;
use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;

use self::paths_tree::{Binding, FoldResult, LocKind, PathsTree};
use super::rty::{Loc, Name, Pred, Sort};
use crate::{
    constraint_gen::ConstrGen,
    fixpoint::KVarGen,
    param_infer,
    refine_tree::{RefineCtxt, Scope},
    rty::VariantIdx,
};

pub trait PathMap {
    fn get(&self, path: &Path) -> Ty;
    fn update(&mut self, path: &Path, ty: Ty);
}

#[derive(Clone, Default)]
pub struct TypeEnv {
    bindings: PathsTree,
}

pub struct TypeEnvInfer {
    scope: Scope,
    bindings: PathsTree,
}

pub struct BasicBlockEnv {
    params: Vec<(Name, Sort)>,
    constrs: Vec<Pred>,
    scope: Scope,
    bindings: PathsTree,
}

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv { bindings: PathsTree::default() }
    }

    pub fn alloc_universal_loc(&mut self, loc: Loc, ty: Ty) {
        self.bindings.insert(loc, ty, LocKind::Universal);
    }

    pub fn alloc_with_ty(&mut self, local: Local, ty: Ty) {
        self.bindings.insert(local.into(), ty, LocKind::Local);
    }

    pub fn alloc(&mut self, local: Local) {
        self.bindings
            .insert(local.into(), Ty::uninit(), LocKind::Local);
    }

    pub fn into_infer(
        self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        scope: Scope,
    ) -> TypeEnvInfer {
        TypeEnvInfer::new(rcx, gen, scope, self)
    }

    pub fn lookup_place(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
    ) -> Result<Ty, OpaqueStructErr> {
        Ok(self
            .bindings
            .lookup_place(gen.genv, rcx, place)?
            .fold(rcx, gen, true)
            .ty())
    }

    pub fn lookup_path(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        path: &Path,
    ) -> Result<Ty, OpaqueStructErr> {
        Ok(self
            .bindings
            .lookup_path(gen.genv, rcx, path)?
            .fold(rcx, gen, false)
            .ty())
    }

    pub fn update_path(&mut self, path: &Path, new_ty: Ty) {
        self.bindings.update(path, new_ty);
    }

    pub fn borrow(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        rk: RefKind,
        place: &Place,
    ) -> Result<Ty, OpaqueStructErr> {
        let ty = match self
            .bindings
            .lookup_place(gen.genv, rcx, place)?
            .fold(rcx, gen, true)
        {
            FoldResult::Strg(path, _) => Ty::ptr(rk, path),
            FoldResult::Ref(result_rk, ty) => {
                debug_assert!(rk <= result_rk);
                Ty::mk_ref(rk, ty)
            }
        };
        Ok(ty)
    }

    pub fn write_place(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
        new_ty: Ty,
    ) -> Result<(), OpaqueStructErr> {
        match self
            .bindings
            .lookup_place(gen.genv, rcx, place)?
            .fold(rcx, gen, true)
        {
            FoldResult::Strg(path, _) => {
                self.bindings.update(&path, new_ty);
            }
            FoldResult::Ref(RefKind::Mut, ty) => {
                gen.subtyping(rcx, &new_ty, &ty);
            }
            FoldResult::Ref(RefKind::Shr, _) => {
                panic!("cannot assign to `{place:?}`, which is behind a `&` reference")
            }
        }
        Ok(())
    }

    pub fn move_place(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
    ) -> Result<Ty, OpaqueStructErr> {
        match self
            .bindings
            .lookup_place(gen.genv, rcx, place)?
            .fold(rcx, gen, true)
        {
            FoldResult::Strg(path, ty) => {
                self.bindings.update(&path, Ty::uninit());
                Ok(ty)
            }
            FoldResult::Ref(RefKind::Mut, _) => {
                panic!("cannot move out of `{place:?}`, which is behind a `&mut` reference")
            }
            FoldResult::Ref(RefKind::Shr, _) => {
                panic!("cannot move out of `{place:?}`, which is behind a `&` reference")
            }
        }
    }

    pub fn unpack(&mut self, rcx: &mut RefineCtxt) {
        self.bindings.fmap_mut(|binding| {
            match binding {
                Binding::Owned(ty) => Binding::Owned(rcx.unpack(ty)),
                Binding::Blocked(ty) => Binding::Blocked(ty.clone()),
            }
        });
    }

    pub fn block(&mut self, path: &Path) {
        self.bindings.block(path)
    }

    fn infer_subst_for_bb_env(&self, bb_env: &BasicBlockEnv) -> FVarSubst {
        let params = bb_env.params.iter().map(|(name, _)| *name).collect();
        let mut subst = FVarSubst::empty();
        self.bindings.iter(|path, binding1| {
            let binding2 = bb_env.bindings.get(&path);
            if bb_env.bindings.contains_loc(path.loc)
              && let Binding::Owned(ty1) = binding1
              && let Binding::Owned(ty2) = binding2 {
                self.infer_subst_for_bb_env_ty(bb_env, &params, ty1, &ty2, &mut subst);
            }
        });

        param_infer::check_inference(
            &subst,
            bb_env
                .params
                .iter()
                .filter(|(_, sort)| !sort.is_loc())
                .map(|(name, _)| *name),
        )
        .unwrap();
        subst
    }

    fn infer_subst_for_bb_env_ty(
        &self,
        bb_env: &BasicBlockEnv,
        params: &FxHashSet<Name>,
        ty1: &Ty,
        ty2: &Ty,
        subst: &mut FVarSubst,
    ) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, indices1), TyKind::Indexed(bty2, indices2)) => {
                self.infer_subst_for_bb_env_bty(bb_env, params, bty1, bty2, subst);
                for (idx1, idx2) in iter::zip(indices1, indices2) {
                    subst.infer_from_exprs(params, &idx1.expr, &idx2.expr);
                }
            }
            (TyKind::Ptr(rk1, path1), TyKind::Ptr(rk2, path2)) => {
                debug_assert_eq!(rk1, rk2);
                debug_assert_eq!(path1, path2);
            }
            (TyKind::Ref(rk1, ty1), TyKind::Ref(rk2, ty2)) => {
                debug_assert_eq!(rk1, rk2);
                self.infer_subst_for_bb_env_ty(bb_env, params, ty1, ty2, subst);
            }
            (TyKind::Ptr(rk1, path), TyKind::Ref(rk2, ty2)) => {
                debug_assert_eq!(rk1, rk2);
                if let Binding::Owned(ty1) = self.bindings.get(path) {
                    self.infer_subst_for_bb_env_ty(bb_env, params, &ty1, ty2, subst);
                }
            }
            _ => {}
        }
    }

    fn infer_subst_for_bb_env_generic_arg(
        &self,
        bb_env: &BasicBlockEnv,
        params: &FxHashSet<Name>,
        arg1: &GenericArg,
        arg2: &GenericArg,
        subst: &mut FVarSubst,
    ) {
        if let (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) = (arg1, arg2) {
            self.infer_subst_for_bb_env_ty(bb_env, params, ty1, ty2, subst);
        }
    }

    fn infer_subst_for_bb_env_bty(
        &self,
        bb_env: &BasicBlockEnv,
        params: &FxHashSet<Name>,
        bty1: &BaseTy,
        bty2: &BaseTy,
        subst: &mut FVarSubst,
    ) {
        if bty1.is_box()  &&
           let BaseTy::Adt(_, substs1) = bty1 &&
           let BaseTy::Adt(_, substs2) = bty2 {
            for (arg1, arg2) in iter::zip(substs1, substs2) {
                self.infer_subst_for_bb_env_generic_arg(bb_env, params, arg1, arg2, subst);
            }
        }
    }

    pub fn check_goto(
        mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        bb_env: &BasicBlockEnv,
    ) -> Result<(), OpaqueStructErr> {
        self.bindings.close_boxes(rcx, gen, &bb_env.scope);

        // Look up paths to make sure they are properly folded/unfolded
        for path in bb_env.bindings.paths() {
            self.bindings
                .lookup_path(gen.genv, rcx, &path)?
                .fold(rcx, gen, false);
        }

        // Infer subst
        let subst = self.infer_subst_for_bb_env(bb_env);

        // Check constraints
        for constr in &bb_env.constrs {
            gen.check_pred(rcx, subst.apply(constr));
        }

        let bb_env = bb_env
            .bindings
            .fmap(|binding| subst.apply(binding))
            .flatten();

        // Convert pointers to borrows
        for (path, binding2) in &bb_env {
            let binding1 = self.bindings.get(path);
            if let (Binding::Owned(ty1), Binding::Owned(ty2)) = (binding1, binding2) {
                match (ty1.kind(), ty2.kind()) {
                    (TyKind::Ptr(RefKind::Mut, ptr_path), TyKind::Ref(RefKind::Mut, bound)) => {
                        let ty = self.bindings.get(ptr_path).expect_owned();
                        gen.subtyping(rcx, &ty, bound);

                        self.bindings
                            .update_binding(ptr_path, Binding::Blocked(bound.clone()));
                        self.bindings
                            .update(path, Ty::mk_ref(RefKind::Mut, bound.clone()));
                    }
                    (TyKind::Ptr(RefKind::Shr, ptr_path), TyKind::Ref(RefKind::Shr, _)) => {
                        let ty = self.bindings.get(ptr_path).expect_owned();
                        self.bindings.block(ptr_path);
                        self.bindings.update(path, Ty::mk_ref(RefKind::Shr, ty));
                    }
                    _ => (),
                }
            }
        }

        // Check subtyping
        for (path, binding2) in bb_env {
            let binding1 = self.bindings.get(&path);
            let ty1 = binding1.ty();
            let ty2 = binding2.ty();
            gen.subtyping(rcx, ty1, ty2);
        }
        Ok(())
    }

    pub fn downcast(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
        variant_idx: VariantIdx,
    ) -> Result<(), OpaqueStructErr> {
        let mut down_place = place.clone();
        down_place.projection.push(PlaceElem::Downcast(variant_idx));
        self.lookup_place(rcx, gen, &down_place)?;
        Ok(())
    }
}

impl PathMap for TypeEnv {
    fn get(&self, path: &Path) -> Ty {
        self.bindings.get(path).expect_owned()
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.bindings.update(path, ty);
    }
}

impl<S> PathMap for std::collections::HashMap<Path, Ty, S>
where
    S: std::hash::BuildHasher,
{
    fn get(&self, path: &Path) -> Ty {
        self.get(path).unwrap().clone()
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.insert(path.clone(), ty);
    }
}

impl TypeEnvInfer {
    pub fn enter(&self) -> TypeEnv {
        TypeEnv { bindings: self.bindings.clone() }
    }

    fn new(
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        scope: Scope,
        mut env: TypeEnv,
    ) -> TypeEnvInfer {
        env.bindings.close_boxes(rcx, gen, &scope);
        let mut bindings = env.bindings;
        bindings.fmap_mut(|binding| {
            match binding {
                Binding::Owned(ty) => Binding::Owned(TypeEnvInfer::pack_ty(&scope, ty)),
                Binding::Blocked(ty) => Binding::Blocked(TypeEnvInfer::pack_ty(&scope, ty)),
            }
        });
        TypeEnvInfer { scope, bindings }
    }

    fn pack_ty(scope: &Scope, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, idxs) => {
                let bty = TypeEnvInfer::pack_bty(scope, bty);
                if scope.has_free_vars(idxs) {
                    let pred = Binders::new(Pred::Hole, bty.sorts());
                    Ty::exists(bty, pred)
                } else {
                    Ty::indexed(bty, idxs.clone())
                }
            }
            TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| TypeEnvInfer::pack_ty(scope, ty))
                    .collect_vec();
                Ty::tuple(tys)
            }
            // TODO(nilehmann) [`TyKind::Exists`] could also in theory contains free variables.
            TyKind::Exists(_, _)
            | TyKind::Never
            | TyKind::Discr(..)
            | TyKind::Ptr(..)
            | TyKind::Uninit
            | TyKind::Ref(..)
            | TyKind::Param(_)
            | TyKind::Constr(_, _)
            | TyKind::BoxPtr(_, _) => ty.clone(),
        }
    }

    fn pack_bty(scope: &Scope, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, substs) => {
                let substs = List::from_vec(
                    substs
                        .iter()
                        .map(|arg| Self::pack_generic_arg(scope, arg))
                        .collect(),
                );
                BaseTy::adt(adt_def.clone(), substs)
            }
            BaseTy::Array(ty, c) => BaseTy::Array(Self::pack_ty(scope, ty), c.clone()),
            BaseTy::Slice(ty) => BaseTy::Slice(Self::pack_ty(scope, ty)),
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::Char => bty.clone(),
        }
    }

    fn pack_generic_arg(scope: &Scope, arg: &GenericArg) -> GenericArg {
        match arg {
            GenericArg::Ty(ty) => GenericArg::Ty(Self::pack_ty(scope, ty)),
            GenericArg::Lifetime => GenericArg::Lifetime,
        }
    }

    /// join(self, genv, other) consumes the bindings in other, to "update"
    /// `self` in place, and returns `true` if there was an actual change
    /// or `false` indicating no change (i.e., a fixpoint was reached).
    pub fn join(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, mut other: TypeEnv) -> bool {
        other.bindings.close_boxes(rcx, gen, &self.scope);

        // Unfold
        self.bindings.join_with(rcx, gen, &mut other.bindings);

        let paths = self.bindings.paths();

        // Convert pointers to borrows
        for path in &paths {
            let binding1 = self.bindings.get(path);
            let binding2 = other.bindings.get(path);
            if let (Binding::Owned(ty1), Binding::Owned(ty2)) = (binding1, binding2) {
                match (ty1.kind(), ty2.kind()) {
                    (TyKind::Ptr(RefKind::Shr, path1), TyKind::Ptr(RefKind::Shr, path2))
                        if path1 != path2 =>
                    {
                        let ty1 = self.bindings.get(path1).expect_owned();
                        let ty2 = other.bindings.get(path2).expect_owned();

                        self.bindings.block(path1);
                        other.bindings.block(path2);

                        self.bindings.update(path, Ty::mk_ref(RefKind::Shr, ty1));
                        other.bindings.update(path, Ty::mk_ref(RefKind::Shr, ty2));
                    }
                    (TyKind::Ptr(RefKind::Shr, ptr_path), TyKind::Ref(RefKind::Shr, _)) => {
                        let ty = self.bindings.get(ptr_path).expect_owned();
                        self.bindings.block(ptr_path);
                        self.bindings.update(path, Ty::mk_ref(RefKind::Shr, ty));
                    }
                    (TyKind::Ref(RefKind::Shr, _), TyKind::Ptr(RefKind::Shr, ptr_path)) => {
                        let ty = other.bindings.get(ptr_path).expect_owned();
                        other.bindings.block(ptr_path);
                        other.bindings.update(path, Ty::mk_ref(RefKind::Shr, ty));
                    }
                    (TyKind::Ptr(RefKind::Mut, path1), TyKind::Ptr(RefKind::Mut, path2))
                        if path1 != path2 =>
                    {
                        let ty1 = self.bindings.get(path1).expect_owned().with_holes();
                        let ty2 = other.bindings.get(path2).expect_owned().with_holes();

                        self.bindings
                            .update(path, Ty::mk_ref(RefKind::Mut, ty1.clone()));
                        other
                            .bindings
                            .update(path, Ty::mk_ref(RefKind::Mut, ty2.clone()));

                        self.bindings.update_binding(path1, Binding::Blocked(ty1));
                        other.bindings.update_binding(path2, Binding::Blocked(ty2));
                    }
                    (TyKind::Ptr(RefKind::Mut, ptr_path), TyKind::Ref(RefKind::Mut, bound)) => {
                        let bound = bound.with_holes();
                        self.bindings
                            .update_binding(ptr_path, Binding::Blocked(bound.clone()));
                        self.bindings.update(path, Ty::mk_ref(RefKind::Mut, bound));
                    }
                    (TyKind::Ref(RefKind::Mut, bound), TyKind::Ptr(RefKind::Mut, ptr_path)) => {
                        let bound = bound.with_holes();
                        other
                            .bindings
                            .update_binding(ptr_path, Binding::Blocked(bound.clone()));
                        other.bindings.update(path, Ty::mk_ref(RefKind::Mut, bound));
                    }
                    _ => {}
                }
            }
        }

        // Join types
        let mut modified = false;
        for path in &paths {
            let binding1 = self.bindings.get(path);
            let binding2 = other.bindings.get(path);
            let binding = match (&binding1, &binding2) {
                (Binding::Owned(ty1), Binding::Owned(ty2)) => {
                    Binding::Owned(self.join_ty(ty1, ty2))
                }
                (Binding::Owned(ty1), Binding::Blocked(ty2))
                | (Binding::Blocked(ty1), Binding::Owned(ty2))
                | (Binding::Blocked(ty1), Binding::Blocked(ty2)) => {
                    Binding::Blocked(self.join_ty(ty1, ty2))
                }
            };
            modified |= binding1 != binding;
            self.bindings.update_binding(path, binding);
        }

        modified
    }

    fn join_ty(&self, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Uninit, _) | (_, TyKind::Uninit) => Ty::uninit(),
            (TyKind::Ptr(rk1, path1), TyKind::Ptr(rk2, path2)) => {
                debug_assert_eq!(rk1, rk2);
                debug_assert_eq!(path1, path2);
                Ty::ptr(*rk1, path1.clone())
            }
            (TyKind::BoxPtr(loc1, alloc1), TyKind::BoxPtr(loc2, alloc2)) => {
                debug_assert_eq!(loc1, loc2);
                debug_assert_eq!(alloc1, alloc2);
                Ty::box_ptr(*loc1, alloc1.clone())
            }
            (TyKind::Indexed(bty1, idxs1), TyKind::Indexed(bty2, idxs2)) => {
                let bty = self.join_bty(bty1, bty2);
                if self.scope.has_free_vars(idxs2) || !Index::exprs_eq(idxs1, idxs2) {
                    let pred = Binders::new(Pred::Hole, bty.sorts());
                    Ty::exists(bty, pred)
                } else {
                    Ty::indexed(bty, idxs1.clone())
                }
            }
            (TyKind::Exists(bty1, _), TyKind::Indexed(bty2, ..) | TyKind::Exists(bty2, ..))
            | (TyKind::Indexed(bty1, _), TyKind::Exists(bty2, ..)) => {
                let bty = self.join_bty(bty1, bty2);
                let pred = Binders::new(Pred::Hole, bty.sorts());
                Ty::exists(bty, pred)
            }
            (TyKind::Ref(rk1, ty1), TyKind::Ref(rk2, ty2)) => {
                debug_assert_eq!(rk1, rk2);
                Ty::mk_ref(*rk1, self.join_ty(ty1, ty2))
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
                Ty::param(*param_ty1)
            }
            (TyKind::Tuple(tys1), TyKind::Tuple(tys2)) => {
                assert!(
                    tys1.is_empty() && tys2.is_empty(),
                    "join of non-empty tuples is not supported yet"
                );
                Ty::tuple(vec![])
            }
            _ => unreachable!("`{ty1:?}` -- `{ty2:?}`"),
        }
    }

    fn join_bty(&self, bty1: &BaseTy, bty2: &BaseTy) -> BaseTy {
        if let (BaseTy::Adt(def1, substs1), BaseTy::Adt(def2, substs2)) = (bty1, bty2) {
            debug_assert_eq!(def1.def_id(), def2.def_id());
            let substs = iter::zip(substs1, substs2)
                .map(|(arg1, arg2)| self.join_generic_arg(arg1, arg2))
                .collect();
            BaseTy::adt(def1.clone(), List::from_vec(substs))
        } else {
            debug_assert_eq!(bty1, bty2);
            bty1.clone()
        }
    }

    fn join_generic_arg(&self, arg1: &GenericArg, arg2: &GenericArg) -> GenericArg {
        match (arg1, arg2) {
            (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => GenericArg::Ty(self.join_ty(ty1, ty2)),
            (GenericArg::Lifetime, GenericArg::Lifetime) => GenericArg::Lifetime,
            _ => panic!("incompatible generic args: `{arg1:?}` `{arg2:?}`"),
        }
    }

    pub fn into_bb_env(self, kvar_gen: &mut impl KVarGen) -> BasicBlockEnv {
        let mut bindings = self.bindings;

        let mut names = vec![];
        let mut sorts = vec![];
        let mut preds = vec![];
        let name_gen = self.scope.name_gen();
        bindings.fmap_mut(|binding| {
            match binding {
                Binding::Owned(ty) => {
                    Binding::Owned(generalize(&name_gen, ty, &mut names, &mut sorts, &mut preds))
                }
                Binding::Blocked(ty) => Binding::Blocked(ty.clone()),
            }
        });

        // Replace all holes with a single fresh kvar on all parameters
        let mut constrs = preds
            .into_iter()
            .filter(|pred| !matches!(pred, Pred::Hole))
            .collect_vec();
        let exprs = names.iter().map(|name| Expr::fvar(*name)).collect_vec();
        let kvar = kvar_gen
            .fresh(&sorts, self.scope.iter())
            .replace_bound_vars(&exprs);
        constrs.push(kvar);

        let params = iter::zip(names, sorts).collect_vec();

        // Replace holes that weren't generalized by fresh kvars
        let mut kvar_gen = kvar_gen.chaining(&self.scope);
        let fresh_kvar = &mut |sorts: &[Sort]| kvar_gen.fresh(sorts, params.iter().cloned());
        bindings.fmap_mut(|binding| binding.replace_holes(fresh_kvar));

        BasicBlockEnv { params, constrs, bindings, scope: self.scope }
    }
}

/// This is effectively doing the same as [`RefineCtxt::unpack`] but for moving existentials
/// to the top level in a [`BasicBlockEnv`]. Maybe we should find a way to abstract over it.
fn generalize(
    name_gen: &IndexGen<Name>,
    ty: &Ty,
    names: &mut Vec<Name>,
    sorts: &mut Vec<Sort>,
    preds: &mut Vec<Pred>,
) -> Ty {
    match ty.kind() {
        TyKind::Indexed(bty, idxs) => {
            let bty = generalize_bty(name_gen, bty, names, sorts, preds);
            Ty::indexed(bty, idxs.clone())
        }
        TyKind::Exists(bty, pred) => {
            let bty = generalize_bty(name_gen, bty, names, sorts, preds);

            let mut idxs = vec![];
            let pred = pred.replace_bvars_with_fresh_fvars(|sort| {
                let fresh = name_gen.fresh();
                names.push(fresh);
                sorts.push(sort.clone());
                idxs.push(Expr::fvar(fresh).into());
                fresh
            });
            preds.push(pred);

            Ty::indexed(bty, idxs)
        }
        TyKind::Ref(RefKind::Shr, ty) => {
            let ty = generalize(name_gen, ty, names, sorts, preds);
            Ty::mk_ref(RefKind::Shr, ty)
        }
        _ => ty.clone(),
    }
}

fn generalize_bty(
    name_gen: &IndexGen<Name>,
    bty: &BaseTy,
    names: &mut Vec<Name>,
    sorts: &mut Vec<Sort>,
    preds: &mut Vec<Pred>,
) -> BaseTy {
    match bty {
        BaseTy::Adt(adt_def, substs) if adt_def.is_box() => {
            let (boxed, alloc) = box_args(substs);
            let boxed = generalize(name_gen, boxed, names, sorts, preds);
            BaseTy::adt(adt_def.clone(), vec![GenericArg::Ty(boxed), GenericArg::Ty(alloc.clone())])
        }
        _ => bty.clone(),
    }
}

impl BasicBlockEnv {
    pub fn enter(&self, rcx: &mut RefineCtxt) -> TypeEnv {
        let mut subst = FVarSubst::empty();
        for (name, sort) in &self.params {
            let fresh = rcx.define_var(sort);
            subst.insert(*name, Expr::fvar(fresh));
        }
        for constr in &self.constrs {
            rcx.assume_pred(subst.apply(constr));
        }
        let bindings = self.bindings.fmap(|binding| subst.apply(binding));
        TypeEnv { bindings }
    }

    pub fn scope(&self) -> &Scope {
        &self.scope
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;
    use itertools::Itertools;

    use super::*;

    impl Pretty for TypeEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
        }
    }

    impl Pretty for TypeEnvInfer {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} {:?}", &self.scope, &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
        }
    }

    impl Pretty for BasicBlockEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} ", &self.scope)?;

            if !self.params.is_empty() {
                w!(
                    "∃ {}. ",
                    ^self.params
                        .iter()
                        .format_with(", ", |(name, sort), f| {
                            f(&format_args_cx!("{:?}: {:?}", ^name, ^sort))
                        })
                )?;
            }
            if !self.constrs.is_empty() {
                w!(
                    "{:?} ⇒ ",
                    join!(", ", self.constrs.iter().filter(|pred| !pred.is_trivially_true()))
                )?;
            }
            w!("{:?}", &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(KVarArgs::Hide)
        }
    }

    impl_debug_with_default_cx!(TypeEnv => "type_env", TypeEnvInfer => "type_env_infer", BasicBlockEnv => "basic_block_env");
}
