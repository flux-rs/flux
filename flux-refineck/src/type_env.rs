pub mod paths_tree;

use std::iter;

use flux_common::{index::IndexGen, tracked_span_bug};
use flux_middle::{
    fhir::WeakKind,
    global_env::{GlobalEnv, OpaqueStructErr},
    intern::List,
    rty::{
        box_args, evars::EVarSol, fold::TypeFoldable, subst::FVarSubst, BaseTy, Binder, Expr,
        ExprKind, GenericArg, Path, PtrKind, Ref, RefKind, Ty, TyKind, INNERMOST,
    },
    rustc::mir::{BasicBlock, Local, Place, PlaceElem},
};
use itertools::{izip, Itertools};
use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;

use self::paths_tree::{Binding, FoldResult, LocKind, PathsTree};
use super::rty::{Loc, Name, Sort};
use crate::{
    constraint_gen::{ConstrGen, ConstrReason},
    fixpoint::{KVarEncoding, KVarStore},
    param_infer,
    refine_tree::{RefineCtxt, Scope},
    rty::VariantIdx,
};

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
    constrs: Vec<Expr>,
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
            .lookup(gen.genv, rcx, place)?
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
            .lookup(gen.genv, rcx, path)?
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
            .lookup(gen.genv, rcx, place)?
            .fold(rcx, gen, true)
        {
            FoldResult::Strg(path, _) => Ty::ptr(rk, path),
            FoldResult::Weak(result_rk, ty) => {
                debug_assert!(WeakKind::from(rk) <= result_rk);
                Ty::mk_ref(rk, ty)
            }
            FoldResult::Raw(ty) => Ty::mk_ref(rk, ty), // TODO(RJ): is this legit?
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
            .lookup(gen.genv, rcx, place)?
            .fold(rcx, gen, true)
        {
            FoldResult::Strg(path, _) => {
                self.bindings.update(&path, new_ty);
            }
            FoldResult::Weak(WeakKind::Mut | WeakKind::Arr, ty) => {
                gen.subtyping(rcx, &new_ty, &ty, ConstrReason::Assign);
            }
            FoldResult::Weak(WeakKind::Shr, _) => {
                tracked_span_bug!("cannot assign to `{place:?}`, which is behind a `&` reference");
            }
            FoldResult::Raw(_) => { /* ignore write through Raw */ }
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
            .lookup(gen.genv, rcx, place)?
            .fold(rcx, gen, true)
        {
            FoldResult::Strg(path, ty) => {
                self.bindings.update(&path, Ty::uninit());
                Ok(ty)
            }
            FoldResult::Weak(WeakKind::Mut, _) => {
                tracked_span_bug!(
                    "cannot move out of `{place:?}`, which is behind a `&mut` reference"
                )
            }
            FoldResult::Weak(WeakKind::Arr, _) | FoldResult::Weak(WeakKind::Shr, _) => {
                tracked_span_bug!("cannot move out of `{place:?}`, which is behind a `&` reference")
            }
            FoldResult::Raw(_) => {
                tracked_span_bug!("cannot move out of a raw pointer")
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

    pub fn block_with(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        path: &Path,
        updated: Ty,
    ) -> Ty {
        self.bindings
            .lookup(gen.genv, rcx, path)
            .unwrap_or_else(|err| tracked_span_bug!("{:?}", err))
            .block_with(rcx, gen, updated)
    }

    pub fn block(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, path: &Path) -> Ty {
        self.bindings
            .lookup(gen.genv, rcx, path)
            .unwrap_or_else(|err| tracked_span_bug!("{:?}", err))
            .block(rcx, gen)
    }

    fn infer_subst_for_bb_env(&self, bb_env: &BasicBlockEnv) -> FVarSubst {
        let params = bb_env.params.iter().map(|(name, _)| *name).collect();
        let mut subst = FVarSubst::empty();
        self.bindings.iter(|_, path, binding1| {
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
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                self.infer_subst_for_bb_env_bty(bb_env, params, bty1, bty2, subst);
                subst.infer_from_idxs(params, idx1, idx2);
            }
            (TyKind::Ptr(pk1, path1), TyKind::Ptr(pk2, path2)) => {
                debug_assert_eq!(pk1, pk2);
                debug_assert_eq!(path1, path2);
            }
            (TyKind::Ptr(pk1, path), Ref!(rk2, ty2)) => {
                debug_assert_eq!(pk1, &PtrKind::from(*rk2));
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
        match (bty1, bty2) {
            (BaseTy::Ref(rk1, ty1), BaseTy::Ref(rk2, ty2)) => {
                debug_assert_eq!(rk1, rk2);
                self.infer_subst_for_bb_env_ty(bb_env, params, ty1, ty2, subst);
            }
            (BaseTy::Adt(adt, substs1), BaseTy::Adt(_, substs2)) if adt.is_box() => {
                for (arg1, arg2) in iter::zip(substs1, substs2) {
                    self.infer_subst_for_bb_env_generic_arg(bb_env, params, arg1, arg2, subst);
                }
            }
            _ => {}
        }
    }

    pub fn check_goto(
        mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        bb_env: &BasicBlockEnv,
        target: BasicBlock,
    ) -> Result<(), OpaqueStructErr> {
        self.bindings.close_boxes(rcx, gen, &bb_env.scope);

        let reason = ConstrReason::Goto(target);

        // Look up paths to make sure they are properly folded/unfolded
        for path in bb_env.bindings.paths() {
            self.bindings
                .lookup(gen.genv, rcx, &path)?
                .fold(rcx, gen, false);
        }

        // Infer subst
        let subst = self.infer_subst_for_bb_env(bb_env);

        // Check constraints
        for constr in &bb_env.constrs {
            gen.check_pred(rcx, subst.apply(constr), reason);
        }

        let bb_env = bb_env
            .bindings
            .fmap(|binding| subst.apply(binding))
            .flatten();

        // Convert pointers to borrows
        for (_, path, binding2) in &bb_env {
            let binding1 = self.bindings.get(path);
            if let (Binding::Owned(ty1), Binding::Owned(ty2)) = (binding1, binding2) {
                match (ty1.kind(), ty2.kind()) {
                    (TyKind::Ptr(PtrKind::Mut, ptr_path), Ref!(RefKind::Mut, bound)) => {
                        let ty = self
                            .bindings
                            .lookup(gen.genv, rcx, ptr_path)?
                            .block(rcx, gen);
                        gen.subtyping(rcx, &ty, bound, reason);

                        self.bindings
                            .update(path, Ty::mk_ref(RefKind::Mut, bound.clone()));
                    }
                    (TyKind::Ptr(PtrKind::Shr, ptr_path), Ref!(RefKind::Shr, _)) => {
                        let ty = self
                            .bindings
                            .lookup(gen.genv, rcx, ptr_path)?
                            .block(rcx, gen);
                        self.bindings.update(path, Ty::mk_ref(RefKind::Shr, ty));
                    }
                    _ => (),
                }
            }
        }

        // Check subtyping
        for (_, path, binding2) in bb_env {
            let binding1 = self.bindings.get(&path);
            let ty1 = binding1.ty();
            let ty2 = binding2.ty();
            gen.subtyping(rcx, ty1, ty2, reason);
        }
        Ok(())
    }

    pub fn downcast(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        place: &Place,
        variant_idx: VariantIdx,
    ) -> Result<(), OpaqueStructErr> {
        let mut down_place = place.clone();
        down_place.projection.push(PlaceElem::Downcast(variant_idx));
        self.bindings.lookup(genv, rcx, &down_place)?;
        Ok(())
    }

    pub fn replace_evars(&mut self, evars: &EVarSol) {
        self.bindings
            .fmap_mut(|binding| binding.replace_evars(evars));
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.bindings.update(path, ty);
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
                    Ty::exists_with_constr(bty, Expr::hole())
                } else {
                    Ty::indexed(bty, idxs.clone())
                }
            }
            // FIXME(nilehmann) [`TyKind::Exists`] could also contain free variables.
            TyKind::Exists(_)
            | TyKind::Discr(..)
            | TyKind::Ptr(..)
            | TyKind::Uninit
            | TyKind::Param(_)
            | TyKind::Constr(_, _) => ty.clone(),
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
            BaseTy::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| TypeEnvInfer::pack_ty(scope, ty))
                    .collect();
                BaseTy::Tuple(tys)
            }
            BaseTy::Slice(ty) => BaseTy::Slice(Self::pack_ty(scope, ty)),
            BaseTy::Ref(rk, ty) => BaseTy::Ref(*rk, Self::pack_ty(scope, ty)),
            BaseTy::Array(ty, c) => BaseTy::Array(Self::pack_ty(scope, ty), c.clone()),
            BaseTy::Int(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::RawPtr(_, _)
            | BaseTy::Char
            | BaseTy::Never => bty.clone(),
        }
    }

    fn pack_generic_arg(scope: &Scope, arg: &GenericArg) -> GenericArg {
        match arg {
            GenericArg::Ty(ty) => GenericArg::Ty(Self::pack_ty(scope, ty)),
            GenericArg::Lifetime => GenericArg::Lifetime,
        }
    }

    fn block(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, path: &Path) -> Ty {
        self.bindings
            .lookup(gen.genv, rcx, path)
            .unwrap_or_else(|err| tracked_span_bug!("{err:?}"))
            .block(rcx, gen)
    }

    pub fn block_with(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        path: &Path,
        updated: Ty,
    ) -> Ty {
        self.bindings
            .lookup(gen.genv, rcx, path)
            .unwrap_or_else(|err| tracked_span_bug!("{:?}", err))
            .block_with(rcx, gen, updated)
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.bindings.update(path, ty);
    }

    /// join(self, genv, other) consumes the bindings in other, to "update"
    /// `self` in place, and returns `true` if there was an actual change
    /// or `false` indicating no change (i.e., a fixpoint was reached).
    pub(crate) fn join(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        mut other: TypeEnv,
    ) -> bool {
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
                    (TyKind::Ptr(PtrKind::Shr, path1), TyKind::Ptr(PtrKind::Shr, path2))
                        if path1 != path2 =>
                    {
                        let ty1 = self.block(rcx, gen, path1);
                        let ty2 = self.block(rcx, gen, path2);

                        self.update(path, Ty::mk_ref(RefKind::Shr, ty1));
                        other.update(path, Ty::mk_ref(RefKind::Shr, ty2));
                    }
                    (TyKind::Ptr(PtrKind::Shr, ptr_path), Ref!(RefKind::Shr, _)) => {
                        let ty = self.block(rcx, gen, ptr_path);
                        self.bindings.update(path, Ty::mk_ref(RefKind::Shr, ty));
                    }
                    (Ref!(RefKind::Shr, _), TyKind::Ptr(PtrKind::Shr, ptr_path)) => {
                        let ty = other.block(rcx, gen, ptr_path);
                        other.update(path, Ty::mk_ref(RefKind::Shr, ty));
                    }
                    (TyKind::Ptr(PtrKind::Mut, path1), TyKind::Ptr(PtrKind::Mut, path2))
                        if path1 != path2 =>
                    {
                        let ty1 = self.bindings.get(path1).expect_owned().with_holes();
                        let ty2 = other.bindings.get(path2).expect_owned().with_holes();

                        self.bindings
                            .update(path, Ty::mk_ref(RefKind::Mut, ty1.clone()));
                        other.update(path, Ty::mk_ref(RefKind::Mut, ty2.clone()));

                        self.block_with(rcx, gen, path1, ty1);
                        other.block_with(rcx, gen, path2, ty2);
                    }
                    (TyKind::Ptr(PtrKind::Mut, ptr_path), Ref!(RefKind::Mut, bound)) => {
                        let bound = bound.with_holes();
                        self.block_with(rcx, gen, ptr_path, bound.clone());
                        self.update(path, Ty::mk_ref(RefKind::Mut, bound));
                    }
                    (Ref!(RefKind::Mut, bound), TyKind::Ptr(PtrKind::Mut, ptr_path)) => {
                        let bound = bound.with_holes();
                        other.block_with(rcx, gen, ptr_path, bound.clone());
                        other.update(path, Ty::mk_ref(RefKind::Mut, bound));
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
            (TyKind::Exists(ty1), _) => self.join_ty(ty1.as_ref().skip_binders(), ty2),
            (_, TyKind::Exists(ty2)) => self.join_ty(ty1, ty2.as_ref().skip_binders()),
            (TyKind::Constr(_, ty1), _) => self.join_ty(ty1, ty2),
            (_, TyKind::Constr(_, ty2)) => self.join_ty(ty1, ty2),
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                let bty = self.join_bty(bty1, bty2);
                let mut sorts = vec![];
                let idx = self.join_idx(&idx1.expr, &idx2.expr, &bty.sort(), &mut sorts);
                let sort = Sort::tuple(sorts);
                if sort.is_unit() {
                    Ty::indexed(bty, idx)
                } else {
                    let ty = Ty::constr(Expr::hole(), Ty::indexed(bty, idx));
                    Ty::exists(Binder::new(ty, sort))
                }
            }
            (TyKind::Ptr(rk1, path1), TyKind::Ptr(rk2, path2)) => {
                debug_assert_eq!(rk1, rk2);
                debug_assert_eq!(path1, path2);
                Ty::ptr(*rk1, path1.clone())
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
                Ty::param(*param_ty1)
            }
            _ => tracked_span_bug!("unexpected types: `{ty1:?}` - `{ty2:?}`"),
        }
    }

    fn join_idx(&self, e1: &Expr, e2: &Expr, sort: &Sort, bound_sorts: &mut Vec<Sort>) -> Expr {
        match (e1.kind(), e2.kind(), sort) {
            (ExprKind::Tuple(es1), ExprKind::Tuple(es2), Sort::Tuple(sorts)) => {
                debug_assert_eq!(es1.len(), es2.len());
                debug_assert_eq!(es1.len(), sorts.len());
                Expr::tuple(
                    izip!(es1, es2, sorts)
                        .map(|(e1, e2, sort)| self.join_idx(e1, e2, sort, bound_sorts))
                        .collect_vec(),
                )
            }
            _ => {
                let has_free_vars2 = self.scope.has_free_vars(e2);
                let has_escaping_vars1 = e1.has_escaping_bvars();
                let has_escaping_vars2 = e2.has_escaping_bvars();
                if !has_free_vars2 && !has_escaping_vars1 && !has_escaping_vars2 && e1 == e2 {
                    e1.clone()
                } else {
                    bound_sorts.push(sort.clone());
                    Expr::tuple_proj(Expr::bvar(INNERMOST), (bound_sorts.len() - 1) as u32)
                }
            }
        }
    }

    fn join_bty(&self, bty1: &BaseTy, bty2: &BaseTy) -> BaseTy {
        match (bty1, bty2) {
            (BaseTy::Adt(def1, substs1), BaseTy::Adt(def2, substs2)) => {
                debug_assert_eq!(def1.def_id(), def2.def_id());
                let substs = iter::zip(substs1, substs2)
                    .map(|(arg1, arg2)| self.join_generic_arg(arg1, arg2))
                    .collect();
                BaseTy::adt(def1.clone(), List::from_vec(substs))
            }
            (BaseTy::Tuple(tys1), BaseTy::Tuple(tys2)) => {
                let tys = iter::zip(tys1, tys2)
                    .map(|(ty1, ty2)| self.join_ty(ty1, ty2))
                    .collect();
                BaseTy::Tuple(tys)
            }
            (BaseTy::Ref(rk1, ty1), BaseTy::Ref(rk2, ty2)) => {
                debug_assert_eq!(rk1, rk2);
                BaseTy::Ref(*rk1, self.join_ty(ty1, ty2))
            }
            (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
                debug_assert_eq!(len1, len2);
                BaseTy::Array(self.join_ty(ty1, ty2), len1.clone())
            }
            _ => {
                debug_assert_eq!(bty1, bty2);
                bty1.clone()
            }
        }
    }

    fn join_generic_arg(&self, arg1: &GenericArg, arg2: &GenericArg) -> GenericArg {
        match (arg1, arg2) {
            (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => GenericArg::Ty(self.join_ty(ty1, ty2)),
            (GenericArg::Lifetime, GenericArg::Lifetime) => GenericArg::Lifetime,
            _ => tracked_span_bug!("unexpected generic args: `{arg1:?}` - `{arg2:?}`"),
        }
    }

    pub fn into_bb_env(self, kvar_store: &mut KVarStore) -> BasicBlockEnv {
        let mut bindings = self.bindings;

        let mut generalizer = Generalizer::new(self.scope.name_gen());
        bindings.fmap_mut(|binding| {
            match binding {
                Binding::Owned(ty) => Binding::Owned(generalizer.generalize_ty(ty)),
                Binding::Blocked(ty) => Binding::Blocked(ty.clone()),
            }
        });
        let (names, sorts, preds) = generalizer.into_parts();
        // Replace all holes with a single fresh kvar on all parameters
        let mut constrs = preds
            .into_iter()
            .filter(|pred| !matches!(pred.kind(), ExprKind::Hole))
            .collect_vec();
        let exprs = names.iter().map(|name| Expr::fvar(*name)).collect_vec();
        let kvar = kvar_store
            .fresh(Sort::tuple(&sorts[..]), self.scope.iter(), KVarEncoding::Conj)
            .replace_bvars(&Expr::tuple(exprs));
        constrs.push(kvar);

        let params = iter::zip(names, sorts).collect_vec();

        // Replace holes that weren't generalized by fresh kvars
        let kvar_gen = &mut |sort| {
            kvar_store.fresh(
                sort,
                self.scope.iter().chain(params.iter().cloned()),
                KVarEncoding::Conj,
            )
        };
        bindings.fmap_mut(|binding| binding.replace_holes(kvar_gen));

        BasicBlockEnv { params, constrs, bindings, scope: self.scope }
    }
}

struct Generalizer {
    name_gen: IndexGen<Name>,
    names: Vec<Name>,
    sorts: Vec<Sort>,
    preds: Vec<Expr>,
}

impl Generalizer {
    fn new(name_gen: IndexGen<Name>) -> Self {
        Self { name_gen, names: vec![], sorts: vec![], preds: vec![] }
    }

    fn into_parts(self) -> (Vec<Name>, Vec<Sort>, Vec<Expr>) {
        (self.names, self.sorts, self.preds)
    }

    /// This is effectively doing the same as [`RefineCtxt::unpack`] but for moving existentials
    /// to the top level in a [`BasicBlockEnv`]. Maybe we should find a way to abstract over it.
    fn generalize_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, idxs) => {
                let bty = self.generalize_bty(bty);
                Ty::indexed(bty, idxs.clone())
            }
            TyKind::Exists(ty) => {
                let ty = ty.replace_bvars_with(|sort| self.fresh_vars(sort));
                self.generalize_ty(&ty)
            }
            TyKind::Constr(pred, ty) => {
                self.preds.push(pred.clone());
                ty.clone()
            }
            _ => ty.clone(),
        }
    }

    fn generalize_bty(&mut self, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, substs) if adt_def.is_box() => {
                let (boxed, alloc) = box_args(substs);
                let boxed = self.generalize_ty(boxed);
                BaseTy::adt(
                    adt_def.clone(),
                    vec![GenericArg::Ty(boxed), GenericArg::Ty(alloc.clone())],
                )
            }
            BaseTy::Ref(RefKind::Shr, ty) => {
                let ty = self.generalize_ty(ty);
                BaseTy::Ref(RefKind::Shr, ty)
            }
            _ => bty.clone(),
        }
    }

    fn fresh_vars(&mut self, sort: &Sort) -> Expr {
        Expr::fold_sort(sort, |sort| Expr::fvar(self.fresh_var(sort)))
    }

    fn fresh_var(&mut self, sort: &Sort) -> Name {
        let fresh = self.name_gen.fresh();
        self.names.push(fresh);
        self.sorts.push(sort.clone());
        fresh
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
