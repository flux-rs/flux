mod projection;

use std::iter;

use flux_common::{index::IndexGen, tracked_span_bug};
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        box_args,
        evars::EVarSol,
        fold::{TypeFoldable, TypeVisitable},
        subst::{FVarSubst, RegionSubst},
        BaseTy, Binder, Expr, ExprKind, GenericArg, Mutability, Path, PtrKind, Ref, Region, Ty,
        TyKind, Var, INNERMOST,
    },
    rustc::mir::{BasicBlock, Local, LocalDecls, Place, PlaceElem},
};
use itertools::{izip, Itertools};
use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;

use self::projection::{LocKind, PlacesTree};
use super::rty::{Loc, Name, Sort};
use crate::{
    checker::errors::CheckerErrKind,
    constraint_gen::{ConstrGen, ConstrReason},
    fixpoint_encoding::{KVarEncoding, KVarStore},
    param_infer,
    refine_tree::{RefineCtxt, Scope},
    rty::VariantIdx,
    CheckerConfig,
};

#[derive(Clone, Default)]
pub struct TypeEnv<'a> {
    bindings: PlacesTree,
    local_decls: &'a LocalDecls,
}

pub struct BasicBlockEnvShape {
    scope: Scope,
    bindings: PlacesTree,
}

pub struct BasicBlockEnv {
    params: Vec<(Name, Sort)>,
    constrs: Vec<Expr>,
    scope: Scope,
    bindings: PlacesTree,
}

impl TypeEnv<'_> {
    pub fn new(local_decls: &LocalDecls) -> TypeEnv {
        TypeEnv { bindings: PlacesTree::default(), local_decls }
    }

    pub fn alloc_universal_loc(&mut self, loc: Loc, ty: Ty) {
        self.bindings.insert(loc, LocKind::Universal, ty);
    }

    pub fn alloc_with_ty(&mut self, local: Local, ty: Ty) {
        let ty = RegionSubst::new(&ty, &self.local_decls[local].ty).apply(&ty);
        self.bindings.insert(local.into(), LocKind::Local, ty);
    }

    pub fn alloc(&mut self, local: Local) {
        self.bindings
            .insert(local.into(), LocKind::Local, Ty::uninit());
    }

    pub(crate) fn into_infer(self, scope: Scope) -> Result<BasicBlockEnvShape, CheckerErrKind> {
        BasicBlockEnvShape::new(scope, self)
    }

    pub(crate) fn lookup_place(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        place: &Place,
    ) -> Result<Ty, CheckerErrKind> {
        Ok(self.bindings.lookup_unfolding(genv, rcx, place)?.ty)
    }

    pub(crate) fn get(&mut self, path: &Path) -> Ty {
        self.bindings.get(path)
    }

    pub fn update_path(&mut self, path: &Path, new_ty: Ty) {
        self.bindings.lookup(path).update(new_ty);
    }

    /// When checking a borrow in the right hand side of an assignment `x = &'?n p`, we use the
    /// annotated region `'?n` in the type of the result. This region will only be used temporarily
    /// and then replaced by the region in the type of the `x` after the assignment.
    pub(crate) fn borrow(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        re: Region,
        mutbl: Mutability,
        place: &Place,
    ) -> Result<Ty, CheckerErrKind> {
        let result = self.bindings.lookup_unfolding(genv, rcx, place)?;
        if result.is_strg && mutbl == Mutability::Mut {
            Ok(Ty::ptr(PtrKind::from_ref(re, mutbl), result.path()))
        } else {
            Ok(Ty::mk_ref(re, result.ty, mutbl))
        }
    }

    pub(crate) fn assign(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
        new_ty: Ty,
    ) -> Result<(), CheckerErrKind> {
        let rustc_ty = place.ty(gen.genv, self.local_decls)?.ty;
        let new_ty = RegionSubst::new(&new_ty, &rustc_ty).apply(&new_ty);
        let result = self.bindings.lookup_unfolding(gen.genv, rcx, place)?;

        if result.is_strg {
            result.update(new_ty);
        } else if !place.behind_raw_ptr(gen.genv, self.local_decls)? {
            gen.subtyping(rcx, &new_ty, &result.ty, ConstrReason::Assign);
        }
        Ok(())
    }

    pub(crate) fn move_place(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        place: &Place,
    ) -> Result<Ty, CheckerErrKind> {
        let result = self.bindings.lookup_unfolding(genv, rcx, place)?;
        if result.is_strg {
            let uninit = Ty::uninit();
            Ok(result.update(uninit))
        } else {
            tracked_span_bug!("cannot move out of {place:?}");
        }
    }

    pub(crate) fn unpack(&mut self, rcx: &mut RefineCtxt) {
        self.bindings.fmap_mut(|ty| rcx.unpack(ty));
    }

    pub(crate) fn unblock(&mut self, rcx: &mut RefineCtxt, place: &Place) {
        self.bindings.lookup(place).unblock(rcx);
    }

    pub(crate) fn block_with(&mut self, path: &Path, new_ty: Ty) -> Ty {
        self.bindings.lookup(path).block_with(new_ty)
    }

    pub(crate) fn block(&mut self, path: &Path) -> Ty {
        self.bindings.lookup(path).block()
    }

    fn infer_subst_for_bb_env(&self, bb_env: &BasicBlockEnv) -> FVarSubst {
        let params = bb_env.params.iter().map(|(name, _)| *name).collect();
        let mut subst = FVarSubst::empty();
        for (loc, binding1) in self.bindings.iter() {
            let binding2 = bb_env.bindings.get_loc(loc);
            self.infer_subst_for_bb_env_ty(bb_env, &params, &binding1.ty, &binding2.ty, &mut subst);
        }

        param_infer::check_inference(&subst, bb_env.params.iter().map(|(name, _)| *name)).unwrap();
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
            (TyKind::Ptr(pk1, path), Ref!(r2, ty2, mutbl2)) => {
                debug_assert_eq!(pk1, &PtrKind::from_ref(*r2, *mutbl2));
                let ty1 = self.bindings.get(path);
                self.infer_subst_for_bb_env_ty(bb_env, params, &ty1, ty2, subst);
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
            (BaseTy::Ref(r1, ty1, mutbl1), BaseTy::Ref(r2, ty2, mutbl2)) => {
                debug_assert_eq!(mutbl1, mutbl2);
                debug_assert_eq!(r1, r2);
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

    pub(crate) fn check_goto(
        mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        bb_env: &BasicBlockEnv,
        target: BasicBlock,
    ) -> Result<(), CheckerErrKind> {
        let reason = ConstrReason::Goto(target);

        // Infer subst
        let subst = self.infer_subst_for_bb_env(bb_env);

        // Check constraints
        for constr in &bb_env.constrs {
            gen.check_pred(rcx, subst.apply(constr), reason);
        }

        let bb_env = bb_env.bindings.fmap(|ty| subst.apply(ty)).flatten();

        // Convert pointers to borrows
        for (path, _, ty2) in &bb_env {
            let ty1 = self.bindings.get(path);
            match (ty1.kind(), ty2.kind()) {
                (TyKind::Ptr(PtrKind::Mut(r1), ptr_path), Ref!(r2, bound, Mutability::Mut)) => {
                    debug_assert_eq!(r1, r2);
                    let ty = self.bindings.lookup(ptr_path).block_with(bound.clone());
                    gen.subtyping(rcx, &ty, bound, reason);

                    self.update(path, Ty::mk_ref(*r1, bound.clone(), Mutability::Mut));
                }
                (TyKind::Ptr(PtrKind::Shr(r1), ptr_path), Ref!(r2, _, Mutability::Not)) => {
                    debug_assert_eq!(r1, r2);
                    let ty = self.bindings.get(ptr_path);
                    self.update(path, Ty::mk_ref(*r1, ty, Mutability::Not));
                }
                _ => (),
            }
        }

        // Check subtyping
        for (path, _, ty2) in bb_env {
            let ty1 = self.bindings.get(&path);
            gen.subtyping(rcx, &ty1.unblocked(), &ty2.unblocked(), reason);
        }
        Ok(())
    }

    pub(crate) fn fold(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
    ) -> Result<(), CheckerErrKind> {
        self.bindings.lookup(place).fold(rcx, gen)
    }

    pub(crate) fn unfold(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        place: &Place,
        checker_conf: CheckerConfig,
    ) -> Result<(), CheckerErrKind> {
        self.bindings.unfold(genv, rcx, place, checker_conf)
    }

    pub(crate) fn downcast(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        place: &Place,
        variant_idx: VariantIdx,
        checker_config: CheckerConfig,
    ) -> Result<(), CheckerErrKind> {
        let mut down_place = place.clone();
        down_place
            .projection
            .push(PlaceElem::Downcast(None, variant_idx));
        self.bindings
            .unfold(genv, rcx, &down_place, checker_config)?;
        Ok(())
    }

    pub fn replace_evars(&mut self, evars: &EVarSol) {
        self.bindings
            .fmap_mut(|binding| binding.replace_evars(evars));
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.bindings.lookup(path).update(ty);
    }
}

impl BasicBlockEnvShape {
    pub fn enter<'a>(&self, local_decls: &'a LocalDecls) -> TypeEnv<'a> {
        TypeEnv { bindings: self.bindings.clone(), local_decls }
    }

    fn new(scope: Scope, env: TypeEnv) -> Result<BasicBlockEnvShape, CheckerErrKind> {
        let mut bindings = env.bindings;
        bindings.fmap_mut(|ty| BasicBlockEnvShape::pack_ty(&scope, ty));
        Ok(BasicBlockEnvShape { scope, bindings })
    }

    fn pack_ty(scope: &Scope, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, idxs) => {
                let bty = BasicBlockEnvShape::pack_bty(scope, bty);
                if scope.has_free_vars(idxs) {
                    Ty::exists_with_constr(bty, Expr::hole())
                } else {
                    Ty::indexed(bty, idxs.clone())
                }
            }
            TyKind::Downcast(adt, substs, ty, variant, fields) => {
                debug_assert!(!scope.has_free_vars(substs));
                debug_assert!(!scope.has_free_vars(ty));
                let fields = fields.iter().map(|ty| Self::pack_ty(scope, ty)).collect();
                Ty::downcast(adt.clone(), substs.clone(), ty.clone(), *variant, fields)
            }
            TyKind::Blocked(ty) => Ty::blocked(BasicBlockEnvShape::pack_ty(scope, ty)),
            TyKind::Alias(..) => {
                assert!(!scope.has_free_vars(ty));
                ty.clone()
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
                    .map(|ty| BasicBlockEnvShape::pack_ty(scope, ty))
                    .collect();
                BaseTy::Tuple(tys)
            }
            BaseTy::Slice(ty) => BaseTy::Slice(Self::pack_ty(scope, ty)),
            BaseTy::Ref(r, ty, mutbl) => BaseTy::Ref(*r, Self::pack_ty(scope, ty), *mutbl),
            BaseTy::Array(ty, c) => BaseTy::Array(Self::pack_ty(scope, ty), c.clone()),
            BaseTy::Int(_)
            | BaseTy::Param(_)
            | BaseTy::Uint(_)
            | BaseTy::Bool
            | BaseTy::Float(_)
            | BaseTy::Str
            | BaseTy::RawPtr(_, _)
            | BaseTy::Char
            | BaseTy::Never
            | BaseTy::Closure(_, _)
            | BaseTy::Generator(_, _)
            | BaseTy::GeneratorWitness(_) => bty.clone(),
        }
    }

    fn pack_generic_arg(scope: &Scope, arg: &GenericArg) -> GenericArg {
        match arg {
            GenericArg::Ty(ty) => GenericArg::Ty(Self::pack_ty(scope, ty)),
            GenericArg::BaseTy(arg) => {
                GenericArg::BaseTy(arg.as_ref().map(|ty| Self::pack_ty(scope, ty)))
            }
            GenericArg::Lifetime(re) => GenericArg::Lifetime(*re),
            GenericArg::Const(c) => GenericArg::Const(c.clone()),
        }
    }

    fn block(&mut self, path: &Path) -> Ty {
        self.bindings.lookup(path).block()
    }

    pub(crate) fn block_with(&mut self, path: &Path, new_ty: Ty) -> Ty {
        self.bindings.lookup(path).block_with(new_ty)
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.bindings.lookup(path).update(ty);
    }

    /// join(self, genv, other) consumes the bindings in other, to "update"
    /// `self` in place, and returns `true` if there was an actual change
    /// or `false` indicating no change (i.e., a fixpoint was reached).
    pub(crate) fn join(&mut self, mut other: TypeEnv) -> Result<bool, CheckerErrKind> {
        let paths = self.bindings.paths();

        // Convert pointers to borrows
        for path in &paths {
            let ty1 = self.bindings.get(path);
            let ty2 = other.bindings.get(path);
            match (ty1.kind(), ty2.kind()) {
                (TyKind::Ptr(PtrKind::Shr(r1), path1), TyKind::Ptr(PtrKind::Shr(r2), path2))
                    if path1 != path2 =>
                {
                    debug_assert_eq!(r1, r2);
                    let ty1 = self.block(path1);
                    let ty2 = self.block(path2);

                    self.update(path, Ty::mk_ref(*r1, ty1, Mutability::Not));
                    other.update(path, Ty::mk_ref(*r2, ty2, Mutability::Not));
                }
                (TyKind::Ptr(PtrKind::Shr(r1), ptr_path), Ref!(r2, _, Mutability::Not)) => {
                    debug_assert_eq!(r1, r2);
                    let ty = self.block(ptr_path);
                    self.update(path, Ty::mk_ref(*r1, ty, Mutability::Not));
                }
                (Ref!(r1, _, Mutability::Not), TyKind::Ptr(PtrKind::Shr(r2), ptr_path)) => {
                    debug_assert_eq!(r1, r2);
                    let ty = other.block(ptr_path);
                    other.update(path, Ty::mk_ref(*r1, ty, Mutability::Not));
                }
                (TyKind::Ptr(PtrKind::Mut(r1), path1), TyKind::Ptr(PtrKind::Mut(r2), path2))
                    if path1 != path2 =>
                {
                    debug_assert_eq!(r1, r2);
                    let ty1 = self.bindings.get(path1).with_holes();
                    let ty2 = other.bindings.get(path2).with_holes();

                    self.update(path, Ty::mk_ref(*r1, ty1.clone(), Mutability::Mut));
                    other.update(path, Ty::mk_ref(*r1, ty2.clone(), Mutability::Mut));

                    self.block_with(path1, ty1);
                    other.block_with(path2, ty2);
                }
                (TyKind::Ptr(PtrKind::Mut(r1), ptr_path), Ref!(r2, bound, Mutability::Mut)) => {
                    debug_assert_eq!(r1, r2);
                    let bound = bound.with_holes();
                    self.block_with(ptr_path, bound.clone());
                    self.update(path, Ty::mk_ref(*r1, bound, Mutability::Mut));
                }
                (Ref!(r1, bound, Mutability::Mut), TyKind::Ptr(PtrKind::Mut(r2), ptr_path)) => {
                    debug_assert_eq!(r1, r2);
                    let bound = bound.with_holes();
                    other.block_with(ptr_path, bound.clone());
                    other.update(path, Ty::mk_ref(*r1, bound, Mutability::Mut));
                }
                _ => {}
            }
        }

        // Join types
        let mut modified = false;
        for path in &paths {
            let ty1 = self.bindings.get(path);
            let ty2 = other.bindings.get(path);
            let ty = self.join_ty(&ty1, &ty2);
            modified |= ty1 != ty;
            self.update(path, ty);
        }

        Ok(modified)
    }

    fn join_ty(&self, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Blocked(ty1), _) => Ty::blocked(self.join_ty(ty1, &ty2.unblocked())),
            (_, TyKind::Blocked(ty2)) => Ty::blocked(self.join_ty(&ty1.unblocked(), ty2)),
            (TyKind::Uninit, _) | (_, TyKind::Uninit) => Ty::uninit(),
            (TyKind::Exists(ty1), _) => self.join_ty(ty1.as_ref().skip_binder(), ty2),
            (_, TyKind::Exists(ty2)) => self.join_ty(ty1, ty2.as_ref().skip_binder()),
            (TyKind::Constr(_, ty1), _) => self.join_ty(ty1, ty2),
            (_, TyKind::Constr(_, ty2)) => self.join_ty(ty1, ty2),
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                let bty = self.join_bty(bty1, bty2);
                let mut sorts = vec![];
                let idx = self.join_idx(&idx1.expr, &idx2.expr, &bty.sort(), &mut sorts);
                if sorts.is_empty() {
                    Ty::indexed(bty, idx)
                } else {
                    let ty = Ty::constr(Expr::hole(), Ty::indexed(bty, idx));
                    Ty::exists(Binder::with_sorts(ty, sorts))
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
            (
                TyKind::Downcast(adt1, substs1, ty1, variant1, fields1),
                TyKind::Downcast(adt2, substs2, ty2, variant2, fields2),
            ) => {
                debug_assert_eq!(adt1, adt2);
                debug_assert_eq!(substs1, substs2);
                debug_assert!(ty1 == ty2 && !self.scope.has_free_vars(ty2));
                debug_assert_eq!(variant1, variant2);
                debug_assert_eq!(fields1.len(), fields2.len());
                let fields = iter::zip(fields1, fields2)
                    .map(|(ty1, ty2)| self.join_ty(ty1, ty2))
                    .collect();
                Ty::downcast(adt1.clone(), substs1.clone(), ty1.clone(), *variant1, fields)
            }
            (TyKind::Alias(kind1, alias_ty1), TyKind::Alias(kind2, alias_ty2)) => {
                debug_assert_eq!(kind1, kind2);
                debug_assert_eq!(alias_ty1, alias_ty2);
                Ty::alias(*kind1, alias_ty1.clone())
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
                    Expr::late_bvar(INNERMOST, (bound_sorts.len() - 1) as u32)
                }
            }
        }
    }

    fn join_bty(&self, bty1: &BaseTy, bty2: &BaseTy) -> BaseTy {
        match (bty1, bty2) {
            (BaseTy::Adt(def1, substs1), BaseTy::Adt(def2, substs2)) => {
                debug_assert_eq!(def1.did(), def2.did());
                let substs = iter::zip(substs1, substs2)
                    .map(|(arg1, arg2)| self.join_generic_arg(arg1, arg2))
                    .collect();
                BaseTy::adt(def1.clone(), List::from_vec(substs))
            }
            (BaseTy::Tuple(fields1), BaseTy::Tuple(fields2)) => {
                let fields = iter::zip(fields1, fields2)
                    .map(|(ty1, ty2)| self.join_ty(ty1, ty2))
                    .collect();
                BaseTy::Tuple(fields)
            }
            (BaseTy::Ref(r1, ty1, mutbl1), BaseTy::Ref(r2, ty2, mutbl2)) => {
                debug_assert_eq!(r1, r2);
                debug_assert_eq!(mutbl1, mutbl2);
                BaseTy::Ref(*r1, self.join_ty(ty1, ty2), *mutbl1)
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
            (GenericArg::BaseTy(_), GenericArg::BaseTy(_)) => {
                tracked_span_bug!("generic argument join for base types ins not implemented")
            }
            (GenericArg::Lifetime(re1), GenericArg::Lifetime(re2)) => {
                debug_assert_eq!(re1, re2);
                GenericArg::Lifetime(*re1)
            }
            _ => tracked_span_bug!("unexpected generic args: `{arg1:?}` - `{arg2:?}`"),
        }
    }

    pub fn into_bb_env(self, kvar_store: &mut KVarStore) -> BasicBlockEnv {
        let mut bindings = self.bindings;

        let mut generalizer = Generalizer::new(self.scope.name_gen());
        bindings.fmap_mut(|ty| generalizer.generalize_ty(ty));
        let (names, sorts, preds) = generalizer.into_parts();
        // Replace all holes with a single fresh kvar on all parameters
        let mut constrs = preds
            .into_iter()
            .filter(|pred| !matches!(pred.kind(), ExprKind::Hole))
            .collect_vec();
        let params = iter::zip(names, sorts).collect_vec();
        let kvar = kvar_store.fresh(
            params.len(),
            params
                .iter()
                .cloned()
                .chain(self.scope.iter())
                .map(|(name, sort)| (Var::Free(name), sort)),
            KVarEncoding::Conj,
        );
        constrs.push(kvar);

        // Replace remaning holes by fresh kvars
        let mut kvar_gen = |sorts: &[_]| {
            kvar_store.fresh_bound(
                sorts,
                self.scope.iter().chain(params.iter().cloned()),
                KVarEncoding::Conj,
            )
        };
        bindings.fmap_mut(|binding| binding.replace_holes(&mut kvar_gen));

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
                let ty = ty.replace_bound_exprs_with(|sort, _| self.fresh_vars(sort));
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
            BaseTy::Ref(r, ty, Mutability::Not) => {
                let ty = self.generalize_ty(ty);
                BaseTy::Ref(*r, ty, Mutability::Not)
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
    pub(crate) fn enter<'a>(
        &self,
        rcx: &mut RefineCtxt,
        local_decls: &'a LocalDecls,
    ) -> TypeEnv<'a> {
        let mut subst = FVarSubst::empty();
        for (name, sort) in &self.params {
            let fresh = rcx.define_var(sort);
            subst.insert(*name, Expr::fvar(fresh));
        }
        for constr in &self.constrs {
            rcx.assume_pred(subst.apply(constr));
        }
        let bindings = self.bindings.fmap(|binding| subst.apply(binding));
        TypeEnv { bindings, local_decls }
    }

    pub(crate) fn scope(&self) -> &Scope {
        &self.scope
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;
    use itertools::Itertools;

    use super::*;

    impl Pretty for TypeEnv<'_> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PlacesTree::default_cx(tcx)
        }
    }

    impl Pretty for BasicBlockEnvShape {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} {:?}", &self.scope, &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PlacesTree::default_cx(tcx)
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
            PlacesTree::default_cx(tcx)
        }
    }

    impl_debug_with_default_cx!(TypeEnv<'_> => "type_env", BasicBlockEnvShape => "type_env_infer", BasicBlockEnv => "basic_block_env");
}
