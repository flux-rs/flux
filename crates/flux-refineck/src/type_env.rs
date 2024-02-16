mod place_ty;

use std::{iter, ops::ControlFlow};

use flux_common::{dbg::debug_assert_eq3, tracked_span_bug};
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        canonicalize::Hoister,
        evars::EVarSol,
        fold::{FallibleTypeFolder, TypeFoldable, TypeVisitable, TypeVisitor},
        subst::RegionSubst,
        BaseTy, Binder, BoundReftKind, Expr, ExprKind, GenericArg, HoleKind, Mutability, Path,
        PtrKind, Region, SortCtor, Ty, TyKind, INNERMOST,
    },
    rustc::mir::{BasicBlock, Local, LocalDecls, Place, PlaceElem},
};
use itertools::{izip, Itertools};
use rustc_middle::ty::TyCtxt;

use self::place_ty::{LocKind, PlacesTree};
use super::rty::{Loc, Sort};
use crate::{
    checker::errors::CheckerErrKind,
    constraint_gen::{ConstrGen, ConstrReason},
    fixpoint_encoding::{KVarEncoding, KVarStore},
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
    data: Binder<BasicBlockEnvData>,
    scope: Scope,
}

#[derive(Debug)]
struct BasicBlockEnvData {
    constrs: List<Expr>,
    bindings: PlacesTree,
}

impl TypeEnv<'_> {
    pub fn new(local_decls: &LocalDecls) -> TypeEnv {
        TypeEnv { bindings: PlacesTree::default(), local_decls }
    }

    pub fn alloc_universal_loc(&mut self, loc: Loc, place: Place, ty: Ty) {
        self.bindings.insert(loc, place, LocKind::Universal, ty);
    }

    pub fn alloc_with_ty(&mut self, local: Local, ty: Ty) {
        let ty = RegionSubst::new(&ty, &self.local_decls[local].ty).apply(&ty);
        self.bindings
            .insert(local.into(), Place::new(local, vec![]), LocKind::Local, ty);
    }

    pub fn alloc(&mut self, local: Local) {
        self.bindings
            .insert(local.into(), Place::new(local, vec![]), LocKind::Local, Ty::uninit());
    }

    pub(crate) fn into_infer(self, scope: Scope) -> Result<BasicBlockEnvShape, CheckerErrKind> {
        BasicBlockEnvShape::new(scope, self)
    }

    pub(crate) fn lookup_place(
        &mut self,
        genv: GlobalEnv,
        rcx: &mut RefineCtxt,
        place: &Place,
    ) -> Result<Ty, CheckerErrKind> {
        Ok(self.bindings.lookup_unfolding(genv, rcx, place)?.ty)
    }

    pub(crate) fn get(&self, path: &Path) -> Ty {
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
        genv: GlobalEnv,
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

    /// Converts a pointer `ptr(mut, l)` to a borrow `&mut T` for a type `T` that needs to be inferred.
    /// For example, given the environment
    /// ```text
    /// x: i32[a], p: ptr(mut, x)
    /// ```
    ///
    /// Converting the pointer to a borrow will produce
    ///
    /// ```text
    /// x: †i32{v: $k(v)}, p: &mut i32{v: $k(v)}
    /// ```
    ///
    /// together with a constraint
    ///
    /// ```text
    /// i32[a] <: i32{v: $k(v)}
    /// ```
    pub(crate) fn ptr_to_borrow(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
    ) -> Result<(), CheckerErrKind> {
        // place: ptr(mut, path)
        let ptr_lookup = self.bindings.lookup(place);
        let TyKind::Ptr(PtrKind::Mut(re), path) = ptr_lookup.ty.kind() else {
            tracked_span_bug!("ptr_to_borrow called on non mutable pointer type")
        };

        // path: old_ty
        let old_ty = self.bindings.lookup(path).fold(rcx, gen)?;

        let mut infcx = gen.infcx(rcx, ConstrReason::Other);

        // old_ty <: new_ty
        let new_ty = old_ty.with_holes().replace_holes(|sorts, kind| {
            debug_assert_eq!(kind, HoleKind::Pred);
            infcx.fresh_kvar(sorts, KVarEncoding::Conj)
        });
        infcx.subtyping(rcx, &old_ty, &new_ty)?;

        // path: new_ty, place: &mut new_ty
        self.bindings.lookup(path).block_with(new_ty.clone());
        self.bindings
            .lookup(place)
            .update(Ty::mk_ref(*re, new_ty, Mutability::Mut));

        rcx.replace_evars(&infcx.solve().unwrap());

        Ok(())
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
        genv: GlobalEnv,
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

    pub(crate) fn unpack(&mut self, rcx: &mut RefineCtxt, check_overflow: bool) {
        self.bindings
            .fmap_mut(|ty| rcx.unpacker().assume_invariants(check_overflow).unpack(ty));
    }

    pub(crate) fn unblock(&mut self, rcx: &mut RefineCtxt, place: &Place, check_overflow: bool) {
        self.bindings.lookup(place).unblock(rcx, check_overflow);
    }

    pub(crate) fn block_with(
        &mut self,
        genv: GlobalEnv,
        path: &Path,
        new_ty: Ty,
    ) -> Result<Ty, CheckerErrKind> {
        let place = self.bindings.path_to_place(path);
        let rustc_ty = place.ty(genv, self.local_decls)?.ty;
        let new_ty = RegionSubst::new(&new_ty, &rustc_ty).apply(&new_ty);

        Ok(self.bindings.lookup(path).block_with(new_ty))
    }

    pub(crate) fn check_goto(
        self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        bb_env: &BasicBlockEnv,
        target: BasicBlock,
    ) -> Result<(), CheckerErrKind> {
        let mut infcx = gen.infcx(rcx, ConstrReason::Goto(target));

        let bb_env = bb_env
            .data
            .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));

        // Check constraints
        for constr in &bb_env.constrs {
            infcx.check_pred(rcx, constr);
        }

        // Check subtyping
        let bb_env = bb_env.bindings.flatten();
        for (path, _, ty2) in bb_env {
            let ty1 = self.bindings.get(&path);
            infcx.subtyping(rcx, &ty1.unblocked(), &ty2.unblocked())?;
        }

        rcx.replace_evars(&infcx.solve().unwrap());

        Ok(())
    }

    pub(crate) fn fold(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
    ) -> Result<(), CheckerErrKind> {
        self.bindings.lookup(place).fold(rcx, gen)?;
        Ok(())
    }

    pub(crate) fn unfold(
        &mut self,
        genv: GlobalEnv,
        rcx: &mut RefineCtxt,
        place: &Place,
        checker_conf: CheckerConfig,
    ) -> Result<(), CheckerErrKind> {
        self.bindings.unfold(genv, rcx, place, checker_conf)
    }

    pub(crate) fn downcast(
        &mut self,
        genv: GlobalEnv,
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
                    Ty::exists_with_constr(bty, Expr::hole(HoleKind::Pred))
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
            | BaseTy::Coroutine(..) => bty.clone(),
        }
    }

    fn pack_generic_arg(scope: &Scope, arg: &GenericArg) -> GenericArg {
        match arg {
            GenericArg::Ty(ty) => GenericArg::Ty(Self::pack_ty(scope, ty)),
            GenericArg::Base(arg) => {
                GenericArg::Base(arg.as_ref().map(|ty| Self::pack_ty(scope, ty)))
            }
            GenericArg::Lifetime(re) => GenericArg::Lifetime(*re),
            GenericArg::Const(c) => GenericArg::Const(c.clone()),
        }
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.bindings.lookup(path).update(ty);
    }

    /// join(self, genv, other) consumes the bindings in other, to "update"
    /// `self` in place, and returns `true` if there was an actual change
    /// or `false` indicating no change (i.e., a fixpoint was reached).
    pub(crate) fn join(&mut self, other: TypeEnv) -> Result<bool, CheckerErrKind> {
        let paths = self.bindings.paths();

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
                let idx = self.join_idx(idx1, idx2, &bty.sort(), &mut sorts);
                if sorts.is_empty() {
                    Ty::indexed(bty, idx)
                } else {
                    let ty = Ty::constr(Expr::hole(HoleKind::Pred), Ty::indexed(bty, idx));
                    Ty::exists(Binder::with_sorts(ty, &sorts))
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
            (ExprKind::Aggregate(_, es1), ExprKind::Aggregate(_, es2), Sort::Tuple(sorts)) => {
                debug_assert_eq3!(es1.len(), es2.len(), sorts.len());
                Expr::tuple(
                    izip!(es1, es2, sorts)
                        .map(|(e1, e2, sort)| self.join_idx(e1, e2, sort, bound_sorts))
                        .collect(),
                )
            }
            (
                ExprKind::Aggregate(_, flds1),
                ExprKind::Aggregate(_, flds2),
                Sort::App(SortCtor::Adt(sort_def), args),
            ) => {
                let sorts = sort_def.sorts(args);
                debug_assert_eq3!(flds1.len(), flds2.len(), sorts.len());

                Expr::adt(
                    sort_def.did(),
                    izip!(flds1, flds2, &sorts)
                        .map(|(f1, f2, sort)| self.join_idx(f1, f2, sort, bound_sorts))
                        .collect(),
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
                    Expr::late_bvar(INNERMOST, (bound_sorts.len() - 1) as u32, BoundReftKind::Annon)
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
            (GenericArg::Base(_), GenericArg::Base(_)) => {
                tracked_span_bug!("generic argument join for base types is not implemented")
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

        let mut hoister = Hoister::default();
        bindings.fmap_mut(|ty| hoister.hoist(ty));
        let (vars, preds) = hoister.into_parts();

        // Replace all holes with a single fresh kvar on all parameters
        let mut constrs = preds
            .into_iter()
            .filter(|pred| !matches!(pred.kind(), ExprKind::Hole(HoleKind::Pred)))
            .collect_vec();

        let outter_sorts = vars.to_sort_list();

        let kvar = kvar_store.fresh(&[outter_sorts.clone()], &self.scope, KVarEncoding::Conj);
        constrs.push(kvar);

        // Replace remaning holes by fresh kvars
        let mut kvar_gen = |sorts: &[_], kind| {
            debug_assert_eq!(kind, HoleKind::Pred);
            let sorts = std::iter::once(outter_sorts.clone())
                .chain(sorts.iter().cloned())
                .collect_vec();
            kvar_store.fresh(&sorts, &self.scope, KVarEncoding::Conj)
        };
        bindings.fmap_mut(|binding| binding.replace_holes(&mut kvar_gen));

        let data = BasicBlockEnvData { constrs: constrs.into(), bindings };

        BasicBlockEnv { data: Binder::new(data, vars), scope: self.scope }
    }
}

impl TypeVisitable for BasicBlockEnvData {
    fn visit_with<V: TypeVisitor>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        unimplemented!()
    }
}

impl TypeFoldable for BasicBlockEnvData {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        Ok(BasicBlockEnvData {
            constrs: self.constrs.try_fold_with(folder)?,
            bindings: self.bindings.try_fold_with(folder)?,
        })
    }
}

impl BasicBlockEnv {
    pub(crate) fn enter<'a>(
        &self,
        rcx: &mut RefineCtxt,
        local_decls: &'a LocalDecls,
    ) -> TypeEnv<'a> {
        let data = self
            .data
            .replace_bound_refts_with(|sort, _, _| rcx.define_vars(sort));
        for constr in &data.constrs {
            rcx.assume_pred(constr);
        }
        TypeEnv { bindings: data.bindings, local_decls }
    }

    pub(crate) fn scope(&self) -> &Scope {
        &self.scope
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;

    use super::*;

    impl Pretty for TypeEnv<'_> {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PrettyCx {
            PlacesTree::default_cx(tcx)
        }
    }

    impl Pretty for BasicBlockEnvShape {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} {:?}", &self.scope, &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PrettyCx {
            PlacesTree::default_cx(tcx)
        }
    }

    impl Pretty for BasicBlockEnv {
        fn fmt(&self, cx: &PrettyCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} ", &self.scope)?;

            let vars = self.data.vars();
            cx.with_bound_vars(vars, || {
                if !vars.is_empty() {
                    cx.fmt_bound_vars("for<", vars, ">", f)?;
                }
                let data = self.data.as_ref().skip_binder();
                if !data.constrs.is_empty() {
                    w!(
                        "{:?} ⇒ ",
                        join!(", ", data.constrs.iter().filter(|pred| !pred.is_trivially_true()))
                    )?;
                }
                w!("{:?}", &data.bindings)
            })
        }

        fn default_cx(tcx: TyCtxt) -> PrettyCx {
            PlacesTree::default_cx(tcx)
        }
    }

    impl_debug_with_default_cx! {
        TypeEnv<'_> => "type_env",
        BasicBlockEnvShape => "basic_block_env_shape",
        BasicBlockEnv => "basic_block_env"
    }
}
