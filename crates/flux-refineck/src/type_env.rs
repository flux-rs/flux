mod place_ty;

use std::{iter, ops::ControlFlow};

use flux_common::{bug, dbg::debug_assert_eq3, tracked_span_bug, tracked_span_dbg_assert_eq};
use flux_infer::{
    fixpoint_encoding::{KVarEncoding, KVarGen},
    infer::{ConstrReason, InferCtxt, InferCtxtAt, InferResult},
    refine_tree::{AssumeInvariants, RefineCtxt, Scope},
};
use flux_macros::DebugAsJson;
use flux_middle::{
    global_env::GlobalEnv,
    pretty::{PrettyCx, WithCx},
    queries::QueryResult,
    rty::{
        canonicalize::{Hoister, LocalHoister},
        evars::EVarSol,
        fold::{FallibleTypeFolder, TypeFoldable, TypeVisitable, TypeVisitor},
        region_matching::{rty_match_regions, ty_match_regions},
        BaseTy, Binder, BoundReftKind, Ensures, Expr, ExprKind, FnOutput, FnSig, GenericArg,
        HoleKind, Lambda, List, Loc, Mutability, Path, PtrKind, Region, SortCtor, SubsetTy, Ty,
        TyKind, VariantIdx, INNERMOST,
    },
    PlaceExt as _,
};
use flux_rustc_bridge::{
    self,
    mir::{BasicBlock, Body, Local, LocalDecls, Place, PlaceElem},
    ty,
};
use itertools::{izip, Itertools};
use rustc_data_structures::unord::UnordMap;
use rustc_index::IndexSlice;
use rustc_middle::{mir::RETURN_PLACE, ty::TyCtxt};
use rustc_span::Symbol;
use rustc_type_ir::BoundVar;
use serde::Serialize;

use self::place_ty::{LocKind, PlacesTree};
use super::rty::Sort;
use crate::{checker::errors::CheckerErrKind, CheckerConfig};

type Result<T = ()> = std::result::Result<T, CheckerErrKind>;

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

impl<'a> TypeEnv<'a> {
    pub fn new(
        infcx: &mut InferCtxt,
        body: &'a Body,
        fn_sig: &FnSig,
        check_overflow: bool,
    ) -> TypeEnv<'a> {
        let mut env = TypeEnv { bindings: PlacesTree::default(), local_decls: &body.local_decls };

        for requires in fn_sig.requires() {
            infcx.assume_pred(requires);
        }

        for (local, ty) in body.args_iter().zip(fn_sig.inputs()) {
            let ty = infcx.unpack(ty);
            infcx.assume_invariants(&ty, check_overflow);
            env.alloc_with_ty(local, ty);
        }

        for local in body.vars_and_temps_iter() {
            env.alloc(local);
        }

        env.alloc(RETURN_PLACE);
        env
    }

    pub fn empty() -> TypeEnv<'a> {
        TypeEnv { bindings: PlacesTree::default(), local_decls: IndexSlice::empty() }
    }

    fn alloc_with_ty(&mut self, local: Local, ty: Ty) {
        let ty = ty_match_regions(&ty, &self.local_decls[local].ty);
        self.bindings.insert(local.into(), LocKind::Local, ty);
    }

    fn alloc(&mut self, local: Local) {
        self.bindings
            .insert(local.into(), LocKind::Local, Ty::uninit());
    }

    pub(crate) fn into_infer(self, scope: Scope) -> Result<BasicBlockEnvShape> {
        BasicBlockEnvShape::new(scope, self)
    }

    pub(crate) fn lookup_rust_ty(&self, genv: GlobalEnv, place: &Place) -> QueryResult<ty::Ty> {
        Ok(place.ty(genv, self.local_decls)?.ty)
    }

    pub(crate) fn lookup_place(&mut self, infcx: &mut InferCtxtAt, place: &Place) -> Result<Ty> {
        Ok(self.bindings.lookup_unfolding(infcx, place)?.ty)
    }

    pub(crate) fn get(&self, path: &Path) -> Ty {
        self.bindings.get(path)
    }

    pub fn update_path(&mut self, path: &Path, new_ty: Ty) {
        self.bindings.lookup(path).update(new_ty);
    }

    /// When checking a borrow in the right hand side of an assignment `x = &'?n p`, we use the
    /// annotated region `'?n` in the type of the result. This region will only be used temporarily
    /// and then replaced by the region in the type of `x` after the assignment. See [`TypeEnv::assign`]
    pub(crate) fn borrow(
        &mut self,
        infcx: &mut InferCtxtAt,
        re: Region,
        mutbl: Mutability,
        place: &Place,
    ) -> Result<Ty> {
        let result = self.bindings.lookup_unfolding(infcx, place)?;
        if result.is_strg && mutbl == Mutability::Mut {
            Ok(Ty::ptr(PtrKind::Mut(re), result.path()))
        } else {
            // FIXME(nilehmann) we should block the place here. That would require a notion
            // of shared vs mutable block types because sometimes blocked places from a shared
            // reference never get unblocked and we should still allow reads through them.
            Ok(Ty::mk_ref(re, result.ty, mutbl))
        }
    }

    // FIXME(nilehmann) this is only used in a single place and we have it because [`TypeEnv`]
    // doesn't expose a lookup without unfolding
    pub(crate) fn ptr_to_ref_at_place(&mut self, infcx: &mut InferCtxtAt, place: &Place) -> Result {
        let lookup = self.bindings.lookup(place);
        let TyKind::Ptr(PtrKind::Mut(re), path) = lookup.ty.kind() else {
            tracked_span_bug!("ptr_to_borrow called on non mutable pointer type")
        };

        let ref_ty =
            self.ptr_to_ref(infcx, ConstrReason::Other, *re, path, PtrToRefBound::Infer)?;

        self.bindings.lookup(place).update(ref_ty);

        Ok(())
    }

    /// Convert a (strong) pointer to a mutable reference.
    ///
    /// This roughly implements the following inference rule:
    /// ```text
    ///                   t₁ <: t₂
    /// -------------------------------------------------
    /// Γ₁,ℓ:t1,Γ₂ ; ptr(mut, ℓ) => Γ₁,ℓ:†t₂,Γ₂ ; &mut t2
    /// ```
    /// That's it, we first get the current type `t₁` at location `ℓ` and check it is a subtype
    /// of `t₂`. Then, we update the type of `ℓ` to `t₂` and block the place.
    ///
    /// The bound `t₂` can be either inferred ([`PtrToRefBound::Infer`]), explicitly provided
    /// ([`PtrToRefBound::Ty`]), or made equal to `t₁` ([`PtrToRefBound::Identity`]).
    ///
    /// As an example, consider the environment `x: i32[a]` and the pointer `ptr(mut, x)`.
    /// Converting the pointer to a mutable reference with an inferred bound produces the following
    /// derivation (roughly):
    ///
    /// ```text
    ///                    i32[a] <: i32{v: $k(v)}
    /// ----------------------------------------------------------------
    /// x: i32[a] ; ptr(mut, x) => x:†i32{v: $k(v)} ; &mut i32{v: $k(v)}
    /// ```
    pub(crate) fn ptr_to_ref(
        &mut self,
        infcx: &mut InferCtxtAt,
        reason: ConstrReason,
        re: Region,
        path: &Path,
        bound: PtrToRefBound,
    ) -> InferResult<Ty> {
        infcx.push_scope();

        // ℓ: t1
        let t1 = self.bindings.lookup(path).fold(infcx)?;

        // t1 <: t2
        let t2 = match bound {
            PtrToRefBound::Ty(t2) => {
                // FIXME(nilehmann) we could match regions against `t1` instead of mapping the path
                // to a place which requires annoying bookkeping.
                // let place = self.bindings.path_to_place(path);
                // let rust_ty = place.ty(infcx.genv, self.local_decls)?.ty;
                let t2 = rty_match_regions(&t2, &t1);
                infcx.subtyping(&t1, &t2, reason)?;
                t2
            }
            PtrToRefBound::Infer => {
                let t2 = t1.with_holes().replace_holes(|sorts, kind| {
                    debug_assert_eq!(kind, HoleKind::Pred);
                    infcx.fresh_kvar(sorts, KVarEncoding::Conj)
                });
                infcx.subtyping(&t1, &t2, reason)?;
                t2
            }
            PtrToRefBound::Identity => t1.clone(),
        };

        // ℓ: †t2
        self.bindings.lookup(path).block_with(t2.clone());

        let evar_sol = infcx.pop_scope().unwrap();
        infcx.replace_evars(&evar_sol);
        self.replace_evars(&evar_sol);

        Ok(Ty::mk_ref(re, t2, Mutability::Mut))
    }

    pub(crate) fn fold_local_ptrs(&mut self, infcx: &mut InferCtxtAt) -> InferResult<()> {
        for (loc, bound, ty) in self.bindings.local_ptrs() {
            infcx.subtyping(&ty, &bound, ConstrReason::FoldLocal)?;
            self.bindings.remove_local(&loc);
        }
        Ok(())
    }

    /// Updates the type of `place` to `new_ty`. This may involve a *strong update* if we have
    /// ownership of `place` or a *weak update* if it's behind a reference (which fires a subtyping
    /// constraint)
    ///
    /// When strong updating, the process involves recovering the original regions (lifetimes) used
    /// in the (unrefined) Rust type of `place` and then substituting these regions in `new_ty`. For
    /// instance, if we are assigning a value of type `S<&'?10 i32{v: v > 0}>` to a variable `x`,
    /// and the (unrefined) Rust type of `x` is `S<&'?5 i32>`, before the assignment, we identify a
    /// substitution that maps the region `'?10` to `'?5`. After applying this substitution, the
    /// type of the place `x` is updated accordingly. This ensures that the lifetimes in the
    /// assigned type are consistent with those expected by the place's original type definition.
    pub(crate) fn assign(&mut self, infcx: &mut InferCtxtAt, place: &Place, new_ty: Ty) -> Result {
        let rustc_ty = place.ty(infcx.genv, self.local_decls)?.ty;
        let new_ty = ty_match_regions(&new_ty, &rustc_ty);
        let result = self.bindings.lookup_unfolding(infcx, place)?;
        infcx.push_scope();
        if result.is_strg {
            result.update(new_ty);
        } else if !place.behind_raw_ptr(infcx.genv, self.local_decls)? {
            infcx.subtyping(&new_ty, &result.ty, ConstrReason::Assign)?;
        }
        let evars = &infcx.pop_scope()?;
        infcx.replace_evars(evars);

        Ok(())
    }

    pub(crate) fn move_place(&mut self, infcx: &mut InferCtxtAt, place: &Place) -> Result<Ty> {
        let result = self.bindings.lookup_unfolding(infcx, place)?;
        if result.is_strg {
            let uninit = Ty::uninit();
            Ok(result.update(uninit))
        } else {
            // ignore the 'move' and trust rustc managed the move correctly
            // https://github.com/flux-rs/flux/issues/725#issuecomment-2295065634
            Ok(result.ty)
        }
    }

    pub(crate) fn unpack(&mut self, infcx: &mut InferCtxt, check_overflow: bool) {
        self.bindings.fmap_mut(|ty| {
            infcx
                .hoister(AssumeInvariants::yes(check_overflow))
                .hoist(ty)
        });
    }

    pub(crate) fn unblock(&mut self, rcx: &mut RefineCtxt, place: &Place, check_overflow: bool) {
        self.bindings.unblock(rcx, place, check_overflow);
    }

    pub(crate) fn check_goto(
        self,
        infcx: &mut InferCtxtAt,
        bb_env: &BasicBlockEnv,
        target: BasicBlock,
    ) -> Result {
        infcx.push_scope();

        let bb_env = bb_env
            .data
            .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));

        // Check constraints
        for constr in &bb_env.constrs {
            infcx.check_pred(constr, ConstrReason::Goto(target));
        }

        // Check subtyping
        let bb_env = bb_env.bindings.flatten();
        for (path, _, ty2) in bb_env {
            let ty1 = self.bindings.get(&path);
            infcx.subtyping(&ty1.unblocked(), &ty2.unblocked(), ConstrReason::Goto(target))?;
        }

        let evars = &infcx.pop_scope().unwrap();
        infcx.replace_evars(evars);

        Ok(())
    }

    pub(crate) fn fold(&mut self, infcx: &mut InferCtxtAt, place: &Place) -> Result {
        self.bindings.lookup(place).fold(infcx)?;
        Ok(())
    }

    pub(crate) fn unfold_local_ptr(
        &mut self,
        infcx: &mut InferCtxt,
        bound: &Ty,
    ) -> InferResult<Loc> {
        let loc = Loc::from(infcx.define_var(&Sort::Loc));
        let ty = infcx.unpack(bound);
        self.bindings
            .insert(loc, LocKind::LocalPtr(bound.clone()), ty);
        Ok(loc)
    }

    /// ```text
    /// -----------------------------------
    /// Γ ; &strg <ℓ: t> => Γ,ℓ: t ; ptr(ℓ)
    /// ```
    pub(crate) fn unfold_strg_ref(
        &mut self,
        infcx: &mut InferCtxt,
        path: &Path,
        ty: &Ty,
    ) -> InferResult<Loc> {
        if let Some(loc) = path.to_loc() {
            let ty = infcx.unpack(ty);
            self.bindings.insert(loc, LocKind::Universal, ty);
            Ok(loc)
        } else {
            bug!("unfold_strg_ref: unexpected path {path:?}")
        }
    }

    pub(crate) fn unfold(
        &mut self,
        infcx: &mut InferCtxt,
        place: &Place,
        checker_conf: CheckerConfig,
    ) -> Result {
        self.bindings.unfold(infcx, place, checker_conf)
    }

    pub(crate) fn downcast(
        &mut self,
        infcx: &mut InferCtxtAt,
        place: &Place,
        variant_idx: VariantIdx,
        checker_config: CheckerConfig,
    ) -> Result {
        let mut down_place = place.clone();
        down_place
            .projection
            .push(PlaceElem::Downcast(None, variant_idx));
        self.bindings.unfold(infcx, &down_place, checker_config)?;
        Ok(())
    }

    pub fn replace_evars(&mut self, evars: &EVarSol) {
        self.bindings
            .fmap_mut(|binding| binding.replace_evars(evars));
    }

    pub(crate) fn update_ensures(
        &mut self,
        infcx: &mut InferCtxt,
        output: &FnOutput,
        overflow_checking: bool,
    ) {
        for ensure in &output.ensures {
            match ensure {
                Ensures::Type(path, updated_ty) => {
                    let updated_ty = infcx.unpack(updated_ty);
                    infcx.assume_invariants(&updated_ty, overflow_checking);
                    self.update_path(path, updated_ty);
                }
                Ensures::Pred(e) => infcx.assume_pred(e),
            }
        }
    }

    pub(crate) fn check_ensures(
        &mut self,
        at: &mut InferCtxtAt,
        output: &FnOutput,
        reason: ConstrReason,
    ) -> InferResult {
        for constraint in &output.ensures {
            match constraint {
                Ensures::Type(path, ty) => {
                    let actual_ty = self.get(path);
                    at.subtyping(&actual_ty, ty, reason)?;
                }
                Ensures::Pred(e) => {
                    at.check_pred(e, ConstrReason::Ret);
                }
            }
        }
        Ok(())
    }
}

pub(crate) enum PtrToRefBound {
    Ty(Ty),
    Infer,
    Identity,
}

impl flux_infer::infer::LocEnv for TypeEnv<'_> {
    fn ptr_to_ref(
        &mut self,
        infcx: &mut InferCtxtAt,
        reason: ConstrReason,
        re: Region,
        path: &Path,
        bound: Ty,
    ) -> InferResult<Ty> {
        self.ptr_to_ref(infcx, reason, re, path, PtrToRefBound::Ty(bound))
    }

    fn get(&self, path: &Path) -> Ty {
        self.get(path)
    }

    fn unfold_strg_ref(&mut self, infcx: &mut InferCtxt, path: &Path, ty: &Ty) -> InferResult<Loc> {
        self.unfold_strg_ref(infcx, path, ty)
    }
}

impl BasicBlockEnvShape {
    pub fn enter<'a>(&self, local_decls: &'a LocalDecls) -> TypeEnv<'a> {
        TypeEnv { bindings: self.bindings.clone(), local_decls }
    }

    fn new(scope: Scope, env: TypeEnv) -> Result<BasicBlockEnvShape> {
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
            TyKind::Downcast(adt, args, ty, variant, fields) => {
                debug_assert!(!scope.has_free_vars(args));
                debug_assert!(!scope.has_free_vars(ty));
                let fields = fields.iter().map(|ty| Self::pack_ty(scope, ty)).collect();
                Ty::downcast(adt.clone(), args.clone(), ty.clone(), *variant, fields)
            }
            TyKind::Blocked(ty) => Ty::blocked(BasicBlockEnvShape::pack_ty(scope, ty)),
            // FIXME(nilehmann) [`TyKind::Exists`] could also contain free variables.
            TyKind::Exists(_)
            | TyKind::Discr(..)
            | TyKind::Ptr(..)
            | TyKind::Uninit
            | TyKind::Param(_)
            | TyKind::Constr(_, _) => ty.clone(),
            TyKind::Infer(_) => bug!("unexpected hole whecn checking function body"),
            TyKind::StrgRef(..) => bug!("unexpected strong reference when checking function body"),
        }
    }

    fn pack_bty(scope: &Scope, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, args) => {
                let args = List::from_vec(
                    args.iter()
                        .map(|arg| Self::pack_generic_arg(scope, arg))
                        .collect(),
                );
                BaseTy::adt(adt_def.clone(), args)
            }
            BaseTy::FnDef(def_id, args) => {
                let args = List::from_vec(
                    args.iter()
                        .map(|arg| Self::pack_generic_arg(scope, arg))
                        .collect(),
                );
                BaseTy::fn_def(*def_id, args)
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
            | BaseTy::Closure(..)
            | BaseTy::Dynamic(..)
            | BaseTy::Alias(..)
            | BaseTy::FnPtr(..)
            | BaseTy::Coroutine(..) => {
                assert!(!scope.has_free_vars(bty));
                bty.clone()
            }
            BaseTy::Infer(..) => {
                tracked_span_bug!("unexpected infer type")
            }
        }
    }

    fn pack_generic_arg(scope: &Scope, arg: &GenericArg) -> GenericArg {
        match arg {
            GenericArg::Ty(ty) => GenericArg::Ty(Self::pack_ty(scope, ty)),
            GenericArg::Base(arg) => {
                assert!(!scope.has_free_vars(arg));
                GenericArg::Base(arg.clone())
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
    pub(crate) fn join(&mut self, other: TypeEnv) -> Result<bool> {
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
                    Ty::exists(Binder::bind_with_sorts(ty, &sorts))
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
                TyKind::Downcast(adt1, args1, ty1, variant1, fields1),
                TyKind::Downcast(adt2, args2, ty2, variant2, fields2),
            ) => {
                debug_assert_eq!(adt1, adt2);
                debug_assert_eq!(args1, args2);
                debug_assert!(ty1 == ty2 && !self.scope.has_free_vars(ty2));
                debug_assert_eq!(variant1, variant2);
                debug_assert_eq!(fields1.len(), fields2.len());
                let fields = iter::zip(fields1, fields2)
                    .map(|(ty1, ty2)| self.join_ty(ty1, ty2))
                    .collect();
                Ty::downcast(adt1.clone(), args1.clone(), ty1.clone(), *variant1, fields)
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
                let sorts = sort_def.field_sorts(args);
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
                } else if sort.is_pred() {
                    // FIXME(nilehmann) we shouldn't special case predicates here. Instead, we
                    // should differentiate between generics and indices.
                    let fsort = sort.expect_func().expect_mono();
                    Expr::abs(Lambda::bind_with_fsort(Expr::hole(HoleKind::Pred), fsort))
                } else {
                    bound_sorts.push(sort.clone());
                    Expr::bvar(
                        INNERMOST,
                        BoundVar::from_usize(bound_sorts.len() - 1),
                        BoundReftKind::Annon,
                    )
                }
            }
        }
    }

    fn join_bty(&self, bty1: &BaseTy, bty2: &BaseTy) -> BaseTy {
        match (bty1, bty2) {
            (BaseTy::Adt(def1, args1), BaseTy::Adt(def2, args2)) => {
                debug_assert_eq!(def1.did(), def2.did());
                let args = iter::zip(args1, args2)
                    .map(|(arg1, arg2)| self.join_generic_arg(arg1, arg2))
                    .collect();
                BaseTy::adt(def1.clone(), List::from_vec(args))
            }
            (BaseTy::Tuple(fields1), BaseTy::Tuple(fields2)) => {
                let fields = iter::zip(fields1, fields2)
                    .map(|(ty1, ty2)| self.join_ty(ty1, ty2))
                    .collect();
                BaseTy::Tuple(fields)
            }
            (BaseTy::Alias(kind1, alias_ty1), BaseTy::Alias(kind2, alias_ty2)) => {
                debug_assert_eq!(kind1, kind2);
                debug_assert_eq!(alias_ty1, alias_ty2);
                BaseTy::Alias(*kind1, alias_ty1.clone())
            }
            (BaseTy::Ref(r1, ty1, mutbl1), BaseTy::Ref(r2, ty2, mutbl2)) => {
                debug_assert_eq!(r1, r2);
                debug_assert_eq!(mutbl1, mutbl2);
                BaseTy::Ref(*r1, self.join_ty(ty1, ty2), *mutbl1)
            }
            (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
                tracked_span_dbg_assert_eq!(len1, len2);
                BaseTy::Array(self.join_ty(ty1, ty2), len1.clone())
            }
            (BaseTy::Slice(ty1), BaseTy::Slice(ty2)) => BaseTy::Slice(self.join_ty(ty1, ty2)),
            _ => {
                tracked_span_dbg_assert_eq!(bty1, bty2);
                bty1.clone()
            }
        }
    }

    fn join_generic_arg(&self, arg1: &GenericArg, arg2: &GenericArg) -> GenericArg {
        match (arg1, arg2) {
            (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => GenericArg::Ty(self.join_ty(ty1, ty2)),
            (GenericArg::Base(ctor1), GenericArg::Base(ctor2)) => {
                let sty1 = ctor1.as_ref().skip_binder();
                let sty2 = ctor2.as_ref().skip_binder();
                debug_assert_eq3!(&sty1.idx, &sty2.idx, &Expr::nu());

                let bty = self.join_bty(&sty1.bty, &sty2.bty);
                let pred = if self.scope.has_free_vars(&sty2.pred) || sty1.pred != sty2.pred {
                    Expr::hole(HoleKind::Pred)
                } else {
                    sty1.pred.clone()
                };
                let sort = bty.sort();
                let ctor = Binder::bind_with_sort(SubsetTy::new(bty, Expr::nu(), pred), sort);
                GenericArg::Base(ctor)
            }
            (GenericArg::Lifetime(re1), GenericArg::Lifetime(_re2)) => {
                // TODO(nilehmann) loop_abstract_refinement.rs is triggering this assertion to fail
                // wee should fix it.
                // debug_assert_eq!(re1, _re2);
                GenericArg::Lifetime(*re1)
            }
            (GenericArg::Const(c1), GenericArg::Const(c2)) => {
                debug_assert_eq!(c1, c2);
                GenericArg::Const(c1.clone())
            }
            _ => tracked_span_bug!("unexpected generic args: `{arg1:?}` - `{arg2:?}`"),
        }
    }

    pub fn into_bb_env(self, kvar_gen: &mut KVarGen) -> BasicBlockEnv {
        let mut delegate = LocalHoister::default();
        let mut hoister = Hoister::with_delegate(&mut delegate).transparent();

        let mut bindings = self.bindings;
        bindings.fmap_mut(|ty| hoister.hoist(ty));

        BasicBlockEnv {
            // We are relying on all the types in `bindings` not having escaping bvars, otherwise
            // we would have to shift them in since we are creating a new binder.
            data: delegate.bind(|vars, preds| {
                // Replace all holes with a single fresh kvar on all parameters
                let mut constrs = preds
                    .into_iter()
                    .filter(|pred| !matches!(pred.kind(), ExprKind::Hole(HoleKind::Pred)))
                    .collect_vec();
                let kvar = kvar_gen.fresh(&[vars.clone()], self.scope.iter(), KVarEncoding::Conj);
                constrs.push(kvar);

                // Replace remaining holes by fresh kvars
                let mut kvar_gen = |binders: &[_], kind| {
                    debug_assert_eq!(kind, HoleKind::Pred);
                    let binders = std::iter::once(vars.clone())
                        .chain(binders.iter().cloned())
                        .collect_vec();
                    kvar_gen.fresh(&binders, self.scope.iter(), KVarEncoding::Conj)
                };
                bindings.fmap_mut(|binding| binding.replace_holes(&mut kvar_gen));

                BasicBlockEnvData { constrs: constrs.into(), bindings }
            }),
            scope: self.scope,
        }
    }
}

impl TypeVisitable for BasicBlockEnvData {
    fn visit_with<V: TypeVisitor>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy> {
        unimplemented!()
    }
}

impl TypeFoldable for BasicBlockEnvData {
    fn try_fold_with<F: FallibleTypeFolder>(
        &self,
        folder: &mut F,
    ) -> std::result::Result<Self, F::Error> {
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
                    cx.fmt_bound_vars(true, "for<", vars, "> ", f)?;
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

/// A very explicit representation of [`TypeEnv`] for debugging/tracing/serialization ONLY.
#[derive(Serialize, DebugAsJson)]
pub struct TypeEnvTrace(Vec<TypeEnvBind>);

#[derive(Serialize)]
struct TypeEnvBind {
    loc: String,
    kind: String,
    ty: String,
}

fn loc_string(local_names: &UnordMap<Local, Symbol>, loc: &Loc) -> Option<String> {
    if let Loc::Local(local) = loc {
        let name = local_names.get(local)?;
        return Some(format!("{}", name));
    }
    return Some(format!("{:?}", loc));
}

impl TypeEnvTrace {
    pub fn new(genv: GlobalEnv, local_names: &UnordMap<Local, Symbol>, env: &TypeEnv) -> Self {
        let mut bindings = vec![];
        let cx = PrettyCx::default_with_genv(genv);
        env.bindings
            .iter()
            .filter(|(_, binding)| !binding.ty.is_uninit())
            .sorted_by(|(loc1, _), (loc2, _)| loc1.cmp(loc2))
            .for_each(|(loc, binding)| {
                // filtering out bindings that do not correspond to source-level names
                if let Some(loc) = loc_string(local_names, loc) {
                    let kind = format!("{:?}", binding.kind);
                    let ty = WithCx::new(&cx, binding.ty.clone());
                    let ty = format!("{:?}", ty);
                    bindings.push(TypeEnvBind { loc, kind, ty });
                }
            });

        TypeEnvTrace(bindings)
    }
}
