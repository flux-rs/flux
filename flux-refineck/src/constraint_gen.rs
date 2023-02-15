use std::iter;

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::{GlobalEnv, OpaqueStructErr, Variance},
    rty::{
        evars::{EVarCxId, EVarSol, UnsolvedEvar},
        fold::TypeFoldable,
        BaseTy, BinOp, Binder, Const, Constraint, EVarGen, Expr, ExprKind, FnOutput, GenericArg,
        Index, InferMode, Path, PolySig, PolyVariant, PtrKind, Ref, RefKind, Sort, TupleTree, Ty,
        TyKind,
    },
    rustc::{
        self,
        mir::{BasicBlock, Place},
    },
};
use itertools::{izip, Itertools};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::FxHashMap;
use rustc_span::Span;

use crate::{
    checker::errors::CheckerError,
    fixpoint::{KVarEncoding, KVarGen},
    refine_tree::{RefineCtxt, Scope, UnpackFlags},
    type_env::TypeEnv,
};

pub struct ConstrGen<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'a, 'tcx>,
    kvar_gen: Box<dyn KVarGen + 'a>,
    span: Span,
}

struct InferCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    kvar_gen: &'a mut (dyn KVarGen + 'a),
    evar_gen: EVarGen,
    tag: Tag,
    scopes: FxIndexMap<EVarCxId, Scope>,
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Tag {
    pub reason: ConstrReason,
    pub span: Span,
}

impl Tag {
    pub fn new(reason: ConstrReason, span: Span) -> Self {
        Self { reason, span }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum ConstrReason {
    Call,
    Assign,
    Ret,
    Fold,
    Assert(&'static str),
    Div,
    Rem,
    Goto(BasicBlock),
    Overflow,
    Other,
}

impl<'a, 'tcx> ConstrGen<'a, 'tcx> {
    pub fn new<G>(genv: &'a GlobalEnv<'a, 'tcx>, kvar_gen: G, span: Span) -> Self
    where
        G: KVarGen + 'a,
    {
        ConstrGen { genv, kvar_gen: Box::new(kvar_gen), span }
    }

    pub fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Expr>, reason: ConstrReason) {
        rcx.check_pred(pred, Tag::new(reason, self.span));
    }

    pub fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty, reason: ConstrReason) {
        let mut infcx = self.infcx(rcx, reason);
        infcx.subtyping(rcx, ty1, ty2);
        rcx.replace_evars(&infcx.solve().unwrap());
    }

    pub fn check_fn_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        fn_sig: &PolySig,
        substs: &[GenericArg],
        actuals: &[Ty],
    ) -> Result<Binder<FnOutput>, CheckerError> {
        // HACK(nilehmann) This let us infer parameters under mutable references for the simple case
        // where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
        // to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
        // mutable references.
        let actuals = iter::zip(actuals, fn_sig.fn_sig.as_ref().skip_binders().args())
            .map(|(actual, formal)| {
                if let (Ref!(RefKind::Mut, _), Ref!(RefKind::Mut, ty)) = (actual.kind(), formal.kind())
                   && let TyKind::Indexed(..) = ty.kind() {
                    rcx.unpack_with(actual, UnpackFlags::EXISTS_IN_MUT_REF)
                } else {
                    actual.clone()
                }
            })
            .collect_vec();

        let mut infcx = self.infcx(rcx, ConstrReason::Call);

        // Replace holes in generic arguments with fresh kvars
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(&mut |sort| infcx.fresh_kvar(sort, KVarEncoding::Conj)))
            .collect_vec();

        // println!("\n{fn_sig:?}");
        // Generate fresh evars and kvars for refinement parameters
        let fn_sig = fn_sig
            .replace_generics(&substs)
            .replace_bvars_with(|sort, kind| infcx.fresh_evar_or_kvar(sort, kind));
        // println!("{fn_sig:?}");

        // Check requires predicates and collect type constraints
        let mut requires = FxHashMap::default();
        for constr in fn_sig.requires() {
            match constr {
                Constraint::Type(path, ty) => {
                    requires.insert(path.clone(), ty);
                }
                Constraint::Pred(pred) => {
                    infcx.check_pred(rcx, pred);
                }
            }
        }

        // Check arguments
        for (actual, formal) in iter::zip(&actuals, fn_sig.args()) {
            let (formal, pred) = formal.unconstr();
            infcx.check_pred(rcx, pred);
            match (actual.kind(), formal.kind()) {
                (TyKind::Ptr(PtrKind::Mut, path1), TyKind::Ptr(PtrKind::Mut, path2)) => {
                    let bound = requires[path2];
                    infcx.unify_exprs(&path1.to_expr(), &path2.to_expr(), false);
                    infcx.check_type_constr(rcx, env, path1, bound)?;
                }
                (TyKind::Ptr(PtrKind::Mut, path), Ref!(RefKind::Mut, bound)) => {
                    let ty = env.block_with(rcx, &mut infcx.as_constr_gen(), path, bound.clone());
                    infcx.subtyping(rcx, &ty, bound);
                }
                (TyKind::Ptr(PtrKind::Shr, path), Ref!(RefKind::Shr, bound)) => {
                    let ty = env.block(rcx, &mut infcx.as_constr_gen(), path);
                    infcx.subtyping(rcx, &ty, bound);
                }
                _ => infcx.subtyping(rcx, actual, &formal),
            }
        }

        // Replace evars
        let evars_sol = infcx.solve()?;
        env.replace_evars(&evars_sol);
        rcx.replace_evars(&evars_sol);
        let output = fn_sig.output().replace_evars(&evars_sol);

        Ok(output)
    }

    pub fn check_ret(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        output: &Binder<FnOutput>,
    ) -> Result<(), CheckerError> {
        let ret_place_ty = env
            .lookup_place(rcx, self, Place::RETURN)
            .map_err(CheckerError::from)?;

        let mut infcx = self.infcx(rcx, ConstrReason::Ret);

        let output = output
            .replace_bvars_with(|sort| infcx.fresh_evar_or_kvar(sort, sort.default_infer_mode()));

        infcx.subtyping(rcx, &ret_place_ty, &output.ret);
        for constraint in &output.ensures {
            infcx.check_constraint(rcx, env, constraint)?;
        }

        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(())
    }

    pub fn check_constructor(
        &mut self,
        rcx: &mut RefineCtxt,
        variant: &PolyVariant,
        substs: &[GenericArg],
        fields: &[Ty],
    ) -> Result<Ty, UnsolvedEvar> {
        // rn we are only calling `check_constructor` from path_tree when folding so we mark this
        // as a folding error.
        let mut infcx = self.infcx(rcx, ConstrReason::Fold);

        // Replace holes in generic arguments with fresh kvars
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(&mut |sorts| infcx.fresh_kvar(sorts, KVarEncoding::Conj)))
            .collect_vec();

        // Generate fresh evars and kvars for refinement parameters
        let variant = variant
            .replace_generics(&substs)
            .replace_bvars_with(|sort| infcx.fresh_evar_or_kvar(sort, sort.default_infer_mode()));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            infcx.subtyping(rcx, actual, formal);
        }

        // Replace evars
        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(variant.ret.replace_evars(&evars_sol))
    }

    pub fn check_mk_array(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        args: &[Ty],
        arr_ty: &rustc::ty::Ty,
    ) -> Result<Ty, CheckerError> {
        let genv = self.genv;

        let mut infcx = self.infcx(rcx, ConstrReason::Other);

        let arr_ty = genv
            .refine_with_holes(arr_ty)
            .replace_holes(&mut |sort| infcx.fresh_kvar(sort, KVarEncoding::Conj));

        for ty in args {
            // TODO(nilehmann) We should share this logic with `check_fn_call`
            match (ty.kind(), arr_ty.kind()) {
                (TyKind::Ptr(PtrKind::Mut, path), Ref!(RefKind::Mut, bound)) => {
                    let ty = env.block_with(rcx, &mut infcx.as_constr_gen(), path, bound.clone());
                    infcx.subtyping(rcx, &ty, bound);
                }
                (TyKind::Ptr(PtrKind::Shr, path), Ref!(RefKind::Shr, bound)) => {
                    let ty = env.block(rcx, &mut infcx.as_constr_gen(), path);
                    infcx.subtyping(rcx, &ty, bound);
                }
                _ => infcx.subtyping(rcx, ty, &arr_ty),
            }
        }
        rcx.replace_evars(&infcx.solve()?);

        Ok(Ty::array(arr_ty, Const { val: args.len() }))
    }

    fn infcx(&mut self, rcx: &RefineCtxt, reason: ConstrReason) -> InferCtxt<'_, 'tcx> {
        InferCtxt::new(self.genv, rcx, &mut self.kvar_gen, Tag::new(reason, self.span))
    }
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        rcx: &RefineCtxt,
        kvar_gen: &'a mut (dyn KVarGen + 'a),
        tag: Tag,
    ) -> Self {
        let mut evar_gen = EVarGen::new();
        let mut scopes = FxIndexMap::default();
        scopes.insert(evar_gen.new_ctxt(), rcx.scope());
        Self { genv, kvar_gen, evar_gen, tag, scopes }
    }

    fn push_scope(&mut self, rcx: &RefineCtxt) {
        self.scopes.insert(self.evar_gen.new_ctxt(), rcx.scope());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn fresh_kvar(&mut self, sort: Sort, encoding: KVarEncoding) -> Binder<Expr> {
        self.kvar_gen.fresh(sort, encoding)
    }

    fn fresh_evars(&mut self, sort: &Sort) -> Expr {
        let cx = *self.scopes.last().unwrap().0;
        Expr::fold_sort(sort, |_, _| Expr::evar(self.evar_gen.fresh_in_cx(cx)))
    }

    fn fresh_evar_or_kvar(&mut self, sort: &Sort, kind: InferMode) -> Expr {
        match kind {
            InferMode::KVar => {
                let fsort = sort.expect_func();
                Expr::abs(self.fresh_kvar(Sort::tuple(fsort.inputs()), KVarEncoding::Single))
            }
            InferMode::EVar => self.fresh_evars(sort),
        }
    }

    fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Expr>) {
        rcx.check_pred(pred, self.tag);
    }

    fn as_constr_gen<'b>(&'b mut self) -> ConstrGen<'b, 'tcx> {
        ConstrGen::new(self.genv, &mut *self.kvar_gen, self.tag.span)
    }

    fn check_type_constr(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        path: &Path,
        ty: &Ty,
    ) -> Result<(), OpaqueStructErr> {
        let actual_ty = env.lookup_path(rcx, &mut self.as_constr_gen(), path)?;
        self.subtyping(rcx, &actual_ty, ty);
        Ok(())
    }

    fn check_constraint(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        constraint: &Constraint,
    ) -> Result<(), OpaqueStructErr> {
        let rcx = &mut rcx.breadcrumb();
        match constraint {
            Constraint::Type(path, ty) => self.check_type_constr(rcx, env, path, ty),
            Constraint::Pred(e) => {
                rcx.check_pred(e, self.tag);
                Ok(())
            }
        }
    }

    fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) {
        // println!("{ty1:?} <: {ty2:?}");
        let rcx = &mut rcx.breadcrumb();

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Exists(ty1), _) => {
                let ty1 = ty1.replace_bvars_with(|sort| rcx.define_vars(sort));
                self.subtyping(rcx, &ty1, ty2);
            }
            (TyKind::Constr(p1, ty1), _) => {
                rcx.assume_pred(p1);
                self.subtyping(rcx, ty1, ty2);
            }
            (_, TyKind::Exists(ty2)) => {
                self.push_scope(rcx);
                let ty2 = ty2.replace_bvars_with(|sort| self.fresh_evars(sort));
                self.subtyping(rcx, ty1, &ty2);
                self.pop_scope();
            }
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                self.bty_subtyping(rcx, bty1, bty2);
                self.index_subtyping(rcx, idx1, idx2);
            }
            (TyKind::Ptr(pk1, path1), TyKind::Ptr(pk2, path2)) => {
                debug_assert_eq!(pk1, pk2);
                debug_assert_eq!(path1, path2);
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
            }
            (TyKind::Param(param1), TyKind::Param(param2)) => {
                debug_assert_eq!(param1, param2);
            }
            (_, TyKind::Constr(p2, ty2)) => {
                rcx.check_pred(p2, self.tag);
                self.subtyping(rcx, ty1, ty2);
            }
            _ => tracked_span_bug!("`{ty1:?}` <: `{ty2:?}`"),
        }
    }

    fn bty_subtyping(&mut self, rcx: &mut RefineCtxt, bty1: &BaseTy, bty2: &BaseTy) {
        match (bty1, bty2) {
            (BaseTy::Int(int_ty1), BaseTy::Int(int_ty2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
            }
            (BaseTy::Uint(uint_ty1), BaseTy::Uint(uint_ty2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
            }
            (BaseTy::Adt(adt1, substs1), BaseTy::Adt(adt2, substs2)) => {
                debug_assert_eq!(adt1.def_id(), adt2.def_id());
                debug_assert_eq!(substs1.len(), substs2.len());
                let variances = self.genv.variances_of(adt1.def_id());
                for (variance, ty1, ty2) in izip!(variances, substs1.iter(), substs2.iter()) {
                    self.generic_arg_subtyping(rcx, *variance, ty1, ty2);
                }
            }
            (BaseTy::Float(float_ty1), BaseTy::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
            }

            (BaseTy::Slice(ty1), BaseTy::Slice(ty2)) => {
                self.subtyping(rcx, ty1, ty2);
            }
            (BaseTy::Ref(RefKind::Mut, ty1), BaseTy::Ref(RefKind::Mut, ty2)) => {
                self.subtyping(rcx, ty1, ty2);
                self.subtyping(rcx, ty2, ty1);
            }
            (BaseTy::Ref(RefKind::Shr, ty1), BaseTy::Ref(RefKind::Shr, ty2)) => {
                self.subtyping(rcx, ty1, ty2);
            }
            (BaseTy::Tuple(tys1), BaseTy::Tuple(tys2)) => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.subtyping(rcx, ty1, ty2);
                }
            }
            (BaseTy::Array(ty1, len1), BaseTy::Array(ty2, len2)) => {
                debug_assert_eq!(len1.val, len2.val);
                self.subtyping(rcx, ty1, ty2);
            }
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char)
            | (BaseTy::RawPtr(_, _), BaseTy::RawPtr(_, _)) => {}
            _ => {
                tracked_span_bug!("unexpected base types: `{:?}` and `{:?}`", bty1, bty2,);
            }
        }
    }

    fn generic_arg_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        variance: Variance,
        arg1: &GenericArg,
        arg2: &GenericArg,
    ) {
        match (arg1, arg2) {
            (GenericArg::Ty(ty1), GenericArg::Ty(ty2)) => {
                match variance {
                    rustc_middle::ty::Variance::Covariant => self.subtyping(rcx, ty1, ty2),
                    rustc_middle::ty::Variance::Invariant => {
                        self.subtyping(rcx, ty1, ty2);
                        self.subtyping(rcx, ty2, ty1);
                    }
                    rustc_middle::ty::Variance::Contravariant => self.subtyping(rcx, ty2, ty1),
                    rustc_middle::ty::Variance::Bivariant => {}
                }
            }
            (GenericArg::Lifetime, GenericArg::Lifetime) => {}
            _ => tracked_span_bug!("incompatible generic args: `{arg1:?}` `{arg2:?}"),
        };
    }

    fn index_subtyping(&mut self, rcx: &mut RefineCtxt, idx1: &Index, idx2: &Index) {
        self.expr_subtyping(rcx, &idx1.expr, &idx2.expr, &idx2.is_binder);
    }

    fn expr_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        e1: &Expr,
        e2: &Expr,
        is_binder: &TupleTree<bool>,
    ) {
        if e1 == e2 {
            return;
        }
        match (e1.kind(), e2.kind()) {
            (ExprKind::Tuple(tup1), ExprKind::Tuple(tup2)) => {
                debug_assert_eq!(tup1.len(), tup2.len());

                for (e1, e2, is_binder) in izip!(tup1, tup2, is_binder.split()) {
                    self.expr_subtyping(rcx, e1, e2, is_binder);
                }
            }
            (ExprKind::Abs(abs1), ExprKind::Abs(abs2)) => {
                debug_assert_eq!(abs1.sort(), abs2.sort());
                let vars = rcx.define_vars(abs1.sort());
                let pred1 = abs1.replace_bvars(&vars);
                let pred2 = abs2.replace_bvars(&vars);
                rcx.check_impl(&pred1, &pred2, self.tag);
                rcx.check_impl(pred2, pred1, self.tag);
            }
            (_, ExprKind::Abs(abs)) => {
                let vars = rcx.define_vars(abs.sort());
                let pred1 = Expr::app(e1, vars.as_tuple().to_vec());
                let pred2 = abs.replace_bvars(&vars);
                rcx.check_impl(&pred1, &pred2, self.tag);
                rcx.check_impl(pred2, pred1, self.tag);
            }
            (ExprKind::Abs(abs), _) => {
                self.unify_exprs(e1, e2, *is_binder.expect_leaf());
                let vars = rcx.define_vars(abs.sort());
                let pred1 = abs.replace_bvars(&vars);
                let pred2 = Expr::app(e2, vars.as_tuple().to_vec());
                rcx.check_impl(&pred1, &pred2, self.tag);
                rcx.check_impl(pred2, pred1, self.tag);
            }
            _ => {
                self.unify_exprs(e1, e2, *is_binder.expect_leaf());
                rcx.check_pred(Expr::binary_op(BinOp::Eq, e1, e2), self.tag);
            }
        }
    }

    fn unify_exprs(&mut self, e1: &Expr, e2: &Expr, replace: bool) {
        if let ExprKind::EVar(evar) = e2.kind()
           && let scope = &self.scopes[&evar.cx()]
           && !scope.has_free_vars(e1)
        {
            self.evar_gen.unify(*evar, e1, replace);
        }
    }

    fn solve(self) -> Result<EVarSol, UnsolvedEvar> {
        self.evar_gen.solve()
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;

    use super::*;

    impl Pretty for Tag {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} at {:?}", ^self.reason, self.span)
        }
    }

    impl_debug_with_default_cx!(Tag);
}
