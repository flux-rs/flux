use std::iter;

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::{GlobalEnv, OpaqueStructErr, Variance},
    intern::List,
    rty::{
        evars::{EVarCxId, EVarSol, UnsolvedEvar},
        fold::TypeFoldable,
        BaseTy, BinOp, Binders, Const, Constraint, EVar, EVarGen, Expr, ExprKind, FnOutput,
        GenericArg, InferMode, Path, PolySig, PolyVariant, PtrKind, RefKind, RefineArg, Sort, Ty,
        TyKind, VariantRet,
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
    span: Option<Span>, // tag: Tag,
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
    pub span: Option<Span>,
}

impl Tag {
    pub fn new(reason: ConstrReason, span: Option<Span>) -> Self {
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
    pub fn new<G>(genv: &'a GlobalEnv<'a, 'tcx>, kvar_gen: G, span: Option<Span>) -> Self
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
    ) -> Result<Binders<FnOutput>, CheckerError> {
        // HACK(nilehmann) This let us infer parameters under mutable references for the simple case
        // where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
        // to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
        // mutable references.
        let actuals = iter::zip(actuals, fn_sig.fn_sig.as_ref().skip_binders().args())
            .map(|(actual, formal)| {
                if let (TyKind::Ref(RefKind::Mut, _), TyKind::Ref(RefKind::Mut, ty)) = (actual.kind(), formal.kind())
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
            .map(|arg| arg.replace_holes(&mut |sorts| infcx.fresh_kvar(sorts, KVarEncoding::Conj)))
            .collect_vec();

        // Generate fresh evars and kvars for refinement parameters
        let fn_sig = fn_sig
            .replace_generic_args(&substs)
            .replace_bvars_with(|sort, kind| infcx.fresh_evar_or_kvar(sort, kind));

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
                (TyKind::Ptr(PtrKind::Mut, path), TyKind::Ref(RefKind::Mut, bound)) => {
                    let ty = env.block_with(path, bound.clone(), false);
                    infcx.subtyping(rcx, &ty, bound);
                }
                (TyKind::Ptr(PtrKind::Shr, path), TyKind::Ref(RefKind::Shr, bound)) => {
                    let ty = env.block(path, false);
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
        output: &Binders<FnOutput>,
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
    ) -> Result<VariantRet, UnsolvedEvar> {
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
            .replace_generic_args(&substs)
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

        let arr_ty =
            genv.refine_ty(arr_ty, &mut |sorts| infcx.fresh_kvar(sorts, KVarEncoding::Conj));

        for ty in args {
            // TODO(nilehmann) We should share this logic with `check_fn_call`
            match (ty.kind(), arr_ty.kind()) {
                (TyKind::Ptr(PtrKind::Mut, path), TyKind::Ref(RefKind::Mut, bound)) => {
                    let ty = env.block_with(path, bound.clone(), false);
                    infcx.subtyping(rcx, &ty, bound);
                }
                (TyKind::Ptr(PtrKind::Shr, path), TyKind::Ref(RefKind::Shr, bound)) => {
                    let ty = env.block(path, false);
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

    fn fresh_kvar(&mut self, sorts: &[Sort], encoding: KVarEncoding) -> Binders<Expr> {
        self.kvar_gen.fresh(sorts, encoding)
    }

    fn fresh_evar(&mut self) -> EVar {
        let cx = self.scopes.last().unwrap().0;
        self.evar_gen.fresh_in_cx(*cx)
    }

    fn fresh_evar_or_kvar(&mut self, sort: &Sort, kind: InferMode) -> RefineArg {
        match kind {
            InferMode::KVar => {
                let fsort = sort.as_func();
                RefineArg::Abs(self.fresh_kvar(fsort.inputs(), KVarEncoding::Single))
            }
            InferMode::EVar => RefineArg::Expr(Expr::evar(self.fresh_evar())),
        }
    }

    fn check_pred(&self, rcx: &mut RefineCtxt, pred: impl Into<Expr>) {
        rcx.check_pred(pred, self.tag);
    }

    fn check_type_constr(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        path: &Path,
        ty: &Ty,
    ) -> Result<(), OpaqueStructErr> {
        let actual_ty = {
            let gen = &mut ConstrGen::new(self.genv, &mut *self.kvar_gen, self.tag.span);
            env.lookup_path(rcx, gen, path)?
        };
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
        let rcx = &mut rcx.breadcrumb();
        if let TyKind::Exists(exists) = ty1.kind() {
            let exists = exists.replace_bvars_with_fresh_fvars(|sort| rcx.define_var(sort));
            rcx.assume_pred(exists.pred);
            self.subtyping(rcx, &Ty::indexed(exists.bty, exists.args), ty2);
            return;
        }

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, idxs1), TyKind::Indexed(bty2, idxs2)) => {
                self.bty_subtyping(rcx, bty1, bty2);
                for (i, (arg1, arg2)) in iter::zip(idxs1.args(), idxs2.args()).enumerate() {
                    self.refine_arg_subtyping(rcx, arg1, arg2, idxs2.is_binder(i));
                }
            }
            (TyKind::Indexed(..), TyKind::Exists(exists)) => {
                self.push_scope(rcx);
                let exists =
                    exists.replace_bvars_with(|_| RefineArg::Expr(Expr::evar(self.fresh_evar())));
                rcx.check_pred(exists.pred, self.tag);
                self.subtyping(rcx, ty1, &Ty::indexed(exists.bty, exists.args));
                self.pop_scope();
            }
            (TyKind::Ptr(pk1, path1), TyKind::Ptr(pk2, path2)) => {
                debug_assert_eq!(pk1, pk2);
                debug_assert_eq!(path1, path2);
            }
            (TyKind::Ref(RefKind::Mut, ty1), TyKind::Ref(RefKind::Mut, ty2)) => {
                self.subtyping(rcx, ty1, ty2);
                self.subtyping(rcx, ty2, ty1);
            }
            (TyKind::Ref(RefKind::Shr, ty1), TyKind::Ref(RefKind::Shr, ty2)) => {
                self.subtyping(rcx, ty1, ty2);
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
            }
            (TyKind::Param(param1), TyKind::Param(param2)) => {
                debug_assert_eq!(param1, param2);
            }
            (TyKind::Tuple(tys1), TyKind::Tuple(tys2)) => {
                debug_assert_eq!(tys1.len(), tys2.len());
                for (ty1, ty2) in iter::zip(tys1, tys2) {
                    self.subtyping(rcx, ty1, ty2);
                }
            }
            (TyKind::Array(ty1, len1), TyKind::Array(ty2, len2)) => {
                debug_assert_eq!(len1.val, len2.val);
                self.subtyping(rcx, ty1, ty2);
            }
            (_, TyKind::Constr(p2, ty2)) => {
                rcx.check_pred(p2, self.tag);
                self.subtyping(rcx, ty1, ty2);
            }
            (TyKind::Constr(p1, ty1), _) => {
                rcx.assume_pred(p1);
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
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char) => {}
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

    fn refine_arg_subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        arg1: &RefineArg,
        arg2: &RefineArg,
        is_binder: bool,
    ) {
        if arg1 == arg2 {
            return;
        }
        self.unify_args(arg1, arg2, is_binder);
        match (arg1, arg2) {
            (RefineArg::Expr(e1), RefineArg::Expr(e2)) => {
                rcx.check_pred(Expr::binary_op(BinOp::Eq, e1, e2), self.tag);
            }
            (RefineArg::Abs(abs1), RefineArg::Abs(abs2)) => {
                debug_assert_eq!(abs1.params(), abs2.params());
                let args = rcx
                    .define_vars(abs1.params())
                    .into_iter()
                    .map(|var| RefineArg::Expr(var.into()))
                    .collect_vec();
                let pred1 = abs1.replace_bvars(&args);
                let pred2 = abs2.replace_bvars(&args);
                rcx.check_impl(&pred1, &pred2, self.tag);
                rcx.check_impl(pred2, pred1, self.tag);
            }
            (RefineArg::Expr(expr), RefineArg::Abs(abs))
            | (RefineArg::Abs(abs), RefineArg::Expr(expr)) => {
                if let Option::Some(var) = expr.to_var() {
                    let args = rcx
                        .define_vars(abs.params())
                        .into_iter()
                        .map(Expr::from)
                        .collect_vec();
                    let pred1 = Expr::app(var, List::from(&args[..]));
                    let args = args.into_iter().map(RefineArg::from).collect_vec();
                    let pred2 = abs.replace_bvars(&args);
                    rcx.check_impl(&pred1, &pred2, self.tag);
                    rcx.check_impl(pred2, pred1, self.tag);
                } else {
                    tracked_span_bug!(
                        "invalid refinement argument subtyping `{arg1:?}` - `{arg2:?}`"
                    );
                }
            }
        }
    }

    fn unify_args(&mut self, arg1: &RefineArg, arg2: &RefineArg, replace: bool) {
        if let RefineArg::Expr(e) = arg2
           && let ExprKind::EVar(evar) = e.kind()
           && let scope = &self.scopes[&evar.cx()]
           && !scope.has_free_vars(arg1)
        {
            self.evar_gen.unify(*evar, arg1, replace);
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
            w!("{:?}", ^self.reason)?;
            if let Some(span) = self.span {
                w!(" at {:?}", span)?;
            }
            Ok(())
        }
    }

    impl_debug_with_default_cx!(Tag);
}
