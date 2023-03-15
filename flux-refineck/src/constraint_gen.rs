use std::{iter, slice};

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        self,
        evars::{EVarCxId, EVarSol, UnsolvedEvar},
        fold::TypeFoldable,
        BaseTy, BinOp, Binder, Const, Constraint, EVarGen, EarlyBinder, Expr, ExprKind, FnOutput,
        GenericArg, InferMode, Path, PolyFnSig, PolyVariant, PtrKind, Ref, RefKind, Sort,
        TupleTree, Ty, TyKind, Var,
    },
    rustc::mir::{BasicBlock, Place},
};
use itertools::{izip, Itertools};
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Variance;
use rustc_span::Span;

use crate::{
    checker::errors::CheckerErrKind,
    fixpoint_encoding::KVarEncoding,
    refine_tree::{RefineCtxt, Scope, Snapshot, UnpackFlags},
    type_env::TypeEnv,
};

pub struct ConstrGen<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'a, 'tcx>,
    kvar_gen: Box<dyn KVarGen + 'a>,
    span: Span,
}

pub(crate) struct Obligations {
    pub(crate) predicates: List<rty::Predicate>,
    /// Snapshot of the refinement subtree where the obligations should be checked
    pub(crate) snapshot: Snapshot,
}

pub trait KVarGen {
    fn fresh(&mut self, args: &[Sort], kind: KVarEncoding) -> Expr;
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

    pub(crate) fn check_pred(
        &self,
        rcx: &mut RefineCtxt,
        pred: impl Into<Expr>,
        reason: ConstrReason,
    ) {
        rcx.check_pred(pred, Tag::new(reason, self.span));
    }

    pub(crate) fn subtyping(
        &mut self,
        rcx: &mut RefineCtxt,
        ty1: &Ty,
        ty2: &Ty,
        reason: ConstrReason,
    ) {
        let mut infcx = self.infcx(rcx, reason);
        infcx.subtyping(rcx, ty1, ty2);
        rcx.replace_evars(&infcx.solve().unwrap());
    }

    pub(crate) fn check_fn_call(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        did: Option<DefId>,
        fn_sig: EarlyBinder<PolyFnSig>,
        substs: &[GenericArg],
        actuals: &[Ty],
    ) -> Result<(Binder<FnOutput>, Obligations), CheckerErrKind> {
        // HACK(nilehmann) This let us infer parameters under mutable references for the simple case
        // where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
        // to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
        // mutable references.
        let actuals = iter::zip(
            actuals,
            fn_sig
                .as_ref()
                .skip_binder()
                .fn_sig
                .as_ref()
                .skip_binder()
                .args(),
        )
        .map(|(actual, formal)| {
            if let (Ref!(RefKind::Mut, _), Ref!(RefKind::Mut, ty)) = (actual.kind(), formal.kind())
                   && let TyKind::Indexed(..) = ty.kind() {
                    rcx.unpack_with(actual, UnpackFlags::EXISTS_IN_MUT_REF)
                } else {
                    actual.clone()
                }
        })
        .collect_vec();

        let genv = self.genv;

        let mut infcx = self.infcx(rcx, ConstrReason::Call);

        // Replace holes in generic arguments with fresh kvars
        let snapshot = rcx.snapshot();
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(|sorts| infcx.fresh_kvar(sorts, KVarEncoding::Conj)))
            .collect_vec();

        // Generate fresh evars and kvars for refinement parameters
        let inst_fn_sig = fn_sig
            .subst_generics(&substs)
            .replace_bvars_with(|sort, kind| infcx.fresh_evars_or_kvar(sort, kind));

        // Check closure obligations
        let closure_obligs = if let Some(did) = did {
            mk_obligations(genv, did, &substs)?
        } else {
            List::from(vec![])
        };

        // Check requires predicates and collect type constraints
        let mut requires = FxHashMap::default();
        for constr in inst_fn_sig.requires() {
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
        for (actual, formal) in iter::zip(&actuals, inst_fn_sig.args()) {
            let rcx = &mut rcx.push_comment(format!("{actual:?} <: {formal:?}"));

            let (formal, pred) = formal.unconstr();
            infcx.check_pred(rcx, pred);
            match (actual.kind(), formal.kind()) {
                (TyKind::Ptr(PtrKind::Mut, path1), TyKind::Ptr(PtrKind::Mut, path2)) => {
                    let bound = requires[path2];
                    infcx.unify_exprs(&path1.to_expr(), &path2.to_expr(), false);
                    infcx.check_type_constr(rcx, env, path1, bound)?;
                }
                (TyKind::Ptr(PtrKind::Mut, path), Ref!(RefKind::Mut, bound)) => {
                    let ty =
                        env.block_with(rcx, &mut infcx.as_constr_gen(), path, bound.clone())?;
                    infcx.subtyping(rcx, &ty, bound);
                }
                (TyKind::Ptr(PtrKind::Shr, path), Ref!(RefKind::Shr, bound)) => {
                    let ty = env.block(rcx, &mut infcx.as_constr_gen(), path)?;
                    infcx.subtyping(rcx, &ty, bound);
                }
                _ => infcx.subtyping(rcx, actual, &formal),
            }
        }

        // Replace evars
        let evars_sol = infcx.solve()?;
        env.replace_evars(&evars_sol);
        rcx.replace_evars(&evars_sol);
        let output = inst_fn_sig.output().replace_evars(&evars_sol);

        Ok((output, Obligations::new(closure_obligs, snapshot)))
    }

    pub(crate) fn check_ret(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        output: &Binder<FnOutput>,
    ) -> Result<(), CheckerErrKind> {
        let ret_place_ty = env.lookup_place(rcx, self, Place::RETURN)?;

        let mut infcx = self.infcx(rcx, ConstrReason::Ret);

        let output = output
            .replace_bvar_with(|sort| infcx.fresh_evars_or_kvar(sort, sort.default_infer_mode()));

        infcx.subtyping(rcx, &ret_place_ty, &output.ret);
        for constraint in &output.ensures {
            infcx.check_constraint(rcx, env, constraint)?;
        }

        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(())
    }

    pub(crate) fn check_constructor(
        &mut self,
        rcx: &mut RefineCtxt,
        variant: EarlyBinder<PolyVariant>,
        substs: &[GenericArg],
        fields: &[Ty],
    ) -> Result<Ty, UnsolvedEvar> {
        // rn we are only calling `check_constructor` from path_tree when folding so we mark this
        // as a folding error.
        let mut infcx = self.infcx(rcx, ConstrReason::Fold);

        // Replace holes in generic arguments with fresh kvars
        let substs = substs
            .iter()
            .map(|arg| arg.replace_holes(|sorts| infcx.fresh_kvar(sorts, KVarEncoding::Conj)))
            .collect_vec();

        // Generate fresh evars and kvars for refinement parameters
        let variant = variant
            .subst_generics(&substs)
            .replace_bvar_with(|sort| infcx.fresh_evars_or_kvar(sort, sort.default_infer_mode()));

        // Check arguments
        for (actual, formal) in iter::zip(fields, variant.fields()) {
            infcx.subtyping(rcx, actual, formal);
        }

        // Replace evars
        let evars_sol = infcx.solve()?;
        rcx.replace_evars(&evars_sol);

        Ok(variant.ret.replace_evars(&evars_sol))
    }

    pub(crate) fn check_mk_array(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        args: &[Ty],
        arr_ty: Ty,
    ) -> Result<Ty, CheckerErrKind> {
        let mut infcx = self.infcx(rcx, ConstrReason::Other);

        let arr_ty = arr_ty.replace_holes(|sort| infcx.fresh_kvar(sort, KVarEncoding::Conj));

        let (arr_ty, pred) = arr_ty.unconstr();
        infcx.check_pred(rcx, pred);

        for ty in args {
            // TODO(nilehmann) We should share this logic with `check_fn_call`
            match (ty.kind(), arr_ty.kind()) {
                (TyKind::Ptr(PtrKind::Mut, path), Ref!(RefKind::Mut, bound)) => {
                    let ty =
                        env.block_with(rcx, &mut infcx.as_constr_gen(), path, bound.clone())?;
                    infcx.subtyping(rcx, &ty, bound);
                }
                (TyKind::Ptr(PtrKind::Shr, path), Ref!(RefKind::Shr, bound)) => {
                    let ty = env.block(rcx, &mut infcx.as_constr_gen(), path)?;
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

    fn fresh_kvar(&mut self, sorts: &[Sort], encoding: KVarEncoding) -> Expr {
        self.kvar_gen.fresh(sorts, encoding)
    }

    fn fresh_evars(&mut self, sort: &Sort) -> Expr {
        let cx = *self.scopes.last().unwrap().0;
        Expr::fold_sort(sort, |_| Expr::evar(self.evar_gen.fresh_in_cx(cx)))
    }

    fn fresh_evars_or_kvar(&mut self, sort: &Sort, kind: InferMode) -> Expr {
        match kind {
            InferMode::KVar => {
                let fsort = sort.expect_func();
                let input = fsort.input();
                Expr::abs(Binder::new(
                    self.fresh_kvar(slice::from_ref(input), KVarEncoding::Single),
                    input.clone(),
                ))
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
    ) -> Result<(), CheckerErrKind> {
        let actual_ty = env.lookup_path(rcx, &mut self.as_constr_gen(), path)?;
        self.subtyping(rcx, &actual_ty, ty);
        Ok(())
    }

    fn check_constraint(
        &mut self,
        rcx: &mut RefineCtxt,
        env: &mut TypeEnv,
        constraint: &Constraint,
    ) -> Result<(), CheckerErrKind> {
        let rcx = &mut rcx.branch();
        match constraint {
            Constraint::Type(path, ty) => self.check_type_constr(rcx, env, path, ty),
            Constraint::Pred(e) => {
                rcx.check_pred(e, self.tag);
                Ok(())
            }
        }
    }

    fn subtyping(&mut self, rcx: &mut RefineCtxt, ty1: &Ty, ty2: &Ty) {
        let rcx = &mut rcx.branch();

        match (ty1.kind(), ty2.kind()) {
            (TyKind::Exists(ty1), _) => {
                let ty1 = ty1.replace_bvar_with(|sort| rcx.define_vars(sort));
                self.subtyping(rcx, &ty1, ty2);
            }
            (TyKind::Constr(p1, ty1), _) => {
                rcx.assume_pred(p1);
                self.subtyping(rcx, ty1, ty2);
            }
            (_, TyKind::Exists(ty2)) => {
                self.push_scope(rcx);
                let ty2 = ty2.replace_bvar_with(|sort| self.fresh_evars(sort));
                self.subtyping(rcx, ty1, &ty2);
                self.pop_scope();
            }
            (TyKind::Indexed(bty1, idx1), TyKind::Indexed(bty2, idx2)) => {
                self.bty_subtyping(rcx, bty1, bty2);
                self.idx_subtyping(rcx, &idx1.expr, &idx2.expr, &idx2.is_binder);
            }
            (TyKind::Ptr(pk1, path1), TyKind::Ptr(pk2, path2)) => {
                debug_assert_eq!(pk1, pk2);
                debug_assert_eq!(path1, path2);
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
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
            (BaseTy::Param(param1), BaseTy::Param(param2)) => {
                debug_assert_eq!(param1, param2);
            }
            (BaseTy::Bool, BaseTy::Bool)
            | (BaseTy::Str, BaseTy::Str)
            | (BaseTy::Char, BaseTy::Char)
            | (BaseTy::RawPtr(_, _), BaseTy::RawPtr(_, _)) => {}
            (BaseTy::Closure(did1), BaseTy::Closure(did2)) if did1 == did2 => {}
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
                    Variance::Covariant => self.subtyping(rcx, ty1, ty2),
                    Variance::Invariant => {
                        self.subtyping(rcx, ty1, ty2);
                        self.subtyping(rcx, ty2, ty1);
                    }
                    Variance::Contravariant => self.subtyping(rcx, ty2, ty1),
                    Variance::Bivariant => {}
                }
            }
            (GenericArg::BaseTy(_), GenericArg::BaseTy(_)) => {
                tracked_span_bug!("sgeneric argument subtyping for base types is not implemented");
            }
            (GenericArg::Lifetime, GenericArg::Lifetime) => {}
            _ => tracked_span_bug!("incompatible generic args: `{arg1:?}` `{arg2:?}"),
        };
    }

    fn idx_subtyping(
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
                    self.idx_subtyping(rcx, e1, e2, is_binder);
                }
            }
            (ExprKind::Abs(p1), ExprKind::Abs(p2)) => {
                self.pred_subtyping(rcx, p1, p2);
            }
            (_, ExprKind::Abs(p)) => {
                self.pred_subtyping(rcx, &e1.eta_expand_abs(p.sort()), p);
            }
            (ExprKind::Abs(p), _) => {
                self.unify_exprs(e1, e2, *is_binder.expect_leaf());
                self.pred_subtyping(rcx, p, &e2.eta_expand_abs(p.sort()));
            }
            _ => {
                self.unify_exprs(e1, e2, *is_binder.expect_leaf());
                rcx.check_pred(Expr::binary_op(BinOp::Eq, e1, e2), self.tag);
            }
        }
    }

    fn pred_subtyping(&mut self, rcx: &mut RefineCtxt, p1: &Binder<Expr>, p2: &Binder<Expr>) {
        debug_assert_eq!(p1.sort(), p2.sort());
        let vars = rcx.define_vars(p1.sort());
        let p1 = p1.replace_bvar(&vars);
        let p2 = p2.replace_bvar(&vars);
        rcx.check_impl(&p1, &p2, self.tag);
        rcx.check_impl(&p2, &p1, self.tag);
    }

    fn unify_exprs(&mut self, e1: &Expr, e2: &Expr, replace: bool) {
        if let ExprKind::Var(Var::EVar(evar)) = e2.kind()
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

impl Obligations {
    fn new(predicates: List<rty::Predicate>, snapshot: Snapshot) -> Self {
        Self { predicates, snapshot }
    }
}

fn mk_obligations(
    genv: &GlobalEnv<'_, '_>,
    did: DefId,
    substs: &[GenericArg],
) -> Result<List<rty::Predicate>, CheckerErrKind> {
    Ok(genv.predicates_of(did)?.predicates().subst_generics(substs))
}

impl<F> KVarGen for F
where
    F: FnMut(&[Sort], KVarEncoding) -> Expr,
{
    fn fresh(&mut self, sorts: &[Sort], kind: KVarEncoding) -> Expr {
        (self)(sorts, kind)
    }
}

impl<'a> KVarGen for &mut (dyn KVarGen + 'a) {
    fn fresh(&mut self, sorts: &[Sort], kind: KVarEncoding) -> Expr {
        (**self).fresh(sorts, kind)
    }
}

impl<'a> KVarGen for Box<dyn KVarGen + 'a> {
    fn fresh(&mut self, sorts: &[Sort], kind: KVarEncoding) -> Expr {
        (**self).fresh(sorts, kind)
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
