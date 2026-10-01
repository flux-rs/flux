//! Subtyping between function signatures.
//!
//! This is used to check, e.g., that the signature of a trait method's implementation is a subtype
//! of the trait method's signature, that a closure satisfies an `Fn` trait obligation, or that a fn
//! pointer can be used where another fn pointer is expected.

use std::iter;

use flux_middle::{
    queries::QueryErr,
    rty::{
        self, BaseTy, EarlyBinder, Expr, Mutability, Path, PolyFnSig, PtrKind, Ty, TyKind,
        fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};
use itertools::{Itertools, izip};
use rustc_hir::def_id::DefId;
use rustc_span::Span;

use crate::{
    infer::{ConstrReason, InferCtxt, InferResult, LocEnv, SubtypeReason},
    projections::NormalizeExt as _,
};

/// `SubFn` lets us reuse _most_ of the same code for `check_fn_subtyping` for both the case where
/// we have an early-bound function signature (e.g., for a trait method???) and versions without,
/// e.g. a plain closure against its FnTraitPredicate obligation.
#[derive(Debug)]
pub enum SubFn {
    Poly(DefId, EarlyBinder<rty::PolyFnSig>, rty::GenericArgs),
    Mono(rty::PolyFnSig),
}

impl SubFn {
    pub fn poly_sig(&self) -> &rty::PolyFnSig {
        match self {
            SubFn::Poly(_, sig, _) => sig.skip_binder_ref(),
            SubFn::Mono(sig) => sig,
        }
    }
}

/// The function `check_fn_subtyping` does a function subtyping check between
/// the sub-type (T_f) corresponding to the type of `def_id` @ `args` and the
/// super-type (T_g) corresponding to the `oblig_sig`. This subtyping is handled
/// as akin to the code
///
///   T_f := (S1,...,Sn) -> S
///   T_g := (T1,...,Tn) -> T
///   T_f <: T_g
///
///  fn g(x1:T1,...,xn:Tn) -> T {
///      f(x1,...,xn)
///  }
///
/// The `env` should be empty: it is used to hold the locations of the strong references in the
/// signatures.
pub fn check_fn_subtyping(
    infcx: &mut InferCtxt,
    env: &mut impl LocEnv,
    sub_sig: SubFn,
    super_sig: &rty::PolyFnSig,
    span: Span,
) -> InferResult {
    let mut infcx = infcx.branch();
    let mut infcx = infcx.at(span);
    let tcx = infcx.genv.tcx();

    let super_sig = super_sig
        .try_replace_bound_vars(
            |_| Ok::<_, QueryErr>(rty::ReErased),
            |sort, _, kind| {
                let sort =
                    sort.deeply_normalize_sorts(infcx.def_id, infcx.genv, infcx.region_infcx)?;
                Ok(Expr::fvar(infcx.define_bound_reft_var(&sort, kind)))
            },
        )?
        .deeply_normalize(&mut infcx)?;

    // 1. Unpack `T_g` input types
    let actuals = super_sig
        .inputs()
        .iter()
        .map(|ty| infcx.unpack(ty))
        .collect_vec();

    let actuals = unfold_local_ptrs(&mut infcx, env, sub_sig.poly_sig(), &actuals)?;
    let actuals = infer_under_mut_ref_hack(&mut infcx, &actuals[..], sub_sig.poly_sig());

    let output = infcx.ensure_resolved_evars(|infcx| {
        // 2. Fresh names for `T_f` refine-params / Instantiate fn_def_sig and normalize it
        // in subtyping_mono, skip next two steps...
        let sub_sig = match sub_sig {
            SubFn::Poly(def_id, early_sig, sub_args) => {
                let refine_args = infcx.instantiate_refine_args(def_id, &sub_args)?;
                early_sig.instantiate(tcx, &sub_args, &refine_args)
            }
            SubFn::Mono(sig) => sig,
        };
        // ... jump right here.
        let sub_sig = sub_sig
            .try_replace_bound_vars(
                |_| Ok::<_, QueryErr>(rty::ReErased),
                |sort, mode, _| {
                    let sort =
                        sort.deeply_normalize_sorts(infcx.def_id, infcx.genv, infcx.region_infcx)?;
                    Ok(infcx.fresh_infer_var(&sort, mode))
                },
            )?
            .deeply_normalize(infcx)?;

        // 3. INPUT subtyping (g-input <: f-input)
        for requires in super_sig.requires() {
            infcx.assume_pred(requires);
        }
        infcx.check_pred(
            Expr::implies(super_sig.no_panic(), sub_sig.no_panic()),
            ConstrReason::Subtype(SubtypeReason::Input),
        );
        for (actual, formal) in iter::zip(actuals, sub_sig.inputs()) {
            let reason = ConstrReason::Subtype(SubtypeReason::Input);
            infcx.subtyping_with_env(env, &actual, formal, reason)?;
        }
        // we check the requires AFTER the actual-formal subtyping as the above may unfold stuff in
        // the actuals
        for requires in sub_sig.requires() {
            let reason = ConstrReason::Subtype(SubtypeReason::Requires);
            infcx.check_pred(requires, reason);
        }

        Ok(sub_sig.output())
    })?;

    let output = infcx
        .fully_resolve_evars(&output)
        .replace_bound_refts_with(|sort, _, kind| {
            Expr::fvar(infcx.define_bound_reft_var(sort, kind))
        });

    // 4. OUTPUT subtyping (f_out <: g_out)
    infcx.ensure_resolved_evars(|infcx| {
        let super_output = super_sig
            .output()
            .replace_bound_refts_with(|sort, mode, _| infcx.fresh_infer_var(sort, mode));
        let reason = ConstrReason::Subtype(SubtypeReason::Output);
        infcx.subtyping(&output.ret, &super_output.ret, reason)?;

        // 6. Update state with Output "ensures" and check super ensures
        env.assume_ensures(infcx, &output.ensures, span);
        env.fold_local_ptrs(infcx)?;
        env.check_ensures(
            infcx,
            &super_output.ensures,
            ConstrReason::Subtype(SubtypeReason::Ensures),
        )
    })
}

/// Temporarily (around a function call) convert an `&mut` to an `&strg` to allow for the call to be
/// checked. This is done by unfolding the `&mut` into a local pointer at the call-site and then
/// folding the pointer back into the `&mut` upon return.
/// See also [`LocEnv::fold_local_ptrs`].
///
/// ```text
///             unpack(T) = T'
/// ---------------------------------------[local-unfold]
/// Γ ; &mut T => Γ, l:[<: T] T' ; ptr(l)
/// ```
pub fn unfold_local_ptrs(
    infcx: &mut InferCtxt,
    env: &mut impl LocEnv,
    fn_sig: &PolyFnSig,
    actuals: &[Ty],
) -> InferResult<Vec<Ty>> {
    // We *only* need to know whether each input is a &strg or not
    let fn_sig = fn_sig.skip_binder_ref();
    let mut tys = vec![];
    for (actual, input) in izip!(actuals, fn_sig.inputs()) {
        let actual = if let (
            TyKind::Indexed(BaseTy::Ref(re, bound, Mutability::Mut), _),
            TyKind::StrgRef(_, _, _),
        ) = (actual.kind(), input.kind())
        {
            let loc = env.unfold_local_ptr(infcx, bound)?;
            let path1 = Path::new(loc, rty::List::empty());
            Ty::ptr(PtrKind::Mut(*re), path1)
        } else {
            actual.clone()
        };
        tys.push(actual);
    }
    Ok(tys)
}

struct SkipConstr;

impl TypeFolder for SkipConstr {
    fn fold_ty(&mut self, ty: &rty::Ty) -> rty::Ty {
        if let rty::TyKind::Constr(_, inner_ty) = ty.kind() {
            inner_ty.fold_with(self)
        } else {
            ty.super_fold_with(self)
        }
    }
}

fn is_indexed_mut_skipping_constr(ty: &Ty) -> bool {
    let ty = SkipConstr.fold_ty(ty);
    if let rty::Ref!(_, inner_ty, Mutability::Mut) = ty.kind()
        && let TyKind::Indexed(..) = inner_ty.kind()
    {
        true
    } else {
        false
    }
}

/// HACK(nilehmann) This let us infer parameters under mutable references for the simple case
/// where the formal argument is of the form `&mut B[@n]`, e.g., the type of the first argument
/// to `RVec::get_mut` is `&mut RVec<T>[@n]`. We should remove this after we implement opening of
/// mutable references.
pub fn infer_under_mut_ref_hack(
    rcx: &mut InferCtxt,
    actuals: &[Ty],
    fn_sig: &PolyFnSig,
) -> Vec<Ty> {
    iter::zip(actuals, fn_sig.skip_binder_ref().inputs())
        .map(|(actual, formal)| {
            if let rty::Ref!(re, deref_ty, Mutability::Mut) = actual.kind()
                && is_indexed_mut_skipping_constr(formal)
            {
                rty::Ty::mk_ref(*re, rcx.unpack(deref_ty), Mutability::Mut)
            } else {
                actual.clone()
            }
        })
        .collect()
}
