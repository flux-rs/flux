use std::ops::ControlFlow;

use flux_middle::{
    query_bug,
    rty::{
        self, AliasKind, AliasTy, BaseTy, Expr, ExprKind, GenericArg, GenericArgsExt, KVid, Ty,
        TyKind,
        fold::{
            FallibleTypeFolder, TypeFoldable, TypeSuperFoldable, TypeSuperVisitable, TypeVisitable,
            TypeVisitor,
        },
        refining::Refiner,
    },
};
use flux_rustc_bridge::lowering::Lower;
use rustc_hir::def_id::DefId;

use crate::{
    infer::{
        ConstrReason, InferCtxt, InferCtxtAt, InferErr, InferResult, OpaqueObligation,
        fn_trait_obligations,
    },
    projections::NormalizeExt as _,
};

impl InferCtxtAt<'_, '_, '_, '_> {
    pub fn reveal_opaque_types<T: TypeFoldable>(
        &mut self,
        t: &T,
        reason: ConstrReason,
    ) -> InferResult<(T, Vec<OpaqueObligation>)> {
        let mut revealer = OpaqueRevealer { infcx: self, reason, obligations: vec![] };
        let t = t.try_fold_with(&mut revealer)?;
        Ok((t, revealer.obligations))
    }
}

/// Inside its defining scope, we can use a value of an opaque type as its hidden type, e.g.,
/// pass the result of a recursive call `foo(n - 1)` to a function expecting a `Wrap<i32>`. We
/// support this by replacing the opaque type with its hidden type refined with fresh kvars. For
/// each projection bound `<Opaque as Trait>::Assoc == T`, the kvars in `<Hidden as Trait>::Assoc`
/// are constrained to be equivalent to `T`. Every other kvar we generate that isn't in the
/// projection bounds is replaced by true.
struct OpaqueRevealer<'a, 'b, 'infcx, 'genv, 'tcx> {
    infcx: &'a mut InferCtxtAt<'b, 'infcx, 'genv, 'tcx>,
    reason: ConstrReason,
    obligations: Vec<OpaqueObligation>,
}

impl FallibleTypeFolder for OpaqueRevealer<'_, '_, '_, '_, '_> {
    type Error = InferErr;

    fn try_fold_ty(&mut self, ty: &Ty) -> InferResult<Ty> {
        if let TyKind::Indexed(bty, _) = ty.kind()
            && let Some(hidden) = self.reveal(bty)?
        {
            return Ok(hidden.to_ty());
        }
        let ty = ty.try_super_fold_with(self)?;
        // The index of a revealed opaque type is usually bound by an existential (`∃v. Opaque[v]`),
        // which we drop once nothing mentions it.
        if let TyKind::Exists(body) = ty.kind()
            && !body.skip_binder_ref().has_escaping_bvars()
        {
            return Ok(body.skip_binder_ref().clone());
        }
        Ok(ty)
    }

    fn try_fold_generic_arg(&mut self, arg: &GenericArg) -> InferResult<GenericArg> {
        // The hidden type has a different sort than the opaque type, so we replace the entire
        // constructor, keeping its predicate if it doesn't mention the opaque type's index.
        if let GenericArg::Base(ctor) = arg
            && let pred = &ctor.as_ref().skip_binder().pred
            && !pred.has_escaping_bvars()
            && let Some(hidden) = self.reveal(ctor.as_bty_skipping_binder())?
        {
            let hidden =
                hidden.map(|sty| rty::SubsetTy::new(sty.bty, sty.idx, Expr::and(sty.pred, pred)));
            return Ok(GenericArg::Base(hidden));
        }
        arg.try_super_fold_with(self)
    }
}

impl OpaqueRevealer<'_, '_, '_, '_, '_> {
    fn reveal(&mut self, bty: &BaseTy) -> InferResult<Option<rty::SubsetTyCtor>> {
        let BaseTy::Alias(alias_ty @ AliasTy { kind: AliasKind::Opaque { def_id }, .. }) = bty
        else {
            return Ok(None);
        };
        let Some(hidden) = hidden_ty_with_kvars(self.infcx, *def_id, alias_ty) else {
            return Ok(None);
        };

        // We reveal coroutines' bodies when they aren't being returned only- at return sites,
        // they are handled normally
        if let BaseTy::Coroutine(..) = hidden.as_bty_skipping_binder() {
            let reveal = self.reason != ConstrReason::Ret;
            return Ok(reveal.then(|| hidden.replace_kvars(|_| Some(Expr::tt()))));
        }

        let bounds = self.infcx.genv.item_bounds(*def_id)?.instantiate(
            self.infcx.tcx(),
            &alias_ty.args,
            &alias_ty.refine_args,
        );

        let (bounds, fn_trait_preds) =
            rty::Clause::split_off_fn_trait_clauses(self.infcx.genv, &bounds);
        let mut pinned = KVidCollector(vec![]);
        for clause in &bounds {
            if !clause.kind().vars().is_empty() {
                Err(query_bug!("reveal opaque type: clause with bound vars: `{clause:?}`"))?;
            }
            if let rty::ClauseKind::Projection(pred) = clause.kind_skipping_binder() {
                let term = pred.term.to_ty().try_fold_with(self)?;
                let alias_ty = pred
                    .projection_term
                    .with_self_ty(hidden.as_bty_skipping_binder().to_subset_ty_ctor())
                    .to_alias_ty();
                let assoc = BaseTy::Alias(alias_ty)
                    .to_ty()
                    .deeply_normalize(self.infcx)?;
                let _ = assoc.visit_with(&mut pinned);
                self.infcx.subtyping(&term, &assoc, self.reason)?;
                self.infcx.subtyping(&assoc, &term, self.reason)?;
            }
        }
        let hidden = hidden.replace_kvars(|kvar| (!pinned.0.contains(&kvar.kvid)).then(Expr::tt));
        self.obligations
            .extend(fn_trait_obligations(fn_trait_preds, &hidden.to_ty()));
        Ok(Some(hidden))
    }
}

/// Returns the hidden type of the opaque type refined with fresh kvars.
fn hidden_ty_with_kvars(
    infcx: &mut InferCtxt,
    def_id: DefId,
    alias_ty: &AliasTy,
) -> Option<rty::SubsetTyCtor> {
    let genv = infcx.genv;
    let tcx = genv.tcx();

    if alias_ty.has_escaping_bvars()
        || tcx.typeck_root_def_id(tcx.parent(def_id)) != tcx.typeck_root_def_id(infcx.def_id)
    {
        return None;
    }

    let hidden = tcx
        .type_of(def_id)
        .instantiate(tcx, alias_ty.args.to_rustc(tcx))
        .skip_normalization();

    // Closures are kept opaque and handled by their predicates
    if hidden
        .walk()
        .any(|arg| arg.as_type().is_some_and(|ty| ty.is_closure()))
    {
        return None;
    }

    let ctor = Refiner::with_holes(genv, infcx.def_id)
        .ok()?
        .refine_ty_or_base(&hidden.lower(tcx).ok()?)
        .ok()?
        .as_base()?;
    Some(ctor.replace_holes(|binders, kind| infcx.fresh_infer_var_for_hole(binders, kind)))
}

/// Collects the kvars appearing in a type.
struct KVidCollector(Vec<KVid>);

impl TypeVisitor for KVidCollector {
    fn visit_expr(&mut self, expr: &Expr) -> ControlFlow<!> {
        if let ExprKind::KVar(kvar) = expr.kind() {
            self.0.push(kvar.kvid);
        }
        expr.super_visit_with(self)
    }
}
