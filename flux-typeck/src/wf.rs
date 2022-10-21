use std::iter;

use flux_common::iter::IterExt;
use flux_middle::{fhir, global_env::GlobalEnv, rty, rty::conv::conv_sort};
use itertools::izip;
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_span::Span;

pub struct Wf<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
}

struct Env {
    sorts: FxHashMap<fhir::Name, rty::Sort>,
}

impl Env {
    fn new(params: &[fhir::Param]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, conv_sort(param.sort)))
            .collect();
        Env { sorts }
    }

    fn with_binders<R>(
        &mut self,
        binders: &[fhir::Name],
        sorts: &[rty::Sort],
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        debug_assert_eq!(binders.len(), sorts.len());
        for (binder, sort) in iter::zip(binders, sorts) {
            self.sorts.insert(*binder, sort.clone());
        }
        let r = f(self);
        for binder in binders {
            self.sorts.remove(binder);
        }
        r
    }
}

impl std::ops::Index<&'_ fhir::Name> for Env {
    type Output = rty::Sort;

    fn index(&self, var: &fhir::Name) -> &Self::Output {
        self.sorts
            .get(var)
            .unwrap_or_else(|| panic!("no enty found for key: `{var:?}`"))
    }
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    pub fn new(genv: &'a GlobalEnv<'a, 'tcx>) -> Wf<'a, 'tcx> {
        Wf { genv }
    }

    pub fn check_fn_sig(&self, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&fn_sig.params);

        let args = fn_sig
            .args
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty, true));

        let requires = fn_sig
            .requires
            .iter()
            .try_for_each_exhaust(|constr| self.check_constr(&mut env, constr));

        let ensures = fn_sig
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constr(&mut env, constr));

        let ret = self.check_type(&mut env, &fn_sig.ret, false);

        let constrs = self.check_constrs(fn_sig);

        args?;
        ret?;
        ensures?;
        requires?;
        constrs?;

        Ok(())
    }

    fn check_constrs(&self, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut output_locs = FxHashSet::default();
        fn_sig.ensures.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, _) = constr
               && !output_locs.insert(loc.name)
            {
                self.emit_err(errors::DuplicatedEnsures::new(loc))
            } else {
                Ok(())
            }
        })?;

        fn_sig.requires.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, _) = constr
               && !output_locs.contains(&loc.name)
            {
                self.emit_err(errors::MissingEnsures::new(loc))
            } else {
                Ok(())
            }
        })
    }

    pub fn check_qualifier(&self, qualifier: &fhir::Qualifier) -> Result<(), ErrorGuaranteed> {
        let env = Env::new(&qualifier.args);

        self.check_expr(&env, &qualifier.expr, rty::Sort::Bool)
    }

    pub fn check_adt_def(&self, adt_def: &fhir::AdtDef) -> Result<(), ErrorGuaranteed> {
        let env = Env::new(&adt_def.refined_by);
        adt_def
            .invariants
            .iter()
            .try_for_each_exhaust(|invariant| self.check_expr(&env, invariant, rty::Sort::Bool))?;

        Ok(())
    }

    pub fn check_struct_def(
        &self,
        adt_data: &fhir::AdtDef,
        def: &fhir::StructDef,
    ) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&adt_data.refined_by);
        if let fhir::StructKind::Transparent { fields } = &def.kind {
            fields.iter().try_for_each_exhaust(|ty| {
                if let Some(ty) = ty {
                    self.check_type(&mut env, ty, true)
                } else {
                    Ok(())
                }
            })?;
        }
        Ok(())
    }

    pub fn check_enum_def(&self, def: &fhir::EnumDef) -> Result<(), ErrorGuaranteed> {
        def.variants
            .iter()
            .try_for_each_exhaust(|variant| self.check_variant(variant))
    }

    fn check_variant(&self, variant: &fhir::VariantDef) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&variant.params);
        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty, true));
        let indices =
            self.check_indices(&env, &variant.ret.indices, self.sorts(&variant.ret.bty), false);
        fields?;
        indices?;
        Ok(())
    }

    fn check_constr(
        &self,
        env: &mut Env,
        constr: &fhir::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                [self.check_loc(env, *loc), self.check_type(env, ty, true)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            fhir::Constraint::Pred(e) => self.check_expr(env, e, rty::Sort::Bool),
        }
    }

    fn check_type(
        &self,
        env: &mut Env,
        ty: &fhir::Ty,
        allow_binder: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match ty {
            fhir::Ty::BaseTy(bty) => self.check_base_ty(env, bty, allow_binder),
            fhir::Ty::Indexed(bty, refine) => {
                self.check_indices(env, refine, self.sorts(bty), allow_binder)?;
                self.check_base_ty(env, bty, allow_binder)
            }
            fhir::Ty::Exists(bty, binders, pred) => {
                let sorts = self.sorts(bty);
                if binders.len() != sorts.len() {
                    return self.emit_err(errors::ParamCountMismatch::new(
                        None,
                        sorts.len(),
                        binders.len(),
                    ));
                }
                self.check_base_ty(env, bty, allow_binder)?;
                env.with_binders(binders, &sorts, |env| self.check_expr(env, pred, rty::Sort::Bool))
            }
            fhir::Ty::Ptr(loc) => self.check_loc(env, *loc),
            fhir::Ty::Ref(_, ty) => self.check_type(env, ty, allow_binder),
            fhir::Ty::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty, allow_binder))
            }
            fhir::Ty::Constr(pred, ty) => {
                self.check_expr(env, pred, rty::Sort::Bool)?;
                self.check_type(env, ty, allow_binder)
            }
            fhir::Ty::Slice(ty) | fhir::Ty::Array(ty, _) => self.check_type(env, ty, false),
            fhir::Ty::Never | fhir::Ty::Param(_) | fhir::Ty::Float(_) | fhir::Ty::Str => Ok(()),
        }
    }

    fn is_box(&self, def_id: DefId) -> bool {
        self.genv.tcx.adt_def(def_id).is_box()
    }

    fn check_base_ty(
        &self,
        env: &mut Env,
        bty: &fhir::BaseTy,
        allow_binder: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match bty {
            fhir::BaseTy::Adt(def, substs) => {
                let allow_binder = allow_binder && self.is_box(*def);
                substs
                    .iter()
                    .map(|ty| self.check_type(env, ty, allow_binder))
                    .try_collect_exhaust()
            }
            fhir::BaseTy::Int(_) | fhir::BaseTy::Uint(_) | fhir::BaseTy::Bool => Ok(()),
        }
    }

    fn check_indices(
        &self,
        env: &Env,
        indices: &fhir::Indices,
        expected: Vec<rty::Sort>,
        allow_binder: bool,
    ) -> Result<(), ErrorGuaranteed> {
        if !allow_binder && indices.indices.iter().any(|i| i.is_binder) {
            return self.emit_err(errors::IllegalBinder::new(Some(indices.span)));
        }

        let found = self.synt_indices(env, indices)?;
        if expected.len() != found.len() {
            return self.emit_err(errors::ParamCountMismatch::new(
                Some(indices.span),
                expected.len(),
                found.len(),
            ));
        }
        izip!(indices, expected, found)
            .map(|(idx, expected, found)| {
                if found == expected {
                    Ok(())
                } else {
                    self.emit_err(errors::SortMismatch::new(idx.expr.span, expected, found))
                }
            })
            .try_collect_exhaust()
    }

    fn check_expr(
        &self,
        env: &Env,
        e: &fhir::Expr,
        expected: rty::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        let found = self.synth_expr(env, e)?;
        if found == expected {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(e.span, expected, found))
        }
    }

    fn check_loc(&self, env: &Env, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = env[&loc.name].clone();
        if found == rty::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(loc.source_info.0, rty::Sort::Loc, found))
        }
    }

    fn synt_indices(
        &self,
        env: &Env,
        refine: &fhir::Indices,
    ) -> Result<Vec<rty::Sort>, ErrorGuaranteed> {
        let sorts: Vec<rty::Sort> = refine
            .indices
            .iter()
            .map(|idx| self.synth_expr(env, &idx.expr))
            .try_collect_exhaust()?;
        Ok(sorts)
    }

    fn synth_expr(&self, env: &Env, e: &fhir::Expr) -> Result<rty::Sort, ErrorGuaranteed> {
        match &e.kind {
            fhir::ExprKind::Var(var, ..) => Ok(env[var].clone()),
            fhir::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(env, *op, e1, e2),
            fhir::ExprKind::Const(_, _) => Ok(rty::Sort::Int), // TODO: generalize const sorts
            fhir::ExprKind::App(f, es) => self.synth_uf_app(env, f, es, e.span),
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                self.check_expr(env, p, rty::Sort::Bool)?;
                let sort = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, sort.clone())?;
                Ok(sort)
            }
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
    ) -> Result<rty::Sort, ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                self.check_expr(env, e1, rty::Sort::Bool)?;
                self.check_expr(env, e2, rty::Sort::Bool)?;
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Eq | fhir::BinOp::Ne => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, s)?;
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                self.check_expr(env, e1, rty::Sort::Int)?;
                self.check_expr(env, e2, rty::Sort::Int)?;
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Add
            | fhir::BinOp::Sub
            | fhir::BinOp::Mod
            | fhir::BinOp::Mul
            | fhir::BinOp::Div => {
                self.check_expr(env, e1, rty::Sort::Int)?;
                self.check_expr(env, e2, rty::Sort::Int)?;
                Ok(rty::Sort::Int)
            }
        }
    }

    fn sorts(&self, bty: &fhir::BaseTy) -> Vec<rty::Sort> {
        match bty {
            fhir::BaseTy::Int(_) | fhir::BaseTy::Uint(_) => vec![rty::Sort::Int],
            fhir::BaseTy::Bool => vec![rty::Sort::Bool],
            fhir::BaseTy::Adt(def_id, _) => self.genv.adt_def(*def_id).sorts().to_vec(),
        }
    }

    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.genv.sess.emit_err(err))
    }

    fn synth_uf_app(
        &self,
        env: &Env,
        f: &fhir::UFun,
        es: &[fhir::Expr],
        span: Span,
    ) -> Result<rty::Sort, ErrorGuaranteed> {
        let Some(uif_def) = self.genv.uif_defs.get(&f.symbol) else {
            return self.emit_err(errors::UnresolvedFunction::new(f.span));
        };
        let found = es.len();
        let expected = uif_def.inputs.len();
        if expected != found {
            return self.emit_err(errors::ParamCountMismatch::new(Some(span), expected, found));
        }
        for (e, t) in iter::zip(es, &uif_def.inputs) {
            let e_t = self.synth_expr(env, e)?;
            if e_t != *t {
                return self.emit_err(errors::SortMismatch::new(e.span, t.clone(), e_t));
            }
        }
        Ok(uif_def.output.clone())
    }
}

fn synth_lit(lit: fhir::Lit) -> rty::Sort {
    match lit {
        fhir::Lit::Int(_) => rty::Sort::Int,
        fhir::Lit::Bool(_) => rty::Sort::Bool,
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::fhir;
    use rustc_span::{Span, Symbol};

    use crate::rty;

    #[derive(Diagnostic)]
    #[diag(wf::sort_mismatch, code = "FLUX")]
    pub struct SortMismatch {
        #[primary_span]
        #[label]
        pub span: Span,
        pub expected: rty::Sort,
        pub found: rty::Sort,
    }

    impl SortMismatch {
        pub fn new(span: Span, expected: rty::Sort, found: rty::Sort) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::param_count_mismatch, code = "FLUX")]
    pub struct ParamCountMismatch {
        #[primary_span]
        #[label]
        pub span: Option<Span>,
        pub expected: usize,
        pub found: usize,
    }

    impl ParamCountMismatch {
        pub fn new(span: Option<Span>, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::unresolved_function, code = "FLUX")]
    pub struct UnresolvedFunction {
        #[primary_span]
        #[label]
        pub span: Span,
    }

    impl UnresolvedFunction {
        pub fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::illegal_binder, code = "FLUX")]
    pub struct IllegalBinder {
        #[primary_span]
        #[label]
        pub span: Option<Span>,
    }

    impl IllegalBinder {
        pub fn new(span: Option<Span>) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::duplicated_ensures, code = "FLUX")]
    pub struct DuplicatedEnsures {
        #[primary_span]
        pub span: Span,
        pub loc: Symbol,
    }

    impl DuplicatedEnsures {
        pub fn new(loc: &fhir::Ident) -> DuplicatedEnsures {
            Self { span: loc.source_info.0, loc: loc.source_info.1 }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::missing_ensures, code = "FLUX")]
    pub struct MissingEnsures {
        #[primary_span]
        pub span: Span,
    }

    impl MissingEnsures {
        pub fn new(loc: &fhir::Ident) -> MissingEnsures {
            Self { span: loc.source_info.0 }
        }
    }
}
