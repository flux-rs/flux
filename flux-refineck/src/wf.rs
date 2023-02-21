//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.
use std::{borrow::Borrow, iter};

use flux_common::{bug, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, SurfaceIdent},
};
use itertools::izip;
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_span::Span;

pub struct Wf<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    modes: FxHashMap<fhir::Name, fhir::InferMode>,
}

struct Env {
    sorts: FxHashMap<fhir::Name, fhir::Sort>,
}

impl Env {
    /// Push a layer of binders. We assume all names are fresh so we don't care about shadowing
    fn push_layer<'a>(
        &mut self,
        binders: impl IntoIterator<Item = (&'a fhir::Name, &'a fhir::Sort)>,
    ) {
        for (binder, sort) in binders {
            self.sorts.insert(*binder, sort.clone());
        }
    }
}

impl From<&[fhir::FunRefineParam]> for Env {
    fn from(params: &[fhir::FunRefineParam]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, param.sort.clone()))
            .collect();
        Env { sorts }
    }
}

impl From<&[(fhir::Ident, fhir::Sort)]> for Env {
    fn from(params: &[(fhir::Ident, fhir::Sort)]) -> Self {
        Env {
            sorts: params
                .iter()
                .map(|(ident, sort)| (ident.name, sort.clone()))
                .collect(),
        }
    }
}

impl<T: Borrow<fhir::Name>> std::ops::Index<T> for Env {
    type Output = fhir::Sort;

    fn index(&self, var: T) -> &Self::Output {
        self.sorts
            .get(var.borrow())
            .unwrap_or_else(|| panic!("no enty found for key: `{:?}`", var.borrow()))
    }
}

impl Wf<'_, '_> {
    pub fn check_qualifier(
        early_cx: &EarlyCtxt,
        qualifier: &fhir::Qualifier,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(early_cx);
        let env = Env::from(&qualifier.args[..]);

        wf.check_expr(&env, &qualifier.expr, &fhir::Sort::Bool)
    }

    pub fn check_defn(early_cx: &EarlyCtxt, defn: &fhir::Defn) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(early_cx);
        let env = Env::from(&defn.args[..]);
        wf.check_expr(&env, &defn.expr, &defn.sort)
    }

    pub fn check_fn_quals(
        sess: &FluxSession,
        qualifiers: &FxHashSet<String>,
        fn_quals: &Vec<SurfaceIdent>,
    ) -> Result<(), ErrorGuaranteed> {
        for qual in fn_quals {
            if !qualifiers.contains(&qual.name.to_string()) {
                let span = qual.span;
                return Err(sess.emit_err(errors::UnknownQualifier::new(span)));
            }
        }
        Ok(())
    }

    pub fn check_alias(early_cx: &EarlyCtxt, alias: &fhir::TyAlias) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(early_cx);
        let mut env = Env::from(&alias.params[..]);
        wf.check_type(&mut env, &alias.ty)
    }

    pub fn check_struct_def(
        early_cx: &EarlyCtxt,
        struct_def: &fhir::StructDef,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(early_cx);
        let mut env = Env::from(&struct_def.params[..]);

        struct_def
            .invariants
            .iter()
            .try_for_each_exhaust(|invariant| wf.check_expr(&env, invariant, &fhir::Sort::Bool))?;

        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            fields
                .iter()
                .try_for_each_exhaust(|ty| wf.check_type(&mut env, ty))?;
        }
        Ok(())
    }

    pub fn check_enum_def(
        early_cx: &EarlyCtxt,
        enum_def: &fhir::EnumDef,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(early_cx);

        let env = Env::from(&enum_def.params[..]);
        enum_def
            .invariants
            .iter()
            .try_for_each_exhaust(|invariant| wf.check_expr(&env, invariant, &fhir::Sort::Bool))?;

        enum_def
            .variants
            .iter()
            .try_for_each_exhaust(|variant| wf.check_variant(variant))
    }

    pub fn check_fn_sig(early_cx: &EarlyCtxt, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut wf = Wf::new(early_cx);
        for param in &fn_sig.params {
            wf.modes.insert(param.name.name, param.mode);
        }
        let mut env = Env::from(&fn_sig.params[..]);

        let args = fn_sig
            .args
            .iter()
            .try_for_each_exhaust(|ty| wf.check_type(&mut env, ty));

        let requires = fn_sig
            .requires
            .iter()
            .try_for_each_exhaust(|constr| wf.check_constr(&mut env, constr));

        env.push_layer(
            fn_sig
                .output
                .params
                .iter()
                .map(|param| (&param.name.name, &param.sort)),
        );
        let ret = wf.check_type(&mut env, &fn_sig.output.ret);
        let ensures = fn_sig
            .output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| wf.check_constr(&mut env, constr));

        let constrs = wf.check_output_locs(fn_sig);

        args?;
        ret?;
        ensures?;
        requires?;
        constrs?;

        Ok(())
    }
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>) -> Self {
        Wf { early_cx, modes: FxHashMap::default() }
    }

    fn check_variant(&self, variant: &fhir::VariantDef) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::from(&variant.params[..]);
        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty));
        let indices = self.check_refine_arg(&mut env, &variant.ret.idx, &variant.ret.bty.sort());
        fields?;
        indices?;
        Ok(())
    }

    fn check_output_locs(&self, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut output_locs = FxHashSet::default();
        fn_sig
            .output
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| {
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

    fn check_constr(
        &self,
        env: &mut Env,
        constr: &fhir::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                [self.check_loc(env, *loc), self.check_type(env, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            fhir::Constraint::Pred(pred) => self.check_pred(env, pred),
        }
    }

    fn check_type(&self, env: &mut Env, ty: &fhir::Ty) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.check_base_ty(env, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                self.check_refine_arg(env, idx, &bty.sort())?;
                self.check_base_ty(env, bty)
            }
            fhir::TyKind::Exists(bty, bind, pred) => {
                let sort = bty.sort();
                self.check_base_ty(env, bty)?;
                env.push_layer([(&bind.name, &sort)]);
                self.check_pred(env, pred)
            }
            fhir::TyKind::Ptr(loc) => self.check_loc(env, *loc),
            fhir::TyKind::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty))
            }
            fhir::TyKind::Ref(_, ty) | fhir::TyKind::Array(ty, _) => self.check_type(env, ty),
            fhir::TyKind::Constr(pred, ty) => {
                self.check_pred(env, pred)?;
                self.check_type(env, ty)
            }
            fhir::TyKind::RawPtr(ty, _) => self.check_type(env, ty),
            fhir::TyKind::Never | fhir::TyKind::Param(_) => Ok(()),
        }
    }

    fn check_base_ty(&self, env: &mut Env, bty: &fhir::BaseTy) -> Result<(), ErrorGuaranteed> {
        match &bty.kind {
            fhir::BaseTyKind::Path(path) => self.check_path(env, path),
            fhir::BaseTyKind::Slice(ty) => self.check_type(env, ty),
        }
    }

    fn check_path(&self, env: &mut Env, path: &fhir::Path) -> Result<(), ErrorGuaranteed> {
        match &path.res {
            fhir::Res::Alias(def_id, args) => {
                let sorts = self.early_cx.early_bound_sorts_of(*def_id);
                if args.len() != sorts.len() {
                    return self.emit_err(errors::EarlyBoundArgCountMismatch::new(
                        path.span,
                        sorts.len(),
                        args.len(),
                    ));
                }
                iter::zip(args, sorts)
                    .try_for_each_exhaust(|(arg, sort)| self.check_refine_arg(env, arg, sort))?;
            }
            fhir::Res::Adt(_)
            | fhir::Res::Int(_)
            | fhir::Res::Uint(_)
            | fhir::Res::Bool
            | fhir::Res::Float(_)
            | fhir::Res::Str
            | fhir::Res::Char => {}
        }
        path.generics
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(env, ty))
    }

    fn check_aggregate(
        &self,
        env: &mut Env,
        def_id: DefId,
        args: &[fhir::RefineArg],
        span: Span,
    ) -> Result<(), ErrorGuaranteed> {
        let sorts = self.early_cx.index_sorts_of(def_id);
        if args.len() != sorts.len() {
            return self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("type"),
                sorts.len(),
                args.len(),
            ));
        }
        izip!(args, sorts)
            .map(|(arg, expected)| self.check_refine_arg(env, arg, expected))
            .try_collect_exhaust()
    }

    fn check_refine_arg(
        &self,
        env: &mut Env,
        arg: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => {
                let found = self.synth_expr(env, expr)?;
                if !self.is_coercible(&found, expected) {
                    return self.emit_err(errors::SortMismatch::new(expr.span, expected, &found));
                }
                if !matches!(&expr.kind, fhir::ExprKind::Var(..)) {
                    self.check_param_uses(env, expr, false)?;
                }
                Ok(())
            }
            fhir::RefineArg::Abs(params, body, span) => {
                if let Some(fsort) = self.is_coercible_to_func(expected) {
                    if params.len() != fsort.inputs().len() {
                        return self.emit_err(errors::ParamCountMismatch::new(
                            *span,
                            fsort.inputs().len(),
                            params.len(),
                        ));
                    }
                    let params = iter::zip(params, fsort.inputs())
                        .map(|((name, _), sort)| (&name.name, sort));
                    env.push_layer(params);
                    self.check_expr(env, body, fsort.output())?;
                    self.check_param_uses(env, body, true)
                } else {
                    self.emit_err(errors::UnexpectedFun::new(*span, expected))
                }
            }
            fhir::RefineArg::Aggregate(def_id, flds, span) => {
                self.check_aggregate(env, *def_id, flds, *span)?;
                let found = fhir::Sort::Aggregate(*def_id);
                if &found != expected {
                    return self.emit_err(errors::SortMismatch::new(*span, expected, &found));
                }
                Ok(())
            }
        }
    }

    fn check_pred(&self, env: &Env, expr: &fhir::Expr) -> Result<(), ErrorGuaranteed> {
        self.check_expr(env, expr, &fhir::Sort::Bool)?;
        self.check_param_uses(env, expr, true)
    }

    fn check_expr(
        &self,
        env: &Env,
        e: &fhir::Expr,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        let found = self.synth_expr(env, e)?;
        if self.is_coercible(&found, expected) {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(e.span, expected, &found))
        }
    }

    fn check_loc(&self, env: &Env, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = &env[&loc.name];
        if found == &fhir::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(loc.span(), &fhir::Sort::Loc, found))
        }
    }

    fn synth_expr(&self, env: &Env, e: &fhir::Expr) -> Result<fhir::Sort, ErrorGuaranteed> {
        match &e.kind {
            fhir::ExprKind::Var(var) => Ok(env[var.name].clone()),
            fhir::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => self.synth_binary_op(env, *op, e1, e2),
            fhir::ExprKind::UnaryOp(op, e) => self.synth_unary_op(env, *op, e),
            fhir::ExprKind::Const(_, _) => Ok(fhir::Sort::Int), // TODO: generalize const sorts
            fhir::ExprKind::App(f, es) => self.synth_app(env, f, es, e.span),
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                self.check_expr(env, p, &fhir::Sort::Bool)?;
                let sort = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, &sort)?;
                Ok(sort)
            }
            fhir::ExprKind::Dot(var, fld) => {
                let sort = &env[var.name];
                match sort {
                    fhir::Sort::Aggregate(def_id) => {
                        self.early_cx
                            .field_sort(*def_id, fld.name)
                            .cloned()
                            .ok_or_else(|| {
                                self.early_cx
                                    .emit_err(errors::FieldNotFound::new(sort, *fld))
                            })
                    }
                    fhir::Sort::Bool | fhir::Sort::Int | fhir::Sort::Real => {
                        self.emit_err(errors::InvalidPrimitiveDotAccess::new(sort, *fld))
                    }
                    _ => self.emit_err(errors::FieldNotFound::new(sort, *fld)),
                }
            }
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                self.check_expr(env, e1, &fhir::Sort::Bool)?;
                self.check_expr(env, e2, &fhir::Sort::Bool)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Eq | fhir::BinOp::Ne => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, &s)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Mod => {
                self.check_expr(env, e1, &fhir::Sort::Int)?;
                self.check_expr(env, e2, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Int)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                let sort = self.synth_expr(env, e1)?;
                if let Some(sort) = self.is_coercible_to_numeric(&sort) {
                    self.check_expr(env, e2, &sort)?;
                    Ok(fhir::Sort::Bool)
                } else {
                    self.emit_err(errors::ExpectedNumeric::new(e1.span, &sort))
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                let sort = self.synth_expr(env, e1)?;
                if let Some(sort) = self.is_coercible_to_numeric(&sort) {
                    self.check_expr(env, e2, &sort)?;
                    Ok(sort)
                } else {
                    self.emit_err(errors::ExpectedNumeric::new(e1.span, &sort))
                }
            }
        }
    }

    fn synth_unary_op(
        &self,
        env: &Env,
        op: fhir::UnOp,
        e: &fhir::Expr,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        match op {
            fhir::UnOp::Not => {
                self.check_expr(env, e, &fhir::Sort::Bool)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::UnOp::Neg => {
                self.check_expr(env, e, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Int)
            }
        }
    }

    #[track_caller]
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.early_cx.emit_err(err))
    }

    fn synth_app(
        &self,
        env: &Env,
        func: &fhir::Func,
        args: &[fhir::Expr],
        span: Span,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        let fsort = self.synth_func(env, func)?;
        if args.len() != fsort.inputs().len() {
            return self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("function"),
                fsort.inputs().len(),
                args.len(),
            ));
        }

        iter::zip(args, fsort.inputs())
            .try_for_each_exhaust(|(arg, formal)| self.check_expr(env, arg, formal))?;

        Ok(fsort.output().clone())
    }

    fn synth_func(&self, env: &Env, func: &fhir::Func) -> Result<fhir::FuncSort, ErrorGuaranteed> {
        match func {
            fhir::Func::Var(var) => {
                let sort = &env[&var.name];
                if let Some(fsort) = self.is_coercible_to_func(sort) {
                    Ok(fsort)
                } else {
                    Err(self
                        .early_cx
                        .emit_err(errors::ExpectedFun::new(var.span(), sort)))
                }
            }
            fhir::Func::Uif(func, span) => {
                Ok(self
                    .early_cx
                    .uif(func)
                    .unwrap_or_else(|| bug!("no definition found for uif `{func:?}` - {span:?}"))
                    .sort
                    .clone())
            }
        }
    }

    /// Whether a value of `sort1` can be automatically coerced to a value of `sort2`. A value of an
    /// [`Aggregate`] sort with a single field of sort `s` can be coerced to a value of sort `s` and vice
    /// versa, i.e., we can automatically project the field out of the adt or inject a value into an
    /// adt.
    ///
    /// [`Aggregate`]: fhir::Sort::Aggregate
    fn is_coercible(&self, sort1: &fhir::Sort, sort2: &fhir::Sort) -> bool {
        let mut sort1 = sort1.clone();
        let mut sort2 = sort2.clone();
        if let Some(sort) = self.is_single_field_adt(&sort1) {
            sort1 = sort.clone();
        }
        if let Some(sort) = self.is_single_field_adt(&sort2) {
            sort2 = sort.clone();
        }
        sort1 == sort2
    }

    fn is_coercible_to_func(&self, sort: &fhir::Sort) -> Option<fhir::FuncSort> {
        self.early_cx.is_coercible_to_func(sort)
    }

    fn is_coercible_to_numeric(&self, sort: &fhir::Sort) -> Option<fhir::Sort> {
        if sort.is_numeric() {
            Some(sort.clone())
        } else if let Some(sort) = self.is_single_field_adt(sort) && sort.is_numeric() {
            Some(sort.clone())
        } else {
            None
        }
    }

    fn is_single_field_adt(&self, sort: &fhir::Sort) -> Option<&'a fhir::Sort> {
        self.early_cx.is_single_field_adt(sort)
    }

    /// Checks that refinement parameters are used in allowed positions.
    fn check_param_uses(
        &self,
        env: &Env,
        expr: &fhir::Expr,
        is_top_level_conj: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, exprs) => {
                let is_pred = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses(env, e, is_pred))
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_param_uses(env, e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                   && let fhir::Func::Var(var) = func
                   && let fhir::InferMode::KVar = self.modes[&var.name]
                {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), &env[var.name]));
                }
                args.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses(env, arg, false))
            }
            fhir::ExprKind::Var(var) => {
                if let sort @ fhir::Sort::Func(_) = &env[var.name] {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
            fhir::ExprKind::IfThenElse(exprs) => {
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses(env, e, false))
            }
            fhir::ExprKind::Literal(_) | fhir::ExprKind::Const(_, _) => Ok(()),
            fhir::ExprKind::Dot(var, _) => {
                if let sort @ fhir::Sort::Func(_) = &env[var.name] {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
        }
    }
}

fn synth_lit(lit: fhir::Lit) -> fhir::Sort {
    match lit {
        fhir::Lit::Int(_) => fhir::Sort::Int,
        fhir::Lit::Bool(_) => fhir::Sort::Bool,
        fhir::Lit::Real(_) => fhir::Sort::Real,
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::fhir::{self, SurfaceIdent};
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(wf::sort_mismatch, code = "FLUX")]
    pub(super) struct SortMismatch<'a> {
        #[primary_span]
        #[label]
        span: Span,
        expected: &'a fhir::Sort,
        found: &'a fhir::Sort,
    }

    impl<'a> SortMismatch<'a> {
        pub(super) fn new(span: Span, expected: &'a fhir::Sort, found: &'a fhir::Sort) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::arg_count_mismatch, code = "FLUX")]
    pub(super) struct ArgCountMismatch {
        #[primary_span]
        #[label]
        span: Option<Span>,
        expected: usize,
        found: usize,
        thing: String,
    }

    impl ArgCountMismatch {
        pub(super) fn new(
            span: Option<Span>,
            thing: String,
            expected: usize,
            found: usize,
        ) -> Self {
            Self { span, expected, found, thing }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::early_bound_arg_count_mismatch, code = "FLUX")]
    pub(super) struct EarlyBoundArgCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        expected: usize,
        found: usize,
    }

    impl EarlyBoundArgCountMismatch {
        pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::duplicated_ensures, code = "FLUX")]
    pub(super) struct DuplicatedEnsures {
        #[primary_span]
        span: Span,
        loc: Symbol,
    }

    impl DuplicatedEnsures {
        pub(super) fn new(loc: &fhir::Ident) -> DuplicatedEnsures {
            Self { span: loc.span(), loc: loc.sym() }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::unknown_qualifier, code = "FLUX")]
    pub(super) struct UnknownQualifier {
        #[primary_span]
        span: Span,
    }

    impl UnknownQualifier {
        pub(super) fn new(span: Span) -> UnknownQualifier {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::missing_ensures, code = "FLUX")]
    pub(super) struct MissingEnsures {
        #[primary_span]
        span: Span,
    }

    impl MissingEnsures {
        pub(super) fn new(loc: &fhir::Ident) -> MissingEnsures {
            Self { span: loc.span() }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::expected_fun, code = "FLUX")]
    pub(super) struct ExpectedFun<'a> {
        #[primary_span]
        span: Span,
        found: &'a fhir::Sort,
    }

    impl<'a> ExpectedFun<'a> {
        pub(super) fn new(span: Span, found: &'a fhir::Sort) -> Self {
            Self { span, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::invalid_param_in_func_pos, code = "FLUX")]
    pub(super) struct InvalidParamPos<'a> {
        #[primary_span]
        #[label]
        span: Span,
        sort: &'a fhir::Sort,
        is_pred: bool,
    }

    impl<'a> InvalidParamPos<'a> {
        pub(super) fn new(span: Span, sort: &'a fhir::Sort) -> Self {
            Self { span, sort, is_pred: sort.is_pred() }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::unexpected_fun, code = "FLUX")]
    pub(super) struct UnexpectedFun<'a> {
        #[primary_span]
        #[label]
        span: Span,
        sort: &'a fhir::Sort,
    }

    impl<'a> UnexpectedFun<'a> {
        pub(super) fn new(span: Span, sort: &'a fhir::Sort) -> Self {
            Self { span, sort }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::expected_numeric, code = "FLUX")]
    pub(super) struct ExpectedNumeric<'a> {
        #[primary_span]
        #[label]
        span: Span,
        found: &'a fhir::Sort,
    }

    impl<'a> ExpectedNumeric<'a> {
        pub(super) fn new(span: Span, found: &'a fhir::Sort) -> Self {
            Self { span, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::param_count_mismatch, code = "FLUX")]
    pub(super) struct ParamCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        expected: usize,
        found: usize,
    }

    impl ParamCountMismatch {
        pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::field_not_found, code = "FLUX")]
    pub(super) struct FieldNotFound<'a> {
        #[primary_span]
        span: Span,
        sort: &'a fhir::Sort,
        fld: SurfaceIdent,
    }

    impl<'a> FieldNotFound<'a> {
        pub(super) fn new(sort: &'a fhir::Sort, fld: SurfaceIdent) -> Self {
            Self { span: fld.span, sort, fld }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::invalid_primitive_dot_access, code = "FLUX")]
    pub(super) struct InvalidPrimitiveDotAccess<'a> {
        #[primary_span]
        span: Span,
        sort: &'a fhir::Sort,
    }

    impl<'a> InvalidPrimitiveDotAccess<'a> {
        pub(super) fn new(sort: &'a fhir::Sort, fld: SurfaceIdent) -> Self {
            Self { sort, span: fld.span }
        }
    }
}
