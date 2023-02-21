//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]
use std::{borrow::Borrow, iter};

use flux_common::{index::IndexGen, iter::IterExt, span_bug};
use flux_errors::FluxSession;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, BtyOrTy},
    intern::List,
};
use flux_syntax::surface::{self, PrimTy, Res};
use rustc_data_structures::fx::{FxIndexMap, IndexEntry};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_span::{sym, symbol::kw, Span, Symbol};

pub fn desugar_qualifier(
    early_cx: &EarlyCtxt,
    qualifier: &surface::Qualifier,
) -> Result<fhir::Qualifier, ErrorGuaranteed> {
    let mut binders = Binders::from_params(early_cx, &qualifier.args)?;
    let name = qualifier.name.name.to_ident_string();
    let expr = ExprCtxt::new(early_cx, &binders).desugar_expr(&qualifier.expr);

    Ok(fhir::Qualifier {
        name,
        args: binders.pop_layer().into_params(),
        global: qualifier.global,
        expr: expr?,
    })
}

pub fn desugar_defn(
    early_cx: &EarlyCtxt,
    defn: surface::Defn,
) -> Result<fhir::Defn, ErrorGuaranteed> {
    let mut binders = Binders::from_params(early_cx, &defn.args)?;
    let expr = ExprCtxt::new(early_cx, &binders).desugar_expr(&defn.expr)?;
    let name = defn.name.name;
    let sort = resolve_sort(early_cx, &defn.sort)?;
    let args = binders.pop_layer().into_params();
    Ok(fhir::Defn { name, args, sort, expr })
}

fn sort_ident(sort: &surface::Sort) -> Result<surface::Ident, ErrorGuaranteed> {
    match sort {
        surface::Sort::Base(x) => Ok(*x),
        surface::Sort::Func { .. } => panic!("Unexpected func-sort!"),
        surface::Sort::Infer => panic!("Unexpected infer-sort!"),
    }
}

pub fn resolve_defn_uif(
    early_cx: &EarlyCtxt,
    defn: &surface::Defn,
) -> Result<fhir::UifDef, ErrorGuaranteed> {
    let inputs: Vec<surface::Ident> = defn
        .args
        .iter()
        .map(|arg| sort_ident(&arg.sort))
        .try_collect_exhaust()?;
    let output: surface::Ident = sort_ident(&defn.sort)?;
    let sort = resolve_func_sort(early_cx, &inputs[..], &output)?;
    Ok(fhir::UifDef { name: defn.name.name, sort })
}

pub fn resolve_uif_def(
    early_cx: &EarlyCtxt,
    defn: surface::UifDef,
) -> Result<fhir::UifDef, ErrorGuaranteed> {
    let inputs: Vec<surface::Ident> = defn
        .args
        .iter()
        .map(|arg| sort_ident(&arg.sort))
        .try_collect_exhaust()?;
    let output: surface::Ident = sort_ident(&defn.sort)?;
    let sort = resolve_func_sort(early_cx, &inputs[..], &output)?;
    Ok(fhir::UifDef { name: defn.name.name, sort })
}

pub fn desugar_refined_by(
    early_cx: &EarlyCtxt,
    def_id: LocalDefId,
    refined_by: &surface::RefinedBy,
) -> Result<fhir::RefinedBy, ErrorGuaranteed> {
    let mut set = FxHashSet::default();
    refined_by.iter().try_for_each_exhaust(|param| {
        if let Some(old) = set.get(&param.name) {
            return Err(early_cx
                .sess
                .emit_err(errors::DuplicateParam::new(*old, param.name)));
        } else {
            set.insert(param.name);
        }
        Ok(())
    })?;
    let early_bound_params: Vec<_> = refined_by
        .early_bound_params
        .iter()
        .map(|param| resolve_sort(early_cx, &param.sort))
        .try_collect_exhaust()?;

    let index_params: Vec<_> = refined_by
        .index_params
        .iter()
        .map(|param| Ok((param.name.name, resolve_sort(early_cx, &param.sort)?)))
        .try_collect_exhaust()?;

    Ok(fhir::RefinedBy::new(def_id, early_bound_params, index_params, refined_by.span))
}

pub fn desugar_type_alias(
    early_cx: &EarlyCtxt,
    def_id: LocalDefId,
    alias: surface::TyAlias<Res>,
) -> Result<fhir::TyAlias, ErrorGuaranteed> {
    let binders = Binders::from_params(early_cx, &alias.refined_by)?;
    let mut cx = DesugarCtxt::new(early_cx, binders);
    let ty = cx.desugar_ty(None, &alias.ty)?;

    Ok(fhir::TyAlias { def_id, params: cx.binders.pop_layer().into_params(), ty, span: alias.span })
}

pub fn desugar_struct_def(
    early_cx: &EarlyCtxt,
    struct_def: surface::StructDef<Res>,
) -> Result<fhir::StructDef, ErrorGuaranteed> {
    let def_id = struct_def.def_id;
    let binders = Binders::from_params(early_cx, struct_def.refined_by.iter().flatten())?;

    let mut cx = DesugarCtxt::new(early_cx, binders);

    let invariants = struct_def
        .invariants
        .iter()
        .map(|invariant| cx.as_expr_ctxt().desugar_expr(invariant))
        .try_collect_exhaust()?;

    let kind = if struct_def.opaque {
        fhir::StructKind::Opaque
    } else {
        let fields = struct_def
            .fields
            .iter()
            .map(|field| {
                if let Some(ty) = &field.ty {
                    cx.desugar_ty(None, ty)
                } else {
                    fhir::lift::lift_field_def(early_cx, field.def_id)
                }
            })
            .try_collect_exhaust()?;
        fhir::StructKind::Transparent { fields }
    };
    Ok(fhir::StructDef { def_id, params: cx.binders.pop_layer().into_params(), kind, invariants })
}

pub fn desugar_enum_def(
    early_cx: &EarlyCtxt,
    enum_def: &surface::EnumDef<Res>,
) -> Result<fhir::EnumDef, ErrorGuaranteed> {
    let def_id = enum_def.def_id;
    let variants = enum_def
        .variants
        .iter()
        .map(|variant| desugar_variant_def(early_cx, variant))
        .try_collect_exhaust()?;

    let mut binders = Binders::from_params(early_cx, enum_def.refined_by.iter().flatten())?;
    let invariants = enum_def
        .invariants
        .iter()
        .map(|invariant| ExprCtxt::new(early_cx, &binders).desugar_expr(invariant))
        .try_collect_exhaust()?;

    Ok(fhir::EnumDef { def_id, params: binders.pop_layer().into_params(), variants, invariants })
}

fn desugar_variant_def(
    early_cx: &EarlyCtxt,
    variant_def: &surface::VariantDef<Res>,
) -> Result<fhir::VariantDef, ErrorGuaranteed> {
    let mut binders = Binders::new();
    binders.gather_params_variant(early_cx, variant_def)?;
    let mut cx = DesugarCtxt::new(early_cx, binders);

    if let Some(data) = &variant_def.data {
        let fields = data
            .fields
            .iter()
            .map(|ty| cx.desugar_ty(None, ty))
            .try_collect_exhaust()?;

        let ret = cx.desugar_variant_ret(&data.ret)?;

        Ok(fhir::VariantDef {
            def_id: variant_def.def_id,
            params: cx.binders.pop_layer().into_fun_params(),
            fields,
            ret,
        })
    } else {
        fhir::lift::lift_variant_def(early_cx, variant_def.def_id)
    }
}

pub fn desugar_fn_sig(
    early_cx: &EarlyCtxt,
    fn_sig: &surface::FnSig<Res>,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    let mut binders = Binders::new();

    // Desugar inputs
    binders.gather_input_params_fn_sig(early_cx, fn_sig)?;
    let mut cx = DesugarCtxt::new(early_cx, binders);

    if let Some(e) = &fn_sig.requires {
        let pred = cx.as_expr_ctxt().desugar_expr(e)?;
        cx.requires.push(fhir::Constraint::Pred(pred));
    }

    // Bail out if there's an error in the arguments to avoid confusing error messages
    let args = fn_sig
        .args
        .iter()
        .map(|arg| cx.desugar_fun_arg(arg))
        .try_collect_exhaust()?;

    // Desugar output
    cx.binders.push_layer();
    cx.binders.gather_output_params_fn_sig(early_cx, fn_sig)?;
    let ret = match &fn_sig.returns {
        Some(returns) => cx.desugar_ty(None, returns),
        None => {
            let kind = fhir::TyKind::Tuple(vec![]);
            let span = fn_sig.span.with_lo(fn_sig.span.hi());
            Ok(fhir::Ty { kind, span })
        }
    };
    let ensures = fn_sig
        .ensures
        .iter()
        .map(|(bind, ty)| {
            let loc = cx.as_expr_ctxt().desugar_loc(*bind);
            let ty = cx.desugar_ty(None, ty);
            Ok(fhir::Constraint::Type(loc?, ty?))
        })
        .try_collect_exhaust();
    let output = fhir::FnOutput {
        params: cx.binders.pop_layer().into_fun_params(),
        ret: ret?,
        ensures: ensures?,
    };

    Ok(fhir::FnSig {
        params: cx.binders.pop_layer().into_fun_params(),
        requires: cx.requires,
        args,
        output,
    })
}

pub struct DesugarCtxt<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    binders: Binders,
    requires: Vec<fhir::Constraint>,
}

/// Keeps track of the surface level identifiers in scope and a mapping between them and a
/// [`Binder`].
struct Binders {
    name_gen: IndexGen<fhir::Name>,
    layers: Vec<Layer>,
}

#[derive(Default, Debug)]
struct Layer {
    map: FxIndexMap<surface::Ident, Binder>,
}

/// The different kind of binders that can appear in the surface syntax
#[derive(Debug, Clone)]
enum Binder {
    /// A normal binder to a refinable type that will be desugared as an explicit parameter.
    /// The boolean indicates whether the binder was declared _implicitly_ with the `@` or `#`
    /// syntax and it is used to determine the [inference mode] for abstract refinements.
    ///
    /// [inference mode]: fhir::InferMode
    Refined(fhir::Name, fhir::Sort, /*implicit*/ bool),
    /// A binder to an unrefinable type (a type that cannot be refined). We try to catch this
    /// situation "eagerly" as it will often result in better error messages, e.g., we will
    /// fail if a type parameter `T` (which cannot be refined) is used as an indexed type
    /// `T[@a]` or as an existential `T{v : v > 0}`, but unrefined binders can appear when
    /// using argument syntax (`x: T`), thus we track them and report appropriate errors if
    /// they are used in any way.
    Unrefined,
}

struct ExprCtxt<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    binders: &'a Binders,
}

enum FuncRes<'a> {
    Param(fhir::Name, &'a fhir::Sort),
    Uif(&'a fhir::UifDef),
}

impl<'a, 'tcx> DesugarCtxt<'a, 'tcx> {
    fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>, binders: Binders) -> DesugarCtxt<'a, 'tcx> {
        DesugarCtxt { early_cx, binders, requires: vec![] }
    }

    fn as_expr_ctxt(&self) -> ExprCtxt<'_, 'tcx> {
        ExprCtxt::new(self.early_cx, &self.binders)
    }

    fn desugar_fun_arg(&mut self, arg: &surface::Arg<Res>) -> Result<fhir::Ty, ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                let ty = match self.desugar_path(path)? {
                    BtyOrTy::Bty(bty) => {
                        let idx = self.bind_into_refine_arg(*bind)?;
                        let kind = fhir::TyKind::Indexed(bty, idx);
                        fhir::Ty { kind, span: path.span }
                    }
                    BtyOrTy::Ty(ty) => ty,
                };
                let kind =
                    fhir::TyKind::Constr(self.as_expr_ctxt().desugar_expr(pred)?, Box::new(ty));
                let span = path.span.to(pred.span);
                Ok(fhir::Ty { kind, span })
            }
            surface::Arg::StrgRef(loc, ty) => {
                let span = loc.span;
                let loc = self.as_expr_ctxt().desugar_loc(*loc)?;
                let ty = self.desugar_ty(None, ty)?;
                self.requires.push(fhir::Constraint::Type(loc, ty));
                let kind = fhir::TyKind::Ptr(loc);
                Ok(fhir::Ty { kind, span })
            }
            surface::Arg::Ty(bind, ty) => self.desugar_ty(*bind, ty),
        }
    }

    fn desugar_ty(
        &mut self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty<Res>,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        let span = ty.span;
        let kind = match &ty.kind {
            surface::TyKind::Base(bty) => return self.desugar_bty_bind(bind, bty),
            surface::TyKind::Indexed { bty, indices } => {
                match self.desugar_bty(bty)? {
                    BtyOrTy::Bty(bty) => {
                        let idx = self.desugar_indices(&bty, indices)?;
                        fhir::TyKind::Indexed(bty, idx)
                    }
                    BtyOrTy::Ty(_) => {
                        return Err(self.early_cx.emit_err(errors::ParamCountMismatch::new(
                            indices.span,
                            0,
                            indices.indices.len(),
                        )));
                    }
                }
            }
            surface::TyKind::Exists { bind: ident, bty, pred } => {
                match self.desugar_bty(bty)? {
                    BtyOrTy::Bty(bty) => {
                        self.binders.push_layer();

                        let name = self.binders.fresh();
                        let binder = Binder::Refined(name, bty.sort(), false);
                        self.binders.insert_binder(self.sess(), *ident, binder)?;
                        let pred = self.as_expr_ctxt().desugar_expr(pred)?;
                        let bind = fhir::Ident::new(name, *ident);

                        self.binders.pop_layer();
                        fhir::TyKind::Exists(bty, bind, pred)
                    }
                    BtyOrTy::Ty(_) => {
                        return Err(self
                            .early_cx
                            .emit_err(errors::ParamCountMismatch::new(ident.span, 0, 1)));
                    }
                }
            }
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.as_expr_ctxt().desugar_expr(pred)?;
                let ty = self.desugar_ty(None, ty)?;
                fhir::TyKind::Constr(pred, Box::new(ty))
            }
            surface::TyKind::Ref(rk, ty) => {
                fhir::TyKind::Ref(desugar_ref_kind(*rk), Box::new(self.desugar_ty(None, ty)?))
            }
            surface::TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.desugar_ty(None, ty))
                    .try_collect_exhaust()?;
                fhir::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.desugar_ty(None, ty)?;
                fhir::TyKind::Array(Box::new(ty), fhir::ArrayLen { val: len.val })
            }
        };
        Ok(fhir::Ty { kind, span })
    }

    fn desugar_indices(
        &mut self,
        bty: &fhir::BaseTy,
        idxs: &surface::Indices,
    ) -> Result<fhir::RefineArg, ErrorGuaranteed> {
        if let Some(def_id) = bty.is_aggregate() && idxs.indices.len() != 1 {
            let flds = self.desugar_refine_args(&idxs.indices)?;
            Ok(fhir::RefineArg::Aggregate(def_id, flds, idxs.span))
        } else {
            let arg = idxs.indices.first().unwrap();
            self.desugar_refine_arg(arg)
        }
    }

    fn desugar_refine_args(
        &mut self,
        args: &[surface::RefineArg],
    ) -> Result<Vec<fhir::RefineArg>, ErrorGuaranteed> {
        args.iter()
            .map(|idx| self.desugar_refine_arg(idx))
            .try_collect_exhaust()
    }

    fn bind_into_refine_arg(
        &self,
        ident: surface::Ident,
    ) -> Result<fhir::RefineArg, ErrorGuaranteed> {
        match self.binders.get(ident) {
            Some(Binder::Refined(name, ..)) => {
                let kind = fhir::ExprKind::Var(fhir::Ident::new(*name, ident));
                let expr = fhir::Expr { kind, span: ident.span };
                Ok(fhir::RefineArg::Expr { expr, is_binder: true })
            }
            Some(Binder::Unrefined) => span_bug!(ident.span, "desugaring unrefined binder"),
            None => Err(self.early_cx.emit_err(errors::UnresolvedVar::new(ident))),
        }
    }

    fn desugar_refine_arg(
        &mut self,
        arg: &surface::RefineArg,
    ) -> Result<fhir::RefineArg, ErrorGuaranteed> {
        match arg {
            surface::RefineArg::Bind(ident, ..) => self.bind_into_refine_arg(*ident),
            surface::RefineArg::Expr(expr) => {
                Ok(fhir::RefineArg::Expr {
                    expr: self.as_expr_ctxt().desugar_expr(expr)?,
                    is_binder: false,
                })
            }
            surface::RefineArg::Abs(params, body, span) => {
                self.binders.push_layer();
                self.binders.insert_params(self.early_cx, params)?;
                let body = self.as_expr_ctxt().desugar_expr(body)?;
                let params = self.binders.pop_layer().into_params();
                Ok(fhir::RefineArg::Abs(params, body, *span))
            }
        }
    }

    fn desugar_bty(&mut self, bty: &surface::BaseTy<Res>) -> Result<BtyOrTy, ErrorGuaranteed> {
        let bty = match &bty.kind {
            surface::BaseTyKind::Path(path) => self.desugar_path(path)?,
            surface::BaseTyKind::Slice(ty) => {
                let kind = fhir::BaseTyKind::Slice(Box::new(self.desugar_ty(None, ty)?));
                let bty = fhir::BaseTy { kind, span: bty.span };
                BtyOrTy::Bty(bty)
            }
        };
        Ok(bty)
    }

    fn desugar_path(&mut self, path: &surface::Path<Res>) -> Result<BtyOrTy, ErrorGuaranteed> {
        let res = match &path.res {
            Res::PrimTy(PrimTy::Bool) => fhir::Res::Bool,
            Res::PrimTy(PrimTy::Int(int_ty)) => fhir::Res::Int(*int_ty),
            Res::PrimTy(PrimTy::Uint(uint_ty)) => fhir::Res::Uint(*uint_ty),
            Res::PrimTy(PrimTy::Char) => fhir::Res::Char,
            Res::PrimTy(PrimTy::Str) => fhir::Res::Str,
            Res::PrimTy(PrimTy::Float(float_ty)) => fhir::Res::Float(*float_ty),
            Res::Adt(def_id) => fhir::Res::Adt(*def_id),
            Res::Alias(def_id) => {
                fhir::Res::Alias(*def_id, self.desugar_refine_args(&path.refine)?)
            }
            Res::Param(def_id) => {
                let kind = fhir::TyKind::Param(*def_id);
                return Ok(fhir::Ty { kind, span: path.span }.into());
            }
        };
        let generics = self.desugar_generic_args(&path.generics)?;
        Ok(fhir::BaseTy::from(fhir::Path { res, generics, span: path.span }).into())
    }

    fn desugar_generic_args(
        &mut self,
        substs: &[surface::Ty<Res>],
    ) -> Result<Vec<fhir::Ty>, ErrorGuaranteed> {
        substs
            .iter()
            .map(|ty| self.desugar_ty(None, ty))
            .try_collect_exhaust()
    }

    fn desugar_bty_bind(
        &mut self,
        bind: Option<surface::Ident>,
        bty: &surface::BaseTy<Res>,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        match self.desugar_bty(bty)? {
            BtyOrTy::Bty(bty) => {
                let span = bty.span;
                let kind = if let Some(bind) = bind {
                    let idx = self.bind_into_refine_arg(bind)?;
                    fhir::TyKind::Indexed(bty, idx)
                } else {
                    fhir::TyKind::BaseTy(bty)
                };
                Ok(fhir::Ty { kind, span })
            }
            BtyOrTy::Ty(ty) => Ok(ty),
        }
    }
    fn desugar_variant_ret(
        &mut self,
        ret: &surface::VariantRet<Res>,
    ) -> Result<fhir::VariantRet, ErrorGuaranteed> {
        match self.desugar_path(&ret.path)? {
            BtyOrTy::Bty(bty) => {
                let idx = self.desugar_indices(&bty, &ret.indices)?;
                Ok(fhir::VariantRet { bty, idx })
            }
            BtyOrTy::Ty(_) => {
                // This shouldn't happen because during annot_check we are checking
                // the path resolves to the correct type.
                panic!("variant output desugared to an unrefined type")
            }
        }
    }

    fn sess(&self) -> &'a FluxSession {
        self.early_cx.sess
    }
}

impl<'a, 'tcx> ExprCtxt<'a, 'tcx> {
    fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>, binders: &'a Binders) -> Self {
        Self { early_cx, binders }
    }

    fn desugar_expr(&self, expr: &surface::Expr) -> Result<fhir::Expr, ErrorGuaranteed> {
        let kind = match &expr.kind {
            surface::ExprKind::Var(ident) => return self.desugar_var(*ident),
            surface::ExprKind::Literal(lit) => {
                fhir::ExprKind::Literal(self.desugar_lit(expr.span, *lit)?)
            }
            surface::ExprKind::BinaryOp(op, box [e1, e2]) => {
                let e1 = self.desugar_expr(e1);
                let e2 = self.desugar_expr(e2);
                fhir::ExprKind::BinaryOp(desugar_bin_op(*op), Box::new([e1?, e2?]))
            }
            surface::ExprKind::UnaryOp(op, box e) => {
                fhir::ExprKind::UnaryOp(desugar_un_op(*op), Box::new(self.desugar_expr(e)?))
            }
            surface::ExprKind::Dot(box e, fld) => {
                if let fhir::ExprKind::Var(var) = self.desugar_expr(e)?.kind {
                    fhir::ExprKind::Dot(var, *fld)
                } else {
                    return Err(self
                        .early_cx
                        .emit_err(errors::InvalidDotVar { span: expr.span }));
                }
            }
            surface::ExprKind::App(func, args) => {
                let args = self.desugar_exprs(args)?;
                match self.resolve_func(*func)? {
                    FuncRes::Uif(_) => {
                        fhir::ExprKind::App(fhir::Func::Uif(func.name, func.span), args)
                    }
                    FuncRes::Param(name, _) => {
                        let func = fhir::Func::Var(fhir::Ident::new(name, *func));
                        fhir::ExprKind::App(func, args)
                    }
                }
            }
            surface::ExprKind::IfThenElse(box [p, e1, e2]) => {
                let p = self.desugar_expr(p);
                let e1 = self.desugar_expr(e1);
                let e2 = self.desugar_expr(e2);
                fhir::ExprKind::IfThenElse(Box::new([p?, e1?, e2?]))
            }
        };
        Ok(fhir::Expr { kind, span: expr.span })
    }

    fn desugar_exprs(&self, exprs: &[surface::Expr]) -> Result<Vec<fhir::Expr>, ErrorGuaranteed> {
        exprs
            .iter()
            .map(|e| self.desugar_expr(e))
            .try_collect_exhaust()
    }

    fn resolve_func(&self, func: surface::Ident) -> Result<FuncRes, ErrorGuaranteed> {
        if let Some(b) = self.binders.get(func) {
            match b {
                Binder::Refined(name, sort, _) => return Ok(FuncRes::Param(*name, sort)),
                Binder::Unrefined => {
                    return Err(self
                        .early_cx
                        .emit_err(errors::InvalidUnrefinedParam::new(func)));
                }
            }
        }
        if let Some(uif) = self.early_cx.uif(func.name) {
            return Ok(FuncRes::Uif(uif));
        }
        Err(self.early_cx.emit_err(errors::UnresolvedVar::new(func)))
    }

    fn desugar_lit(&self, span: Span, lit: surface::Lit) -> Result<fhir::Lit, ErrorGuaranteed> {
        match lit.kind {
            surface::LitKind::Integer => {
                let Ok(n) = lit.symbol.as_str().parse::<i128>() else {
                    return Err(self.early_cx.emit_err(errors::IntTooLarge { span }));
                };
                let suffix = lit.suffix.unwrap_or(SORTS.int);
                if suffix == SORTS.int {
                    Ok(fhir::Lit::Int(n))
                } else if suffix == SORTS.real {
                    Ok(fhir::Lit::Real(n))
                } else {
                    Err(self
                        .early_cx
                        .emit_err(errors::InvalidNumericSuffix::new(span, suffix)))
                }
            }
            surface::LitKind::Bool => Ok(fhir::Lit::Bool(lit.symbol == kw::True)),
            _ => Err(self.early_cx.emit_err(errors::UnexpectedLiteral { span })),
        }
    }

    fn desugar_var(&self, ident: surface::Ident) -> Result<fhir::Expr, ErrorGuaranteed> {
        let kind = match (self.binders.get(ident), self.early_cx.const_by_name(ident.name)) {
            (Some(Binder::Refined(name, ..)), _) => {
                fhir::ExprKind::Var(fhir::Ident::new(*name, ident))
            }
            (Some(Binder::Unrefined), _) => {
                return Err(self
                    .early_cx
                    .emit_err(errors::InvalidUnrefinedParam::new(ident)));
            }
            (None, Some(const_info)) => fhir::ExprKind::Const(const_info.def_id, ident.span),
            (None, None) => return Err(self.early_cx.emit_err(errors::UnresolvedVar::new(ident))),
        };
        Ok(fhir::Expr { kind, span: ident.span })
    }

    fn desugar_loc(&self, loc: surface::Ident) -> Result<fhir::Ident, ErrorGuaranteed> {
        match self.binders.get(loc) {
            Some(&Binder::Refined(name, ..)) => Ok(fhir::Ident::new(name, loc)),
            Some(binder @ Binder::Unrefined) => {
                // This shouldn't happen because loc bindings in input position should
                // already be inserted as Binder::Single when gathering parameters and
                // locs in ensure clauses are guaranteed to be locs during annot_check.
                panic!("aggregate or unrefined binder used in loc position: `{binder:?}`")
            }
            None => Err(self.early_cx.emit_err(errors::UnresolvedVar::new(loc))),
        }
    }
}

fn desugar_ref_kind(rk: surface::RefKind) -> fhir::RefKind {
    match rk {
        surface::RefKind::Mut => fhir::RefKind::Mut,
        surface::RefKind::Shr => fhir::RefKind::Shr,
    }
}

fn resolve_sort(early_cx: &EarlyCtxt, sort: &surface::Sort) -> Result<fhir::Sort, ErrorGuaranteed> {
    match sort {
        surface::Sort::Base(sort) => resolve_base_sort(early_cx, *sort),
        surface::Sort::Func { inputs, output } => {
            Ok(resolve_func_sort(early_cx, inputs, output)?.into())
        }
        surface::Sort::Infer => Ok(fhir::Sort::Infer),
    }
}

fn resolve_func_sort(
    early_cx: &EarlyCtxt,
    inputs: &[surface::Ident],
    output: &surface::Ident,
) -> Result<fhir::FuncSort, ErrorGuaranteed> {
    let mut inputs_and_output: Vec<fhir::Sort> = inputs
        .iter()
        .map(|sort| resolve_base_sort(early_cx, *sort))
        .try_collect_exhaust()?;
    inputs_and_output.push(resolve_base_sort(early_cx, *output)?);
    Ok(fhir::FuncSort { inputs_and_output: List::from_vec(inputs_and_output) })
}

fn resolve_base_sort(
    early_cx: &EarlyCtxt,
    sort: surface::Ident,
) -> Result<fhir::Sort, ErrorGuaranteed> {
    if sort.name == SORTS.int {
        Ok(fhir::Sort::Int)
    } else if sort.name == sym::bool {
        Ok(fhir::Sort::Bool)
    } else if sort.name == SORTS.real {
        Ok(fhir::Sort::Real)
    } else if early_cx.sort_decl(sort.name).is_some() {
        Ok(fhir::Sort::User(sort.name))
    } else {
        Err(early_cx.emit_err(errors::UnresolvedSort::new(sort)))
    }
}

impl Binders {
    fn new() -> Binders {
        Binders { name_gen: IndexGen::new(), layers: vec![Layer::default()] }
    }

    fn from_params<'a>(
        early_cx: &EarlyCtxt,
        params: impl IntoIterator<Item = &'a surface::RefineParam>,
    ) -> Result<Self, ErrorGuaranteed> {
        let mut binders = Self::new();
        binders.insert_params(early_cx, params)?;
        Ok(binders)
    }

    fn insert_params<'a>(
        &mut self,
        early_cx: &EarlyCtxt,
        params: impl IntoIterator<Item = &'a surface::RefineParam>,
    ) -> Result<(), ErrorGuaranteed> {
        for param in params {
            self.insert_binder(
                early_cx.sess,
                param.name,
                Binder::Refined(self.fresh(), resolve_sort(early_cx, &param.sort)?, false),
            )?;
        }
        Ok(())
    }

    fn fresh(&self) -> fhir::Name {
        self.name_gen.fresh()
    }

    fn get(&self, ident: impl Borrow<surface::Ident>) -> Option<&Binder> {
        self.iter_layers(|layer| layer.get(ident.borrow()))
    }

    fn insert_binder(
        &mut self,
        sess: &FluxSession,
        ident: surface::Ident,
        binder: Binder,
    ) -> Result<(), ErrorGuaranteed> {
        self.top_layer().insert(sess, ident, binder)
    }

    fn gather_params_variant(
        &mut self,
        early_cx: &EarlyCtxt,
        variant_def: &surface::VariantDef<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        let Some(data) = &variant_def.data else {
            return Ok(())
        };
        for ty in &data.fields {
            self.gather_params_ty(early_cx, None, ty, TypePos::Input)?;
        }
        // Traverse return type to find illegal binders.
        self.gather_params_path(early_cx, &data.ret.path, TypePos::Other)?;
        // Check binders in `VariantRet`
        data.ret.indices.indices.iter().try_for_each_exhaust(|idx| {
            if let surface::RefineArg::Bind(_, kind, span) = idx {
                Err(early_cx.emit_err(errors::IllegalBinder::new(*span, *kind)))
            } else {
                Ok(())
            }
        })
    }

    fn gather_input_params_fn_sig(
        &mut self,
        early_cx: &EarlyCtxt,
        fn_sig: &surface::FnSig<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        for param in &fn_sig.params {
            self.insert_binder(
                early_cx.sess,
                param.name,
                Binder::Refined(self.fresh(), resolve_sort(early_cx, &param.sort)?, false),
            )?;
        }
        for arg in &fn_sig.args {
            self.gather_params_fun_arg(early_cx, arg)?;
        }

        Ok(())
    }

    fn gather_output_params_fn_sig(
        &mut self,
        early_cx: &EarlyCtxt,
        fn_sig: &surface::FnSig<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        if let Some(ret_ty) = &fn_sig.returns {
            self.gather_params_ty(early_cx, None, ret_ty, TypePos::Output)?;
        }
        for (_, ty) in &fn_sig.ensures {
            self.gather_params_ty(early_cx, None, ty, TypePos::Output)?;
        }
        Ok(())
    }

    fn gather_params_fun_arg(
        &mut self,
        early_cx: &EarlyCtxt,
        arg: &surface::Arg<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, _) => {
                self.insert_binder(
                    early_cx.sess,
                    *bind,
                    Binder::from_res(&self.name_gen, path.res),
                )?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.insert_binder(
                    early_cx.sess,
                    *loc,
                    Binder::Refined(self.fresh(), fhir::Sort::Loc, false),
                )?;
                self.gather_params_ty(early_cx, None, ty, TypePos::Input)?;
            }
            surface::Arg::Ty(bind, ty) => {
                self.gather_params_ty(early_cx, *bind, ty, TypePos::Input)?;
            }
        }
        Ok(())
    }

    fn gather_params_ty(
        &mut self,
        early_cx: &EarlyCtxt,
        bind: Option<surface::Ident>,
        ty: &surface::Ty<Res>,
        pos: TypePos,
    ) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            surface::TyKind::Indexed { bty, indices } => {
                if let Some(bind) = bind {
                    self.insert_binder(early_cx.sess, bind, Binder::Unrefined)?;
                }
                if let [surface::RefineArg::Bind(ident, kind, span)] = indices.indices[..] {
                    let binder = Binder::from_bty(&self.name_gen, bty);
                    if !pos.is_binder_allowed(kind) {
                        return Err(early_cx.emit_err(errors::IllegalBinder::new(span, kind)));
                    }
                    self.insert_binder(early_cx.sess, ident, binder)?;
                } else {
                    let refined_by = index_sorts(early_cx, bty);
                    let exp = refined_by.len();
                    let got = indices.indices.len();
                    if exp != got {
                        return Err(
                            early_cx.emit_err(errors::ParamCountMismatch::new(ty.span, exp, got))
                        );
                    }

                    for (idx, sort) in iter::zip(&indices.indices, refined_by) {
                        if let surface::RefineArg::Bind(ident, kind, span) = idx {
                            if !pos.is_binder_allowed(*kind) {
                                return Err(
                                    early_cx.emit_err(errors::IllegalBinder::new(*span, *kind))
                                );
                            }
                            let name = self.name_gen.fresh();
                            self.insert_binder(
                                early_cx.sess,
                                *ident,
                                Binder::Refined(name, sort.clone(), true),
                            )?;
                        }
                    }
                }
                self.gather_params_bty(early_cx, bty, pos)
            }
            surface::TyKind::Base(bty) => {
                if let Some(bind) = bind {
                    self.insert_binder(early_cx.sess, bind, Binder::from_bty(&self.name_gen, bty))?;
                }
                self.gather_params_bty(early_cx, bty, pos)
            }

            surface::TyKind::Ref(_, ty) | surface::TyKind::Constr(_, ty) => {
                if let Some(bind) = bind {
                    self.insert_binder(early_cx.sess, bind, Binder::Unrefined)?;
                }
                self.gather_params_ty(early_cx, None, ty, pos)
            }
            surface::TyKind::Tuple(tys) => {
                if let Some(bind) = bind {
                    self.insert_binder(early_cx.sess, bind, Binder::Unrefined)?;
                }
                for ty in tys {
                    self.gather_params_ty(early_cx, None, ty, pos)?;
                }
                Ok(())
            }
            surface::TyKind::Array(ty, _) => {
                self.gather_params_ty(early_cx, None, ty, TypePos::Other)
            }
            surface::TyKind::Exists { bty, .. } => {
                if let Some(bind) = bind {
                    self.insert_binder(early_cx.sess, bind, Binder::Unrefined)?;
                }
                self.gather_params_bty(early_cx, bty, pos)
            }
        }
    }

    fn gather_params_path(
        &mut self,
        early_cx: &EarlyCtxt,
        path: &surface::Path<Res>,
        pos: TypePos,
    ) -> Result<(), ErrorGuaranteed> {
        let pos = if is_box(early_cx, path.res) { pos } else { TypePos::Other };
        path.generics
            .iter()
            .try_for_each_exhaust(|ty| self.gather_params_ty(early_cx, None, ty, pos))
    }

    fn gather_params_bty(
        &mut self,
        early_cx: &EarlyCtxt,
        bty: &surface::BaseTy<Res>,
        pos: TypePos,
    ) -> Result<(), ErrorGuaranteed> {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => self.gather_params_path(early_cx, path, pos),
            surface::BaseTyKind::Slice(ty) => {
                self.gather_params_ty(early_cx, None, ty, TypePos::Other)
            }
        }
    }

    fn top_layer(&mut self) -> &mut Layer {
        self.layers.last_mut().unwrap()
    }

    fn iter_layers<'a, T>(&'a self, f: impl FnMut(&'a Layer) -> Option<T>) -> Option<T> {
        self.layers.iter().rev().find_map(f)
    }

    fn push_layer(&mut self) {
        self.layers.push(Layer::default());
    }

    fn pop_layer(&mut self) -> Layer {
        self.layers.pop().unwrap()
    }
}

fn infer_mode(implicit: bool, sort: &fhir::Sort) -> fhir::InferMode {
    if !implicit && sort.is_pred() {
        fhir::InferMode::KVar
    } else {
        fhir::InferMode::EVar
    }
}

fn is_box(early_cx: &EarlyCtxt, res: surface::Res) -> bool {
    if let Res::Adt(def_id) = res {
        early_cx.tcx.adt_def(def_id).is_box()
    } else {
        false
    }
}

impl<T: Borrow<surface::Ident>> std::ops::Index<T> for Binders {
    type Output = Binder;

    fn index(&self, index: T) -> &Self::Output {
        self.get(index).unwrap()
    }
}

fn param_from_ident(
    ident: surface::Ident,
    name: fhir::Name,
    sort: fhir::Sort,
    mode: fhir::InferMode,
) -> fhir::FunRefineParam {
    let name = fhir::Ident::new(name, ident);
    fhir::FunRefineParam { name, sort, mode }
}

fn desugar_bin_op(op: surface::BinOp) -> fhir::BinOp {
    match op {
        surface::BinOp::Iff => fhir::BinOp::Iff,
        surface::BinOp::Imp => fhir::BinOp::Imp,
        surface::BinOp::Or => fhir::BinOp::Or,
        surface::BinOp::And => fhir::BinOp::And,
        surface::BinOp::Eq => fhir::BinOp::Eq,
        surface::BinOp::Ne => fhir::BinOp::Ne,
        surface::BinOp::Gt => fhir::BinOp::Gt,
        surface::BinOp::Ge => fhir::BinOp::Ge,
        surface::BinOp::Lt => fhir::BinOp::Lt,
        surface::BinOp::Le => fhir::BinOp::Le,
        surface::BinOp::Add => fhir::BinOp::Add,
        surface::BinOp::Sub => fhir::BinOp::Sub,
        surface::BinOp::Mod => fhir::BinOp::Mod,
        surface::BinOp::Mul => fhir::BinOp::Mul,
        surface::BinOp::Div => fhir::BinOp::Div,
    }
}

fn desugar_un_op(op: surface::UnOp) -> fhir::UnOp {
    match op {
        surface::UnOp::Not => fhir::UnOp::Not,
        surface::UnOp::Neg => fhir::UnOp::Neg,
    }
}

impl Layer {
    fn get(&self, key: impl Borrow<surface::Ident>) -> Option<&Binder> {
        self.map.get(key.borrow())
    }

    fn insert(
        &mut self,
        sess: &FluxSession,
        ident: surface::Ident,
        binder: Binder,
    ) -> Result<(), ErrorGuaranteed> {
        match self.map.entry(ident) {
            IndexEntry::Occupied(entry) => {
                Err(sess.emit_err(errors::DuplicateParam::new(*entry.key(), ident)))
            }
            IndexEntry::Vacant(entry) => {
                entry.insert(binder);
                Ok(())
            }
        }
    }

    fn into_params(self) -> Vec<(fhir::Ident, fhir::Sort)> {
        let mut args = vec![];
        for (ident, binder) in self.map {
            if let Binder::Refined(name, sort, _) = binder {
                let name = fhir::Ident::new(name, ident);
                args.push((name, sort));
            } else {
                span_bug!(ident.span, "unexpected refined binder");
            }
        }
        args
    }

    fn into_fun_params(self) -> Vec<fhir::FunRefineParam> {
        let mut params = vec![];
        for (ident, binder) in self.map {
            match binder {
                Binder::Refined(name, sort, implicit) => {
                    params.push(param_from_ident(
                        ident,
                        name,
                        sort.clone(),
                        infer_mode(implicit, &sort),
                    ));
                }
                Binder::Unrefined => {}
            }
        }
        params
    }
}

impl Binder {
    fn from_res(name_gen: &IndexGen<fhir::Name>, res: surface::Res) -> Binder {
        let sort = match res {
            Res::PrimTy(PrimTy::Bool) => fhir::Sort::Bool,
            Res::PrimTy(PrimTy::Int(_) | PrimTy::Uint(_)) => fhir::Sort::Int,
            Res::Alias(def_id) | Res::Adt(def_id) => fhir::Sort::Aggregate(def_id),
            Res::PrimTy(PrimTy::Float(_) | PrimTy::Str | PrimTy::Char) => fhir::Sort::Unit,
            Res::Param(..) => {
                return Binder::Unrefined;
            }
        };
        Binder::Refined(name_gen.fresh(), sort, true)
    }

    fn from_bty(name_gen: &IndexGen<fhir::Name>, bty: &surface::BaseTy<Res>) -> Binder {
        match &bty.kind {
            surface::BaseTyKind::Path(path) => Binder::from_res(name_gen, path.res),
            surface::BaseTyKind::Slice(_) => {
                Binder::Refined(name_gen.fresh(), fhir::Sort::Int, true)
            }
        }
    }
}

fn index_sorts<'a>(early_cx: &'a EarlyCtxt, bty: &surface::BaseTy<Res>) -> &'a [fhir::Sort] {
    match &bty.kind {
        surface::BaseTyKind::Path(path) => {
            match path.res {
                Res::PrimTy(PrimTy::Bool) => &[fhir::Sort::Bool],
                Res::PrimTy(PrimTy::Int(_) | PrimTy::Uint(_)) => &[fhir::Sort::Int],
                Res::Adt(def_id) | Res::Alias(def_id) => early_cx.index_sorts_of(def_id),
                Res::PrimTy(PrimTy::Char | PrimTy::Str | PrimTy::Float(_)) | Res::Param(..) => &[],
            }
        }
        surface::BaseTyKind::Slice(_) => &[fhir::Sort::Bool],
    }
}

#[derive(Clone, Copy)]
enum TypePos {
    /// Type in input position allowing `@n` binders
    Input,
    /// Type in output position allowing `#n` binders
    Output,
    /// Any other position which doesn't allow binders, e.g., inside generic arguments (except for boxes)
    Other,
}

impl TypePos {
    fn is_binder_allowed(self, kind: surface::BindKind) -> bool {
        match self {
            TypePos::Input => matches!(kind, surface::BindKind::At),
            TypePos::Output => matches!(kind, surface::BindKind::Pound),
            TypePos::Other => false,
        }
    }
}

struct Sorts {
    int: Symbol,
    real: Symbol,
}

static SORTS: std::sync::LazyLock<Sorts> =
    std::sync::LazyLock::new(|| Sorts { int: Symbol::intern("int"), real: Symbol::intern("real") });

mod errors {
    use flux_macros::Diagnostic;
    use flux_syntax::surface::BindKind;
    use rustc_span::{symbol::Ident, Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(desugar::unresolved_var, code = "FLUX")]
    pub(super) struct UnresolvedVar {
        #[primary_span]
        #[label]
        span: Span,
        var: Ident,
    }

    impl UnresolvedVar {
        pub(super) fn new(var: Ident) -> Self {
            Self { span: var.span, var }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::duplicate_param, code = "FLUX")]
    pub(super) struct DuplicateParam {
        #[primary_span]
        #[label]
        span: Span,
        name: Symbol,
        #[label(desugar::first_use)]
        first_use: Span,
    }

    impl DuplicateParam {
        pub(super) fn new(old_ident: Ident, new_ident: Ident) -> Self {
            debug_assert_eq!(old_ident.name, new_ident.name);
            Self { span: new_ident.span, name: new_ident.name, first_use: old_ident.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::unresolved_sort, code = "FLUX")]
    pub(super) struct UnresolvedSort {
        #[primary_span]
        #[label]
        span: Span,
        sort: Ident,
    }

    impl UnresolvedSort {
        pub(super) fn new(sort: Ident) -> Self {
            Self { span: sort.span, sort }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::int_too_large, code = "FLUX")]
    pub(super) struct IntTooLarge {
        #[primary_span]
        pub(super) span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar::unexpected_literal, code = "FLUX")]
    pub(super) struct UnexpectedLiteral {
        #[primary_span]
        pub(super) span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar::invalid_dot_var, code = "FLUX")]
    pub(super) struct InvalidDotVar {
        #[primary_span]
        pub(super) span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar::param_count_mismatch, code = "FLUX")]
    pub(super) struct ParamCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        expected: String,
        found: usize,
    }

    impl ParamCountMismatch {
        pub(super) fn new(span: Span, exp: usize, found: usize) -> Self {
            let expected = if exp > 1 { format!("1 or {exp:?}") } else { exp.to_string() };
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::invalid_unrefined_param, code = "FLUX")]
    pub(super) struct InvalidUnrefinedParam {
        #[primary_span]
        #[label]
        span: Span,
        var: Ident,
    }

    impl InvalidUnrefinedParam {
        pub(super) fn new(var: Ident) -> Self {
            Self { var, span: var.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::illegal_binder, code = "FLUX")]
    pub(super) struct IllegalBinder {
        #[primary_span]
        #[label]
        span: Span,
        kind: &'static str,
    }

    impl IllegalBinder {
        pub(super) fn new(span: Span, kind: BindKind) -> Self {
            Self { span, kind: kind.token_str() }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::invalid_numeric_suffix, code = "FLUX")]
    pub(super) struct InvalidNumericSuffix {
        #[primary_span]
        #[label]
        span: Span,
        suffix: Symbol,
    }

    impl InvalidNumericSuffix {
        pub(super) fn new(span: Span, suffix: Symbol) -> Self {
            Self { span, suffix }
        }
    }
}
