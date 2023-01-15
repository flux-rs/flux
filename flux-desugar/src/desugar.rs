//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]
use std::{borrow::Borrow, iter};

use flux_common::{bug, index::IndexGen, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::{fhir, intern::List};
use flux_syntax::surface::{self, Res, TyCtxt};
use itertools::Itertools;
use rustc_data_structures::fx::{FxIndexMap, IndexEntry};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_span::{sym, symbol::kw, Span, Symbol};

pub fn desugar_qualifier(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    qualifier: &surface::Qualifier,
) -> Result<fhir::Qualifier, ErrorGuaranteed> {
    let mut binders = Binders::from_params(sess, map, &qualifier.args)?;
    let name = qualifier.name.name.to_ident_string();
    let expr = ExprCtxt::new(tcx, sess, map, &binders).desugar_expr(&qualifier.expr);

    Ok(fhir::Qualifier {
        name,
        args: binders.pop_layer().into_args(),
        global: qualifier.global,
        expr: expr?,
    })
}

pub fn desugar_defn(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    defn: surface::Defn,
) -> Result<fhir::Defn, ErrorGuaranteed> {
    let mut binders = Binders::from_params(sess, map, &defn.args.params)?;
    let expr = ExprCtxt::new(tcx, sess, map, &binders).desugar_expr(&defn.expr)?;
    let name = defn.name.name;
    let sort = resolve_sort(sess, map, &defn.sort)?;
    let args = binders.pop_layer().into_args();
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
    sess: &FluxSession,
    map: &fhir::Map,
    defn: &surface::Defn,
) -> Result<fhir::UifDef, ErrorGuaranteed> {
    let inputs: Vec<surface::Ident> = defn
        .args
        .iter()
        .map(|arg| sort_ident(&arg.sort))
        .try_collect_exhaust()?;
    let output: surface::Ident = sort_ident(&defn.sort)?;
    let sort = resolve_func_sort(sess, map, &inputs[..], &output)?;
    Ok(fhir::UifDef { name: defn.name.name, sort })
}

pub fn resolve_uif_def(
    sess: &FluxSession,
    map: &fhir::Map,
    defn: surface::UifDef,
) -> Result<fhir::UifDef, ErrorGuaranteed> {
    let inputs: Vec<surface::Ident> = defn
        .args
        .iter()
        .map(|arg| sort_ident(&arg.sort))
        .try_collect_exhaust()?;
    let output: surface::Ident = sort_ident(&defn.sort)?;
    let sort = resolve_func_sort(sess, map, &inputs[..], &output)?;
    Ok(fhir::UifDef { name: defn.name.name, sort })
}

pub fn desugar_adt_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    def_id: DefId,
    refined_by: &surface::RefinedBy,
    invariants: &[surface::Expr],
    opaque: bool,
) -> Result<fhir::AdtDef, ErrorGuaranteed> {
    let mut binders = Binders::from_params(sess, map, refined_by)?;

    let invariants = invariants
        .iter()
        .map(|invariant| ExprCtxt::new(tcx, sess, map, &binders).desugar_expr(invariant))
        .try_collect_exhaust()?;

    let refined_by =
        fhir::RefinedBy { params: binders.pop_layer().into_args(), span: refined_by.span };
    Ok(fhir::AdtDef::new(def_id, refined_by, invariants, opaque))
}

pub fn desugar_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    adt_def: surface::StructDef<Res>,
) -> Result<fhir::StructDef, ErrorGuaranteed> {
    let def_id = adt_def.def_id.to_def_id();
    let binders = Binders::from_params(sess, map, adt_def.refined_by.iter().flatten())?;

    let mut cx = DesugarCtxt::new(tcx, sess, map, binders);

    let kind = if adt_def.opaque {
        fhir::StructKind::Opaque
    } else {
        let fields = adt_def
            .fields
            .iter()
            .map(|ty| ty.as_ref().map(|ty| cx.desugar_ty(None, ty)).transpose())
            .try_collect_exhaust()?;
        fhir::StructKind::Transparent { fields }
    };
    Ok(fhir::StructDef { def_id, kind })
}

pub fn desugar_enum_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    enum_def: &surface::EnumDef<Res>,
) -> Result<fhir::EnumDef, ErrorGuaranteed> {
    let def_id = enum_def.def_id.to_def_id();
    let variants = enum_def
        .variants
        .iter()
        .map(|variant| desugar_variant(tcx, sess, map, variant))
        .try_collect_exhaust()?;

    Ok(fhir::EnumDef { def_id, variants })
}

fn desugar_variant(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    variant: &surface::VariantDef<Res>,
) -> Result<fhir::VariantDef, ErrorGuaranteed> {
    let mut binders = Binders::new();
    binders.gather_params_variant(tcx, sess, map, variant)?;
    let mut cx = DesugarCtxt::new(tcx, sess, map, binders);

    let fields = variant
        .fields
        .iter()
        .map(|ty| cx.desugar_ty(None, ty))
        .try_collect_exhaust()?;

    let ret = cx.desugar_variant_ret(&variant.ret)?;

    Ok(fhir::VariantDef { params: cx.binders.pop_layer().into_params(), fields, ret })
}

pub fn desugar_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    fn_sig: &surface::FnSig<Res>,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    let mut binders = Binders::new();

    // # Desugar inputs
    binders.gather_input_params_fn_sig(tcx, sess, map, fn_sig)?;
    let mut cx = DesugarCtxt::new(tcx, sess, map, binders);

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

    // # Desugar output
    cx.binders.push_layer();
    cx.binders
        .gather_output_params_fn_sig(tcx, sess, map, fn_sig)?;
    let ret = match &fn_sig.returns {
        Some(returns) => cx.desugar_ty(None, returns),
        None => Ok(fhir::Ty::Tuple(vec![])),
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
        params: cx.binders.pop_layer().into_params(),
        ret: ret?,
        ensures: ensures?,
    };

    Ok(fhir::FnSig {
        params: cx.binders.pop_layer().into_params(),
        requires: cx.requires,
        args,
        output,
    })
}

pub struct DesugarCtxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    map: &'a fhir::Map,
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
    /// The boolean indicates whether the binder was declared _implicitly_ with the `@` syntax and
    /// it is used to determine the inference mode for abstract refinements.
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
    _tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    map: &'a fhir::Map,
    binders: &'a Binders,
}

enum BtyOrTy {
    Bty(fhir::BaseTy),
    Ty(fhir::Ty),
}

enum FuncRes<'a> {
    Param(fhir::Name, &'a fhir::Sort),
    Uif(&'a fhir::UifDef),
}

impl<'a, 'tcx> DesugarCtxt<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
        map: &'a fhir::Map,
        binders: Binders,
    ) -> DesugarCtxt<'a, 'tcx> {
        DesugarCtxt { tcx, sess, binders, requires: vec![], map }
    }

    fn as_expr_ctxt(&self) -> ExprCtxt<'_, 'tcx> {
        ExprCtxt::new(self.tcx, self.sess, self.map, &self.binders)
    }

    fn desugar_fun_arg(&mut self, arg: &surface::Arg<Res>) -> Result<fhir::Ty, ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                let ty = match self.desugar_path(path)? {
                    BtyOrTy::Bty(bty) => {
                        let idx = self.desugar_bind(*bind)?;
                        fhir::Ty::Indexed(bty, idx)
                    }
                    BtyOrTy::Ty(ty) => ty,
                };
                Ok(fhir::Ty::Constr(self.as_expr_ctxt().desugar_expr(pred)?, Box::new(ty)))
            }
            surface::Arg::StrgRef(loc, ty) => {
                let loc = self.as_expr_ctxt().desugar_loc(*loc)?;
                let ty = self.desugar_ty(None, ty)?;
                self.requires.push(fhir::Constraint::Type(loc, ty));
                Ok(fhir::Ty::Ptr(loc))
            }
            surface::Arg::Ty(bind, ty) => self.desugar_ty(*bind, ty),
            surface::Arg::Alias(..) => panic!("Unexpected-Alias in desugar!"),
        }
    }

    fn desugar_ty(
        &mut self,
        bind: Option<surface::Ident>,
        ty: &surface::Ty<Res>,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        match &ty.kind {
            surface::TyKind::Base(bty) => self.desugar_bty_bind(bind, bty),
            surface::TyKind::Indexed { bty, indices } => {
                match self.desugar_bty(bty)? {
                    BtyOrTy::Bty(bty) => {
                        let idx = self.desugar_indices(&bty, indices)?;
                        Ok(fhir::Ty::Indexed(bty, idx))
                    }
                    BtyOrTy::Ty(_) => {
                        Err(self.sess.emit_err(errors::ParamCountMismatch::new(
                            indices.span,
                            0,
                            indices.indices.len(),
                        )))
                    }
                }
            }
            surface::TyKind::Exists { bind: ident, bty, pred } => {
                match self.desugar_bty(bty)? {
                    BtyOrTy::Bty(bty) => {
                        if let Some(bind) = bind {
                            let binder = self.binders[bind].clone();
                            let pred = self.binders.with_binder(*ident, binder, |binders| {
                                ExprCtxt::new(self.tcx, self.sess, self.map, binders)
                                    .desugar_expr(pred)
                            })?;
                            let idxs = self.desugar_bind(bind)?;
                            Ok(fhir::Ty::Constr(pred, Box::new(fhir::Ty::Indexed(bty, idxs))))
                        } else {
                            let name = self.binders.fresh();
                            let binder = Binder::Refined(name, bty.sort(), false);
                            let pred = self.binders.with_binder(*ident, binder, |binders| {
                                ExprCtxt::new(self.tcx, self.sess, self.map, binders)
                                    .desugar_expr(pred)
                            })?;
                            let bind = fhir::Ident::new(name, *ident);
                            Ok(fhir::Ty::Exists(bty, bind, pred))
                        }
                    }
                    BtyOrTy::Ty(_) => {
                        Err(self
                            .sess
                            .emit_err(errors::ParamCountMismatch::new(ident.span, 0, 1)))
                    }
                }
            }
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.as_expr_ctxt().desugar_expr(pred)?;
                let ty = self.desugar_ty(None, ty)?;
                Ok(fhir::Ty::Constr(pred, Box::new(ty)))
            }
            surface::TyKind::Ref(rk, ty) => {
                Ok(fhir::Ty::Ref(desugar_ref_kind(*rk), Box::new(self.desugar_ty(None, ty)?)))
            }
            surface::TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.desugar_ty(None, ty))
                    .try_collect_exhaust()?;
                Ok(fhir::Ty::Tuple(tys))
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.desugar_ty(None, ty)?;
                Ok(fhir::Ty::Array(Box::new(ty), fhir::ArrayLen { val: len.val }))
            }
        }
    }

    fn desugar_indices(
        &mut self,
        bty: &fhir::BaseTy,
        idxs: &surface::Indices,
    ) -> Result<fhir::Index, ErrorGuaranteed> {
        let kind = if let fhir::BaseTy::Adt(def_id, _) = bty && idxs.indices.len() != 1 {
            let args = idxs
                .indices
                .iter()
                .map(|idx| self.desugar_refine_arg(idx))
                .try_collect_exhaust()?;
            fhir::IndexKind::Aggregate(*def_id, args)
        } else {
            let arg = idxs.indices.first().unwrap();
            fhir::IndexKind::Single(self.desugar_refine_arg(arg)?)
        };
        Ok(fhir::Index { kind, span: idxs.span })
    }

    fn desugar_bind(&self, bind: surface::Ident) -> Result<fhir::Index, ErrorGuaranteed> {
        let kind = fhir::IndexKind::Single(self.bind_into_arg(bind)?);
        Ok(fhir::Index { kind, span: bind.span })
    }

    fn bind_into_arg(&self, ident: surface::Ident) -> Result<fhir::RefineArg, ErrorGuaranteed> {
        match self.binders.get(ident) {
            Some(Binder::Refined(name, ..)) => {
                let kind = fhir::ExprKind::Var(fhir::Ident::new(*name, ident));
                let expr = fhir::Expr { kind, span: ident.span };
                Ok(fhir::RefineArg::Expr { expr, is_binder: true })
            }
            Some(Binder::Unrefined) => todo!(),
            None => Err(self.sess.emit_err(errors::UnresolvedVar::new(ident))),
        }
    }

    fn desugar_refine_arg(
        &mut self,
        arg: &surface::RefineArg,
    ) -> Result<fhir::RefineArg, ErrorGuaranteed> {
        match arg {
            surface::RefineArg::Bind(ident, ..) => self.bind_into_arg(*ident),
            surface::RefineArg::Expr(expr) => {
                Ok(fhir::RefineArg::Expr {
                    expr: self.as_expr_ctxt().desugar_expr(expr)?,
                    is_binder: false,
                })
            }
            surface::RefineArg::Abs(params, body, span) => {
                let (body, names) = self.binders.with_abs_params(params, |binders| {
                    let cx = ExprCtxt::new(self.tcx, self.sess, self.map, binders);
                    cx.desugar_expr(body)
                })?;
                Ok(fhir::RefineArg::Abs(names, body, *span))
            }
        }
    }

    fn desugar_path(&mut self, path: &surface::Path<Res>) -> Result<BtyOrTy, ErrorGuaranteed> {
        let bty = match &path.res {
            Res::Bool => BtyOrTy::Bty(fhir::BaseTy::Bool),
            Res::Int(int_ty) => BtyOrTy::Bty(fhir::BaseTy::Int(*int_ty)),
            Res::Uint(uint_ty) => BtyOrTy::Bty(fhir::BaseTy::Uint(*uint_ty)),
            Res::Adt(def_id) => {
                let substs = path
                    .args
                    .iter()
                    .map(|ty| self.desugar_ty(None, ty))
                    .try_collect_exhaust()?;
                BtyOrTy::Bty(fhir::BaseTy::Adt(*def_id, substs))
            }
            Res::Float(float_ty) => BtyOrTy::Ty(fhir::Ty::Float(*float_ty)),
            Res::Param(param_ty) => BtyOrTy::Ty(fhir::Ty::Param(*param_ty)),
            Res::Str => BtyOrTy::Ty(fhir::Ty::Str),
            Res::Char => BtyOrTy::Ty(fhir::Ty::Char),
        };
        Ok(bty)
    }

    fn desugar_bty(&mut self, bty: &surface::BaseTy<Res>) -> Result<BtyOrTy, ErrorGuaranteed> {
        let bty = match bty {
            surface::BaseTy::Path(path) => self.desugar_path(path)?,

            surface::BaseTy::Slice(ty) => {
                let bty = fhir::BaseTy::Slice(Box::new(self.desugar_ty(None, ty)?));
                BtyOrTy::Bty(bty)
            }
        };
        Ok(bty)
    }

    fn desugar_bty_bind(
        &mut self,
        bind: Option<surface::Ident>,
        bty: &surface::BaseTy<Res>,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        match self.desugar_bty(bty)? {
            BtyOrTy::Bty(bty) => {
                if let Some(bind) = bind {
                    let idx = self.desugar_bind(bind)?;
                    Ok(fhir::Ty::Indexed(bty, idx))
                } else {
                    Ok(fhir::Ty::BaseTy(bty))
                }
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
}

impl<'a, 'tcx> ExprCtxt<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
        map: &'a fhir::Map,
        binders: &'a Binders,
    ) -> Self {
        Self { _tcx: tcx, sess, map, binders }
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
                        .sess
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
                    let def_ident = self.binders.def_ident(func).unwrap();
                    return Err(self
                        .sess
                        .emit_err(errors::InvalidUnrefinedParam::new(def_ident, func)));
                }
            }
        }
        if let Some(uif) = self.map.uif(func.name) {
            return Ok(FuncRes::Uif(uif));
        }
        Err(self.sess.emit_err(errors::UnresolvedVar::new(func)))
    }

    fn desugar_lit(&self, span: Span, lit: surface::Lit) -> Result<fhir::Lit, ErrorGuaranteed> {
        match lit.kind {
            surface::LitKind::Integer => {
                let Ok(n) = lit.symbol.as_str().parse::<i128>() else {
                    return Err(self.sess.emit_err(errors::IntTooLarge { span }));
                };
                let suffix = lit.suffix.unwrap_or(SORTS.int);
                if suffix == SORTS.int {
                    Ok(fhir::Lit::Int(n))
                } else if suffix == SORTS.real {
                    Ok(fhir::Lit::Real(n))
                } else {
                    Err(self
                        .sess
                        .emit_err(errors::InvalidNumericSuffix::new(span, suffix)))
                }
            }
            surface::LitKind::Bool => Ok(fhir::Lit::Bool(lit.symbol == kw::True)),
            _ => Err(self.sess.emit_err(errors::UnexpectedLiteral { span })),
        }
    }

    fn desugar_var(&self, ident: surface::Ident) -> Result<fhir::Expr, ErrorGuaranteed> {
        let kind = match (self.binders.get(ident), self.map.const_by_name(ident.name)) {
            (Some(Binder::Refined(name, ..)), _) => {
                fhir::ExprKind::Var(fhir::Ident::new(*name, ident))
            }
            (Some(Binder::Unrefined), _) => {
                let def_ident = self.binders.def_ident(ident).unwrap();
                return Err(self
                    .sess
                    .emit_err(errors::InvalidUnrefinedParam::new(def_ident, ident)));
            }
            (None, Some(const_info)) => fhir::ExprKind::Const(const_info.def_id, ident.span),
            (None, None) => return Err(self.sess.emit_err(errors::UnresolvedVar::new(ident))),
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
            None => Err(self.sess.emit_err(errors::UnresolvedVar::new(loc))),
        }
    }
}

fn desugar_ref_kind(rk: surface::RefKind) -> fhir::RefKind {
    match rk {
        surface::RefKind::Mut => fhir::RefKind::Mut,
        surface::RefKind::Shr => fhir::RefKind::Shr,
    }
}

fn resolve_sort(
    sess: &FluxSession,
    map: &fhir::Map,
    sort: &surface::Sort,
) -> Result<fhir::Sort, ErrorGuaranteed> {
    match sort {
        surface::Sort::Base(sort) => resolve_base_sort(sess, map, *sort),
        surface::Sort::Func { inputs, output } => {
            Ok(resolve_func_sort(sess, map, inputs, output)?.into())
        }
        surface::Sort::Infer => todo!(),
    }
}

fn resolve_func_sort(
    sess: &FluxSession,
    map: &fhir::Map,
    inputs: &[surface::Ident],
    output: &surface::Ident,
) -> Result<fhir::FuncSort, ErrorGuaranteed> {
    let mut inputs_and_output: Vec<fhir::Sort> = inputs
        .iter()
        .map(|sort| resolve_base_sort(sess, map, *sort))
        .try_collect_exhaust()?;
    inputs_and_output.push(resolve_base_sort(sess, map, *output)?);
    Ok(fhir::FuncSort { inputs_and_output: List::from_vec(inputs_and_output) })
}

fn resolve_base_sort(
    sess: &FluxSession,
    map: &fhir::Map,
    sort: surface::Ident,
) -> Result<fhir::Sort, ErrorGuaranteed> {
    if sort.name == SORTS.int {
        Ok(fhir::Sort::Int)
    } else if sort.name == sym::bool {
        Ok(fhir::Sort::Bool)
    } else if sort.name == SORTS.real {
        Ok(fhir::Sort::Real)
    } else if map.sort_decl(sort.name).is_some() {
        Ok(fhir::Sort::User(sort.name))
    } else {
        Err(sess.emit_err(errors::UnresolvedSort::new(sort)))
    }
}

impl Binders {
    fn new() -> Binders {
        Binders { name_gen: IndexGen::new(), layers: vec![Layer::default()] }
    }

    fn from_params<'a>(
        sess: &FluxSession,
        map: &fhir::Map,
        params: impl IntoIterator<Item = &'a surface::RefineParam>,
    ) -> Result<Self, ErrorGuaranteed> {
        let mut binders = Self::new();
        for param in params {
            binders.insert_binder(
                sess,
                param.name,
                Binder::Refined(binders.fresh(), resolve_sort(sess, map, &param.sort)?, false),
            )?;
        }
        Ok(binders)
    }

    fn fresh(&self) -> fhir::Name {
        self.name_gen.fresh()
    }

    fn def_ident(&self, ident: impl Borrow<surface::Ident>) -> Option<surface::Ident> {
        self.iter_layers(|layer| Some(*layer.get_key_value(ident.borrow())?.0))
    }

    fn get(&self, ident: impl Borrow<surface::Ident>) -> Option<&Binder> {
        self.iter_layers(|layer| layer.get(ident.borrow()))
    }

    fn with_binder<R>(
        &mut self,
        ident: surface::Ident,
        binder: Binder,
        f: impl FnOnce(&mut Self) -> Result<R, ErrorGuaranteed>,
    ) -> Result<R, ErrorGuaranteed> {
        self.with_binders([(ident, binder)], f)
    }

    fn with_abs_params<R>(
        &mut self,
        params: &[surface::Ident],
        f: impl FnOnce(&mut Self) -> Result<R, ErrorGuaranteed>,
    ) -> Result<(R, Vec<fhir::Name>), ErrorGuaranteed> {
        let names = params.iter().map(|_| self.fresh()).collect_vec();
        let binders = iter::zip(&names, params)
            .map(|(name, param)| (*param, Binder::Refined(*name, fhir::Sort::Infer, false)))
            .collect_vec();
        let r = self.with_binders(binders, f)?;
        Ok((r, names))
    }

    fn with_binders<R>(
        &mut self,
        binders: impl IntoIterator<Item = (surface::Ident, Binder)>,
        f: impl FnOnce(&mut Self) -> Result<R, ErrorGuaranteed>,
    ) -> Result<R, ErrorGuaranteed> {
        self.push_layer();
        for (ident, binder) in binders {
            self.top_layer().insert(ident, binder);
        }
        let r = f(self)?;
        self.pop_layer();
        Ok(r)
    }

    fn insert_binder(
        &mut self,
        sess: &FluxSession,
        ident: surface::Ident,
        binder: Binder,
    ) -> Result<(), ErrorGuaranteed> {
        match self.top_layer().entry(ident) {
            IndexEntry::Occupied(entry) => {
                Err(sess.emit_err(errors::DuplicateParam::new(*entry.key(), ident)))
            }
            IndexEntry::Vacant(entry) => {
                entry.insert(binder);
                Ok(())
            }
        }
    }

    fn gather_params_variant(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        variant: &surface::VariantDef<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        for ty in &variant.fields {
            self.gather_params_ty(tcx, sess, map, None, ty, TypePos::Input)?;
        }
        // Traverse return type to find illegal binders.
        self.gather_params_path(tcx, sess, map, &variant.ret.path, TypePos::Other)?;
        // Check binders in `VariantRet`
        variant
            .ret
            .indices
            .indices
            .iter()
            .try_for_each_exhaust(|idx| {
                if let surface::RefineArg::Bind(_, kind, span) = idx {
                    Err(sess.emit_err(errors::IllegalBinder::new(*span, *kind)))
                } else {
                    Ok(())
                }
            })
    }

    fn gather_input_params_fn_sig(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        fn_sig: &surface::FnSig<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        for param in &fn_sig.params {
            self.insert_binder(
                sess,
                param.name,
                Binder::Refined(self.fresh(), resolve_sort(sess, map, &param.sort)?, false),
            )?;
        }
        for arg in &fn_sig.args {
            self.gather_params_fun_arg(tcx, sess, map, arg)?;
        }

        Ok(())
    }

    fn gather_output_params_fn_sig(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        fn_sig: &surface::FnSig<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        if let Some(ret_ty) = &fn_sig.returns {
            self.gather_params_ty(tcx, sess, map, None, ret_ty, TypePos::Output)?;
        }
        for (_, ty) in &fn_sig.ensures {
            self.gather_params_ty(tcx, sess, map, None, ty, TypePos::Output)?;
        }
        Ok(())
    }

    fn gather_params_fun_arg(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        arg: &surface::Arg<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, _) => {
                self.insert_binder(sess, *bind, Binder::from_res(&self.name_gen, path.res))?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.insert_binder(
                    sess,
                    *loc,
                    Binder::Refined(self.fresh(), fhir::Sort::Loc, false),
                )?;
                self.gather_params_ty(tcx, sess, map, None, ty, TypePos::Input)?;
            }
            surface::Arg::Ty(bind, ty) => {
                self.gather_params_ty(tcx, sess, map, *bind, ty, TypePos::Input)?;
            }
            surface::Arg::Alias(..) => panic!("alias are not allowed after expansion"),
        }
        Ok(())
    }

    fn gather_params_ty(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        bind: Option<surface::Ident>,
        ty: &surface::Ty<Res>,
        pos: TypePos,
    ) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            surface::TyKind::Indexed { bty, indices } => {
                if bind.is_some() {
                    // This code is currently not reachable because the parser won't allow it as it conflicts with alias
                    // applications. If we ever allow this we should think about the meaning of the syntax `x: T[@n]` and
                    // `x: T[n]`. The second syntax should behave appropriately even when `n` is bound explicitly in the
                    // list of refinement parameters, i.e., what's the meaning of `fn<n: int>(x: i32[n])` or the meaning
                    // of `fn<n: int>(x: RMat[n, n])`
                    unreachable!("[sanity check] this code is unreachable but we are leaving a not in case it is not anymore");
                }
                if let [surface::RefineArg::Bind(ident, kind, span)] = indices.indices[..] {
                    let binder = Binder::from_bty(&self.name_gen, bty);
                    if !pos.is_binder_allowed(kind) {
                        return Err(sess.emit_err(errors::IllegalBinder::new(span, kind)));
                    }
                    self.insert_binder(sess, ident, binder)?;
                } else {
                    let refined_by = sorts(map, bty).unwrap();
                    let exp = refined_by.len();
                    let got = indices.indices.len();
                    if exp != got {
                        return Err(
                            sess.emit_err(errors::ParamCountMismatch::new(ty.span, exp, got))
                        );
                    }

                    for (idx, sort) in iter::zip(&indices.indices, refined_by) {
                        if let surface::RefineArg::Bind(ident, kind, span) = idx {
                            if !pos.is_binder_allowed(*kind) {
                                return Err(sess.emit_err(errors::IllegalBinder::new(*span, *kind)));
                            }
                            let name = self.name_gen.fresh();
                            self.insert_binder(
                                sess,
                                *ident,
                                Binder::Refined(name, sort.clone(), true),
                            )?;
                        }
                    }
                }
                self.gather_params_bty(tcx, sess, map, bty, pos)
            }
            surface::TyKind::Base(bty) => {
                if let Some(bind) = bind {
                    self.insert_binder(sess, bind, Binder::from_bty(&self.name_gen, bty))?;
                }
                self.gather_params_bty(tcx, sess, map, bty, pos)
            }

            surface::TyKind::Ref(_, ty) | surface::TyKind::Constr(_, ty) => {
                if let Some(bind) = bind {
                    self.insert_binder(sess, bind, Binder::Unrefined)?;
                }
                self.gather_params_ty(tcx, sess, map, None, ty, pos)
            }
            surface::TyKind::Tuple(tys) => {
                if let Some(bind) = bind {
                    self.insert_binder(sess, bind, Binder::Unrefined)?;
                }
                for ty in tys {
                    self.gather_params_ty(tcx, sess, map, None, ty, pos)?;
                }
                Ok(())
            }
            surface::TyKind::Array(ty, _) => {
                self.gather_params_ty(tcx, sess, map, None, ty, TypePos::Other)
            }
            surface::TyKind::Exists { bty, .. } => {
                if let Some(bind) = bind {
                    self.insert_binder(sess, bind, Binder::from_bty(&self.name_gen, bty))?;
                }
                self.gather_params_bty(tcx, sess, map, bty, pos)
            }
        }
    }

    fn gather_params_path(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        path: &surface::Path<Res>,
        pos: TypePos,
    ) -> Result<(), ErrorGuaranteed> {
        let pos = if is_box(tcx, path.res) { pos } else { TypePos::Other };
        path.args
            .iter()
            .try_for_each_exhaust(|ty| self.gather_params_ty(tcx, sess, map, None, ty, pos))
    }

    fn gather_params_bty(
        &mut self,
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        bty: &surface::BaseTy<Res>,
        pos: TypePos,
    ) -> Result<(), ErrorGuaranteed> {
        match bty {
            surface::BaseTy::Path(path) => self.gather_params_path(tcx, sess, map, path, pos),
            surface::BaseTy::Slice(ty) => {
                self.gather_params_ty(tcx, sess, map, None, ty, TypePos::Other)
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

fn is_box(tcx: TyCtxt, res: surface::Res) -> bool {
    if let Res::Adt(def_id) = res {
        tcx.adt_def(def_id).is_box()
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
) -> fhir::RefineParam {
    let name = fhir::Ident::new(name, ident);
    fhir::RefineParam { name, sort, mode }
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
    fn get_key_value(
        &self,
        key: impl Borrow<surface::Ident>,
    ) -> Option<(&surface::Ident, &Binder)> {
        self.map.get_key_value(key.borrow())
    }

    fn get(&self, key: impl Borrow<surface::Ident>) -> Option<&Binder> {
        self.map.get(key.borrow())
    }

    fn insert(&mut self, ident: surface::Ident, binder: Binder) {
        self.map.insert(ident, binder);
    }

    fn entry(&mut self, ident: surface::Ident) -> IndexEntry<surface::Ident, Binder> {
        self.map.entry(ident)
    }

    fn into_args(self) -> Vec<(fhir::Ident, fhir::Sort)> {
        let mut args = vec![];
        for (ident, binder) in self.map {
            if let Binder::Refined(name, sort, _) = binder {
                let name = fhir::Ident::new(name, ident);
                args.push((name, sort));
            } else {
                bug!();
            }
        }
        args
    }

    fn into_params(self) -> Vec<fhir::RefineParam> {
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
        match res {
            Res::Bool => Binder::Refined(name_gen.fresh(), fhir::Sort::Bool, true),
            Res::Int(_) | Res::Uint(_) => Binder::Refined(name_gen.fresh(), fhir::Sort::Int, false),
            Res::Adt(def_id) => Binder::Refined(name_gen.fresh(), fhir::Sort::Adt(def_id), true),
            Res::Float(_) | Res::Param(_) | Res::Str | Res::Char => Binder::Unrefined,
        }
    }

    fn from_bty(name_gen: &IndexGen<fhir::Name>, bty: &surface::BaseTy<Res>) -> Binder {
        match bty {
            surface::BaseTy::Path(path) => Binder::from_res(name_gen, path.res),
            surface::BaseTy::Slice(_) => Binder::Refined(name_gen.fresh(), fhir::Sort::Int, true),
        }
    }
}

fn sorts<'a>(map: &'a fhir::Map, bty: &surface::BaseTy<Res>) -> Option<&'a [fhir::Sort]> {
    let sorts = match bty {
        surface::BaseTy::Path(path) => {
            match path.res {
                Res::Bool => &[fhir::Sort::Bool],
                Res::Int(_) | Res::Uint(_) => &[fhir::Sort::Int],
                Res::Adt(def_id) => map.sorts_of(def_id).unwrap_or(&[]),
                Res::Float(_) | Res::Param(_) | Res::Str | Res::Char => return None,
            }
        }
        surface::BaseTy::Slice(_) => &[fhir::Sort::Bool],
    };
    Some(sorts)
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
        #[label(desugar::defined_here)]
        def_span: Span,
    }

    impl InvalidUnrefinedParam {
        pub(super) fn new(def: Ident, var: Ident) -> Self {
            Self { def_span: def.span, var, span: var.span }
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
