//! Desugaring from types in [`flux_syntax::surface`] to types in [`flux_middle::fhir`]
use std::{borrow::Borrow, iter};

use flux_common::{index::IndexGen, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::{fhir, intern::List};
use flux_syntax::surface::{self, Res, TyCtxt};
use rustc_data_structures::fx::{FxIndexMap, IndexEntry};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def_id::DefId;
use rustc_span::{sym, symbol::kw, Symbol};

pub fn desugar_qualifier(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    qualifier: surface::Qualifier,
) -> Result<fhir::Qualifier, ErrorGuaranteed> {
    let mut binders = Binders::new();
    binders.insert_params(sess, qualifier.args)?;
    let name = qualifier.name.name.to_ident_string();
    let expr = ExprCtxt::new(tcx, sess, map, &binders).desugar_expr(qualifier.expr);

    Ok(fhir::Qualifier { name, args: binders.into_params(), expr: expr? })
}

pub fn resolve_uif_def(
    sess: &FluxSession,
    uif_def: surface::UifDef,
) -> Result<fhir::UifDef, ErrorGuaranteed> {
    let inputs = uif_def
        .inputs
        .into_iter()
        .map(|ident| resolve_sort(sess, ident))
        .try_collect_exhaust()?;
    let output = resolve_sort(sess, uif_def.output)?;
    Ok(fhir::UifDef { name: uif_def.name.name, sort: fhir::FuncSort::new(inputs, output) })
}

pub fn desugar_adt_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    def_id: DefId,
    refined_by: &surface::RefinedBy,
    invariants: Vec<surface::Expr>,
    opaque: bool,
) -> Result<fhir::AdtDef, ErrorGuaranteed> {
    let mut binders = Binders::new();
    binders.insert_params(sess, refined_by)?;

    let invariants = invariants
        .into_iter()
        .map(|invariant| ExprCtxt::new(tcx, sess, map, &binders).desugar_expr(invariant))
        .try_collect_exhaust()?;

    let refined_by = fhir::RefinedBy { params: binders.into_params(), span: refined_by.span };
    Ok(fhir::AdtDef::new(def_id, refined_by, invariants, opaque))
}

pub fn desugar_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    adt_def: surface::StructDef<Res>,
) -> Result<fhir::StructDef, ErrorGuaranteed> {
    let def_id = adt_def.def_id.to_def_id();
    let mut binders = Binders::new();
    binders.insert_params(sess, adt_def.refined_by.into_iter().flatten())?;

    let mut cx = DesugarCtxt::new(tcx, sess, map, binders);

    let kind = if adt_def.opaque {
        fhir::StructKind::Opaque
    } else {
        let fields = adt_def
            .fields
            .into_iter()
            .map(|ty| ty.map(|ty| cx.desugar_ty(None, ty)).transpose())
            .try_collect_exhaust()?;
        fhir::StructKind::Transparent { fields }
    };
    Ok(fhir::StructDef { def_id, kind })
}

pub fn desugar_enum_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    enum_def: surface::EnumDef<Res>,
) -> Result<fhir::EnumDef, ErrorGuaranteed> {
    let mut binders = Binders::new();
    binders.insert_params(sess, enum_def.refined_by.into_iter().flatten())?;
    let def_id = enum_def.def_id.to_def_id();
    let variants = enum_def
        .variants
        .into_iter()
        .map(|variant| desugar_variant(tcx, sess, map, variant))
        .try_collect_exhaust()?;

    Ok(fhir::EnumDef { def_id, variants })
}

fn desugar_variant(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    variant: surface::VariantDef<Res>,
) -> Result<fhir::VariantDef, ErrorGuaranteed> {
    let mut binders = Binders::new();
    for ty in &variant.fields {
        binders.ty_gather_params(sess, map, None, ty)?;
    }
    let mut cx = DesugarCtxt::new(tcx, sess, map, binders);

    let fields = variant
        .fields
        .into_iter()
        .map(|ty| cx.desugar_ty(None, ty))
        .try_collect_exhaust()?;

    let ret = cx.desugar_variant_ret(variant.ret)?;

    Ok(fhir::VariantDef { params: cx.binders.into_params(), fields, ret })
}

pub fn desugar_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    map: &fhir::Map,
    fn_sig: surface::FnSig<Res>,
) -> Result<fhir::FnSig, ErrorGuaranteed> {
    let mut binders = Binders::new();
    binders.gather_fn_sig_params(sess, map, &fn_sig)?;
    let mut cx = DesugarCtxt::new(tcx, sess, map, binders);

    if let Some(e) = fn_sig.requires {
        let pred = cx.as_expr_ctxt().desugar_expr(e)?;
        cx.requires.push(fhir::Constraint::Pred(pred));
    }

    // We bail out if there's an error in the arguments to avoid confusing error messages
    let args = fn_sig
        .args
        .into_iter()
        .map(|arg| cx.desugar_arg(arg))
        .try_collect_exhaust()?;

    let ret = match fn_sig.returns {
        Some(returns) => cx.desugar_ty(None, returns),
        None => Ok(fhir::Ty::Tuple(vec![])),
    };

    let ensures = fn_sig
        .ensures
        .into_iter()
        .map(|(bind, ty)| {
            let loc = cx.as_expr_ctxt().desugar_loc(bind);
            let ty = cx.desugar_ty(None, ty);
            Ok(fhir::Constraint::Type(loc?, ty?))
        })
        .try_collect_exhaust();

    Ok(fhir::FnSig {
        params: cx.binders.into_params(),
        requires: cx.requires,
        args,
        ret: ret?,
        ensures: ensures?,
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
    map: FxIndexMap<surface::Ident, Binder>,
}

/// The different kind of binders that can appear in the surface syntax
#[derive(Debug, Clone)]
enum Binder {
    /// A binder that needs to be desugared to a single index. They come from bindings
    /// to a native type indexed by a single value, e.g., `x: i32` or `bool[@b]`, or
    /// by explicitly listing the indices for a type with multiple indices, e.g,
    /// `RMat[@row, @cols]`.
    Single(fhir::Name, fhir::Sort),
    /// A binder that will desugar into multiple indices and _must_ be projected using
    /// dot syntax. They come from binders to user defined types with a `#[refined_by]`
    /// annotation, e.g., `mat: RMat` or `RMat[@mat]`. User defined types with a single
    /// index are treated specially as they can be used either with a projection or the
    /// binder directly.
    Aggregate(DefId, FxIndexMap<Symbol, (fhir::Name, fhir::Sort)>),
    /// A binder to an unrefined type (a type that cannot be refined). We try to catch this
    /// situation "eagerly" as it will often result in better error messages, e.g., we will
    /// fail if a type parameter `T` (which cannot be refined) is used as an indexed type
    /// `T[@a]` or as an existential `T{v : v > 0}`, but unrefined binders can appear when
    /// using argument syntax (`x: T`), thus we track them and report appropriate errors if
    /// they are used in any way.
    Unrefined,
}

struct ExprCtxt<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
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

    fn desugar_arg(&mut self, arg: surface::Arg<Res>) -> Result<fhir::Ty, ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, pred) => {
                let ty = match self.desugar_path(path)? {
                    BtyOrTy::Bty(bty) => fhir::Ty::Indexed(bty, self.desugar_bind(bind)?),
                    BtyOrTy::Ty(ty) => ty,
                };
                Ok(fhir::Ty::Constr(self.as_expr_ctxt().desugar_expr(pred)?, Box::new(ty)))
            }
            surface::Arg::StrgRef(loc, ty) => {
                let loc = self.as_expr_ctxt().desugar_loc(loc)?;
                let ty = self.desugar_ty(None, ty)?;
                self.requires.push(fhir::Constraint::Type(loc, ty));
                Ok(fhir::Ty::Ptr(loc))
            }
            surface::Arg::Ty(bind, ty) => self.desugar_ty(bind, ty),
            surface::Arg::Alias(..) => panic!("Unexpected-Alias in desugar!"),
        }
    }

    fn desugar_ty(
        &mut self,
        bind: Option<surface::Ident>,
        ty: surface::Ty<Res>,
    ) -> Result<fhir::Ty, ErrorGuaranteed> {
        let ty = match ty.kind {
            surface::TyKind::Path(surface::Path { ident: Res::Float(float_ty), .. }) => {
                fhir::Ty::Float(float_ty)
            }
            surface::TyKind::Path(surface::Path { ident: Res::Param(param_ty), .. }) => {
                fhir::Ty::Param(param_ty)
            }
            surface::TyKind::Path(path) => {
                match self.desugar_path(path)? {
                    BtyOrTy::Bty(bty) => {
                        if let Some(bind) = bind {
                            fhir::Ty::Indexed(bty, self.desugar_bind(bind)?)
                        } else {
                            fhir::Ty::BaseTy(bty)
                        }
                    }
                    BtyOrTy::Ty(ty) => ty,
                }
            }
            surface::TyKind::Indexed { path, indices } => {
                match self.desugar_path(path)? {
                    BtyOrTy::Bty(bty) => fhir::Ty::Indexed(bty, self.desugar_indices(indices)?),
                    BtyOrTy::Ty(_) => {
                        return Err(self.sess.emit_err(errors::ParamCountMismatch::new(
                            indices.span,
                            0,
                            indices.indices.len(),
                        )))
                    }
                }
            }
            surface::TyKind::Exists { bind: ident, path, pred } => {
                let res = path.ident;
                match self.desugar_path(path)? {
                    BtyOrTy::Bty(bty) => {
                        if let Some(bind) = bind {
                            let binder = self.binders[bind].clone();
                            let (pred, _) = self.binders.with_bind(ident, binder, |binders| {
                                ExprCtxt::new(self.tcx, self.sess, self.map, binders)
                                    .desugar_expr(pred)
                            })?;
                            let idxs = self.desugar_bind(bind)?;
                            fhir::Ty::Constr(pred, Box::new(fhir::Ty::Indexed(bty, idxs)))
                        } else {
                            let binder = Binder::from_res(&self.binders.name_gen, self.map, res);
                            let (pred, binder) =
                                self.binders.with_bind(ident, binder, |binders| {
                                    ExprCtxt::new(self.tcx, self.sess, self.map, binders)
                                        .desugar_expr(pred)
                                })?;
                            fhir::Ty::Exists(bty, binder.names(), pred)
                        }
                    }
                    BtyOrTy::Ty(_) => {
                        return Err(self
                            .sess
                            .emit_err(errors::ParamCountMismatch::new(ident.span, 0, 1)))
                    }
                }
            }
            surface::TyKind::Ref(rk, ty) => {
                fhir::Ty::Ref(desugar_ref_kind(rk), Box::new(self.desugar_ty(None, *ty)?))
            }
            surface::TyKind::Unit => fhir::Ty::Tuple(vec![]),
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.as_expr_ctxt().desugar_expr(pred)?;
                let ty = self.desugar_ty(None, *ty)?;
                fhir::Ty::Constr(pred, Box::new(ty))
            }
            surface::TyKind::Array(ty, _) => {
                let ty = self.desugar_ty(None, *ty)?;
                fhir::Ty::Array(Box::new(ty), fhir::ArrayLen)
            }
            surface::TyKind::Slice(ty) => fhir::Ty::Slice(Box::new(self.desugar_ty(None, *ty)?)),
        };
        Ok(ty)
    }

    fn desugar_indices(&self, indices: surface::Indices) -> Result<fhir::Indices, ErrorGuaranteed> {
        let mut exprs = vec![];
        for idx in indices.indices {
            let idxs = self.desugar_index(idx)?;
            for e in idxs {
                exprs.push(e)
            }
        }
        Ok(fhir::Indices { indices: exprs, span: indices.span })
    }

    fn desugar_bind(&self, bind: surface::Ident) -> Result<fhir::Indices, ErrorGuaranteed> {
        Ok(fhir::Indices { indices: self.bind_into_indices(bind)?, span: bind.span })
    }

    fn bind_into_indices(
        &self,
        ident: surface::Ident,
    ) -> Result<Vec<fhir::Index>, ErrorGuaranteed> {
        match self.binders.get(ident) {
            Some(Binder::Single(name, _)) => {
                let kind = fhir::ExprKind::Var(*name, ident.name, ident.span);
                let expr = fhir::Expr { kind, span: ident.span };
                Ok(vec![fhir::Index { expr, is_binder: true }])
            }
            Some(Binder::Aggregate(_, fields)) => {
                let indices = fields
                    .values()
                    .map(|(name, _)| {
                        let kind = fhir::ExprKind::Var(*name, ident.name, ident.span);
                        fhir::Index { expr: fhir::Expr { kind, span: ident.span }, is_binder: true }
                    })
                    .collect();
                Ok(indices)
            }
            Some(Binder::Unrefined) => Ok(vec![]),
            None => Err(self.sess.emit_err(errors::UnresolvedVar::new(ident))),
        }
    }

    fn desugar_index(&self, idx: surface::Index) -> Result<Vec<fhir::Index>, ErrorGuaranteed> {
        match idx {
            surface::Index::Bind(ident) => self.bind_into_indices(ident),
            surface::Index::Expr(expr) => {
                Ok(vec![fhir::Index {
                    expr: self.as_expr_ctxt().desugar_expr(expr)?,
                    is_binder: false,
                }])
            }
        }
    }

    fn desugar_path(&mut self, path: surface::Path<Res>) -> Result<BtyOrTy, ErrorGuaranteed> {
        let bty = match path.ident {
            Res::Bool => BtyOrTy::Bty(fhir::BaseTy::Bool),
            Res::Int(int_ty) => BtyOrTy::Bty(fhir::BaseTy::Int(int_ty)),
            Res::Uint(uint_ty) => BtyOrTy::Bty(fhir::BaseTy::Uint(uint_ty)),
            Res::Adt(def_id) => {
                let substs = path
                    .args
                    .into_iter()
                    .map(|ty| self.desugar_ty(None, ty))
                    .try_collect_exhaust()?;
                BtyOrTy::Bty(fhir::BaseTy::Adt(def_id, substs))
            }
            Res::Float(float_ty) => BtyOrTy::Ty(fhir::Ty::Float(float_ty)),
            Res::Param(param_ty) => BtyOrTy::Ty(fhir::Ty::Param(param_ty)),
            Res::Str => BtyOrTy::Ty(fhir::Ty::Str),
            Res::Char => BtyOrTy::Ty(fhir::Ty::Char),
        };
        Ok(bty)
    }

    fn desugar_variant_ret(
        &mut self,
        ret: surface::VariantRet<Res>,
    ) -> Result<fhir::VariantRet, ErrorGuaranteed> {
        match self.desugar_path(ret.path)? {
            BtyOrTy::Bty(bty) => {
                let indices = self.desugar_indices(ret.indices)?;
                Ok(fhir::VariantRet { bty, indices })
            }
            BtyOrTy::Ty(_) => {
                // This shouldn't happen because during zip_resolve we are checking
                // the path resolves to the correct type.
                panic!("variant output desugared to a unrefined type")
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
        Self { tcx, sess, map, binders }
    }

    fn desugar_expr(&self, expr: surface::Expr) -> Result<fhir::Expr, ErrorGuaranteed> {
        let kind = match expr.kind {
            surface::ExprKind::Var(ident) => return self.desugar_var(ident),
            surface::ExprKind::Literal(lit) => fhir::ExprKind::Literal(self.desugar_lit(lit)?),
            surface::ExprKind::BinaryOp(op, box [e1, e2]) => {
                let e1 = self.desugar_expr(e1);
                let e2 = self.desugar_expr(e2);
                fhir::ExprKind::BinaryOp(desugar_bin_op(op), Box::new([e1?, e2?]))
            }
            surface::ExprKind::Dot(e, fld) => return self.desugar_dot(*e, fld),
            surface::ExprKind::App(func, args) => {
                let args = self.desugar_exprs(args)?;
                match self.resolve_func(func)? {
                    FuncRes::Uif(_) => {
                        fhir::ExprKind::App(fhir::Func::Uif(func.name, func.span), args)
                    }
                    FuncRes::Param(name, _) => {
                        let func =
                            fhir::Func::Var(fhir::Ident { name, source_info: to_src_info(func) });
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

    fn desugar_exprs(&self, exprs: Vec<surface::Expr>) -> Result<Vec<fhir::Expr>, ErrorGuaranteed> {
        exprs
            .into_iter()
            .map(|e| self.desugar_expr(e))
            .try_collect_exhaust()
    }

    fn resolve_func(&self, func: surface::Ident) -> Result<FuncRes, ErrorGuaranteed> {
        match (self.binders.get(func), self.map.uif(func.name)) {
            (Some(Binder::Single(name, sort)), _) => Ok(FuncRes::Param(*name, sort)),
            (Some(Binder::Aggregate(..)), _) => todo!(),
            (Some(Binder::Unrefined), _) => todo!(),
            (None, Some(uif)) => Ok(FuncRes::Uif(uif)),
            (None, None) => todo!(),
        }
    }

    fn desugar_lit(&self, lit: surface::Lit) -> Result<fhir::Lit, ErrorGuaranteed> {
        match lit.kind {
            surface::LitKind::Integer => {
                match lit.symbol.as_str().parse::<i128>() {
                    Ok(n) => Ok(fhir::Lit::Int(n)),
                    Err(_) => Err(self.sess.emit_err(errors::IntTooLarge { span: lit.span })),
                }
            }
            surface::LitKind::Bool => Ok(fhir::Lit::Bool(lit.symbol == kw::True)),
            _ => {
                Err(self
                    .sess
                    .emit_err(errors::UnexpectedLiteral { span: lit.span }))
            }
        }
    }

    fn desugar_var(&self, ident: surface::Ident) -> Result<fhir::Expr, ErrorGuaranteed> {
        let kind = match (self.binders.get(ident), self.map.const_by_name(ident.name)) {
            (Some(Binder::Single(name, _)), _) => {
                fhir::ExprKind::Var(*name, ident.name, ident.span)
            }
            (Some(Binder::Aggregate(_, fields)), _) => {
                if fields.len() == 1 {
                    let (name, _) = fields.values().next().unwrap();
                    fhir::ExprKind::Var(*name, ident.name, ident.span)
                } else {
                    return Err(self
                        .sess
                        .emit_err(errors::UnresolvedDotVar::new(ident, fields.keys())));
                }
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

    fn desugar_dot(
        &self,
        expr: surface::Expr,
        fld: surface::Ident,
    ) -> Result<fhir::Expr, ErrorGuaranteed> {
        // This error never occurs because the parser forces `expr` to be an ident, but we report an error just in case.
        let surface::ExprKind::Var(ident) = expr.kind else {
            return Err(self
                .sess
                .emit_err(errors::InvalidDotVar { span: expr.span }))
        };

        match self.binders.get(ident) {
            Some(Binder::Single(_, sort)) => {
                let def_ident = self.binders.def_ident(ident).unwrap();
                Err(self
                    .sess
                    .emit_err(errors::InvalidPrimitiveDotAccess::new(def_ident, sort, ident, fld)))
            }
            Some(Binder::Aggregate(def_id, fields)) => {
                let (name, _) = fields.get(&fld.name).ok_or_else(|| {
                    self.sess
                        .emit_err(errors::FieldNotFound::new(self.tcx, self.map, *def_id, fld))
                })?;
                let span = ident.span.to(fld.span);
                let kind = fhir::ExprKind::Var(*name, ident.name, span);
                Ok(fhir::Expr { kind, span })
            }
            Some(Binder::Unrefined) => {
                let def_ident = self.binders.def_ident(ident).unwrap();
                Err(self
                    .sess
                    .emit_err(errors::InvalidUnrefinedParam::new(def_ident, ident)))
            }
            None => Err(self.sess.emit_err(errors::UnresolvedVar::new(ident))),
        }
    }

    fn desugar_loc(&self, loc: surface::Ident) -> Result<fhir::Ident, ErrorGuaranteed> {
        match self.binders.get(loc) {
            Some(&Binder::Single(name, _)) => {
                Ok(fhir::Ident { name, source_info: to_src_info(loc) })
            }
            Some(binder @ (Binder::Aggregate(..) | Binder::Unrefined)) => {
                // This shouldn't happen because loc bindings in input position should
                // already be inserted as Binder::Single when gathering parameters and
                // locs in ensure clauses are guaranteed to be locs during the resolving phase.
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

fn resolve_sort(sess: &FluxSession, sort: surface::Ident) -> Result<fhir::Sort, ErrorGuaranteed> {
    if sort.name == SORTS.int {
        Ok(fhir::Sort::Int)
    } else if sort.name == sym::bool {
        Ok(fhir::Sort::Bool)
    } else {
        Err(sess.emit_err(errors::UnresolvedSort::new(sort)))
    }
}

fn resolve_func_sort(
    sess: &FluxSession,
    inputs: &[surface::Ident],
    output: &surface::Ident,
) -> Result<fhir::FuncSort, ErrorGuaranteed> {
    let mut inputs_and_output: Vec<fhir::Sort> = inputs
        .iter()
        .map(|sort| resolve_sort(sess, *sort))
        .try_collect_exhaust()?;
    inputs_and_output.push(resolve_sort(sess, *output)?);
    Ok(fhir::FuncSort { inputs_and_output: List::from_vec(inputs_and_output) })
}

impl Binders {
    fn new() -> Binders {
        Binders { name_gen: IndexGen::new(), map: FxIndexMap::default() }
    }

    fn fresh(&self) -> fhir::Name {
        self.name_gen.fresh()
    }

    fn def_ident(&self, ident: impl Borrow<surface::Ident>) -> Option<surface::Ident> {
        Some(*self.map.get_key_value(ident.borrow())?.0)
    }

    fn get(&self, ident: impl Borrow<surface::Ident>) -> Option<&Binder> {
        self.map.get(ident.borrow())
    }

    fn with_bind<R>(
        &mut self,
        ident: surface::Ident,
        binder: Binder,
        f: impl FnOnce(&mut Self) -> Result<R, ErrorGuaranteed>,
    ) -> Result<(R, Binder), ErrorGuaranteed> {
        let old = self.map.insert(ident, binder);
        let r = f(self)?;
        let binder = if let Some(old) = old {
            self.map.insert(ident, old).unwrap()
        } else {
            self.map.remove(&ident).unwrap()
        };
        Ok((r, binder))
    }

    fn insert_params<P>(
        &mut self,
        sess: &FluxSession,
        params: impl IntoIterator<Item = P>,
    ) -> Result<(), ErrorGuaranteed>
    where
        P: Borrow<surface::Param>,
    {
        for param in params {
            let param = param.borrow();
            self.insert_binder(
                sess,
                param.name,
                Binder::Single(self.fresh(), resolve_sort(sess, param.sort)?),
            )?;
        }
        Ok(())
    }

    fn insert_binder(
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

    fn gather_fn_sig_params(
        &mut self,
        sess: &FluxSession,
        map: &fhir::Map,
        fn_sig: &surface::FnSig<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        for pred in &fn_sig.abstract_params {
            self.insert_binder(
                sess,
                pred.name,
                Binder::Single(
                    self.fresh(),
                    fhir::Sort::Func(resolve_func_sort(sess, &pred.inputs, &pred.output)?),
                ),
            )?;
        }
        for arg in &fn_sig.args {
            self.arg_gather_params(sess, map, arg)?;
        }
        Ok(())
    }

    fn arg_gather_params(
        &mut self,
        sess: &FluxSession,
        map: &fhir::Map,
        arg: &surface::Arg<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            surface::Arg::Constr(bind, path, _) => {
                self.insert_binder(sess, *bind, Binder::from_res(&self.name_gen, map, path.ident))?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.insert_binder(sess, *loc, Binder::Single(self.fresh(), fhir::Sort::Loc))?;
                self.ty_gather_params(sess, map, None, ty)?;
            }
            surface::Arg::Ty(bind, ty) => self.ty_gather_params(sess, map, *bind, ty)?,
            surface::Arg::Alias(..) => panic!("alias are not allowed after expansion"),
        }
        Ok(())
    }

    fn ty_gather_params(
        &mut self,
        sess: &FluxSession,
        map: &fhir::Map,
        bind: Option<surface::Ident>,
        ty: &surface::Ty<Res>,
    ) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            surface::TyKind::Indexed { path, indices } => {
                let binder = Binder::from_res(&self.name_gen, map, path.ident);
                if let Some(bind) = bind {
                    self.insert_binder(sess, bind, binder.clone())?;
                }
                if let [surface::Index::Bind(ident)] = &indices.indices[..] {
                    self.insert_binder(sess, *ident, binder)?;
                } else {
                    let refined_by = binder.deaggregate();
                    let exp = refined_by.len();
                    let got = indices.indices.len();
                    if exp != got {
                        return Err(
                            sess.emit_err(errors::ParamCountMismatch::new(ty.span, exp, got))
                        );
                    }

                    for (idx, (name, sort)) in iter::zip(&indices.indices, refined_by) {
                        if let surface::Index::Bind(bind) = idx {
                            self.insert_binder(sess, *bind, Binder::Single(name, sort))?;
                        }
                    }
                }
                Ok(())
            }
            surface::TyKind::Path(path) => {
                if let Some(bind) = bind {
                    self.insert_binder(
                        sess,
                        bind,
                        Binder::from_res(&self.name_gen, map, path.ident),
                    )?;
                }
                for ty in &path.args {
                    self.ty_gather_params(sess, map, None, ty)?;
                }
                Ok(())
            }
            surface::TyKind::Ref(_, ty)
            | surface::TyKind::Array(ty, _)
            | surface::TyKind::Slice(ty)
            | surface::TyKind::Constr(_, ty) => {
                if let Some(bind) = bind {
                    self.insert_binder(sess, bind, Binder::Unrefined)?;
                }
                self.ty_gather_params(sess, map, None, ty)
            }
            surface::TyKind::Exists { path, .. } => {
                if let Some(bind) = bind {
                    self.insert_binder(
                        sess,
                        bind,
                        Binder::from_res(&self.name_gen, map, path.ident),
                    )?;
                }
                Ok(())
            }
            surface::TyKind::Unit => Ok(()),
        }
    }

    fn into_params(self) -> Vec<fhir::Param> {
        let mut params = vec![];
        for (ident, binder) in self.map {
            match binder {
                Binder::Single(name, sort) => {
                    params.push(param_from_ident(ident, name, sort.clone()))
                }
                Binder::Aggregate(_, fields) => {
                    for (_, (name, sort)) in fields {
                        params.push(param_from_ident(ident, name, sort.clone()));
                    }
                }
                Binder::Unrefined => {}
            }
        }
        params
    }
}

impl<T: Borrow<surface::Ident>> std::ops::Index<T> for Binders {
    type Output = Binder;

    fn index(&self, index: T) -> &Self::Output {
        &self.map[index.borrow()]
    }
}

fn param_from_ident(ident: surface::Ident, name: fhir::Name, sort: fhir::Sort) -> fhir::Param {
    let name = fhir::Ident { name, source_info: to_src_info(ident) };
    fhir::Param { name, sort }
}

fn desugar_bin_op(op: surface::BinOp) -> fhir::BinOp {
    match op {
        surface::BinOp::Iff => fhir::BinOp::Iff,
        surface::BinOp::Imp => fhir::BinOp::Imp,
        surface::BinOp::Or => fhir::BinOp::Or,
        surface::BinOp::And => fhir::BinOp::And,
        surface::BinOp::Eq => fhir::BinOp::Eq,
        surface::BinOp::Gt => fhir::BinOp::Gt,
        surface::BinOp::Ge => fhir::BinOp::Ge,
        surface::BinOp::Lt => fhir::BinOp::Lt,
        surface::BinOp::Le => fhir::BinOp::Le,
        surface::BinOp::Add => fhir::BinOp::Add,
        surface::BinOp::Sub => fhir::BinOp::Sub,
        surface::BinOp::Mod => fhir::BinOp::Mod,
        surface::BinOp::Mul => fhir::BinOp::Mul,
    }
}

impl Binder {
    fn from_res(name_gen: &IndexGen<fhir::Name>, map: &fhir::Map, res: surface::Res) -> Binder {
        match res {
            Res::Bool => Binder::Single(name_gen.fresh(), fhir::Sort::Bool),
            Res::Int(_) | Res::Uint(_) => Binder::Single(name_gen.fresh(), fhir::Sort::Int),
            Res::Adt(def_id) => {
                let fields: FxIndexMap<_, _> = map
                    .refined_by(def_id)
                    .unwrap_or(fhir::RefinedBy::DUMMY)
                    .iter()
                    .map(|param| {
                        let fld = param.name.source_info.1;
                        (fld, (name_gen.fresh(), param.sort.clone()))
                    })
                    .collect();
                Binder::Aggregate(def_id, fields)
            }
            Res::Float(_) | Res::Param(_) | Res::Str | Res::Char => Binder::Unrefined,
        }
    }

    fn deaggregate(self) -> Vec<(fhir::Name, fhir::Sort)> {
        match self {
            Binder::Single(name, sort) => vec![(name, sort)],
            Binder::Aggregate(_, fields) => fields.into_values().collect(),
            Binder::Unrefined => vec![],
        }
    }

    fn names(self) -> Vec<fhir::Name> {
        match self {
            Binder::Single(name, _) => vec![name],
            Binder::Aggregate(_, fields) => fields.into_values().map(|(name, _)| name).collect(),
            Binder::Unrefined => vec![],
        }
    }
}

fn to_src_info(ident: surface::Ident) -> fhir::SourceInfo {
    (ident.span, ident.name)
}

struct Sorts {
    int: Symbol,
}

static SORTS: std::sync::LazyLock<Sorts> =
    std::sync::LazyLock::new(|| Sorts { int: Symbol::intern("int") });

mod errors {
    use flux_macros::{Diagnostic, Subdiagnostic};
    use flux_middle::fhir;
    use rustc_errors::MultiSpan;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(desugar::unresolved_var, code = "FLUX")]
    pub struct UnresolvedVar {
        #[primary_span]
        #[label]
        pub span: Span,
        pub var: Ident,
    }

    impl UnresolvedVar {
        pub fn new(var: Ident) -> Self {
            Self { span: var.span, var }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::duplicate_param, code = "FLUX")]
    pub struct DuplicateParam {
        #[primary_span]
        #[label]
        span: Span,
        name: Symbol,
        #[label(desugar::first_use)]
        first_use: Span,
    }

    impl DuplicateParam {
        pub fn new(old_ident: Ident, new_ident: Ident) -> Self {
            debug_assert_eq!(old_ident.name, new_ident.name);
            Self { span: new_ident.span, name: new_ident.name, first_use: old_ident.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::unresolved_sort, code = "FLUX")]
    pub struct UnresolvedSort {
        #[primary_span]
        #[label]
        pub span: Span,
        pub sort: Ident,
    }

    impl UnresolvedSort {
        pub fn new(sort: Ident) -> Self {
            Self { span: sort.span, sort }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::int_too_large, code = "FLUX")]
    pub struct IntTooLarge {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar::unexpected_literal, code = "FLUX")]
    pub struct UnexpectedLiteral {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar::invalid_dot_var, code = "FLUX")]
    pub struct InvalidDotVar {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(desugar::param_count_mismatch, code = "FLUX")]
    pub struct ParamCountMismatch {
        #[primary_span]
        #[label]
        pub span: Span,
        pub expected: String,
        pub found: usize,
    }

    impl ParamCountMismatch {
        pub fn new(span: Span, exp: usize, found: usize) -> Self {
            let expected = if exp > 1 { format!("1 or {exp:?}") } else { exp.to_string() };
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::unresolved_dot_var, code = "FLUX")]
    pub struct UnresolvedDotVar {
        #[primary_span]
        #[label]
        pub span: Span,
        pub ident: Ident,
        pub msg: String,
    }

    impl UnresolvedDotVar {
        pub fn new<'a>(ident: Ident, fields: impl IntoIterator<Item = &'a Symbol>) -> Self {
            let msg: Vec<String> = fields
                .into_iter()
                .map(|fld| format!("{}.{}", ident.name.as_str(), fld.as_str()))
                .collect();
            let msg = msg.join(", ");
            Self { span: ident.span, ident, msg }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::invalid_primitive_dot_access, code = "FLUX")]
    pub struct InvalidPrimitiveDotAccess<'a> {
        #[primary_span]
        #[label]
        span: Span,
        name: Ident,
        fld: Symbol,
        #[label(desugar::defined_here)]
        def_span: Span,
        sort: &'a fhir::Sort,
    }

    impl<'a> InvalidPrimitiveDotAccess<'a> {
        pub fn new(def_ident: Ident, sort: &'a fhir::Sort, name: Ident, fld: Ident) -> Self {
            let span = name.span.to(fld.span);
            Self { def_span: def_ident.span, sort, span, name, fld: fld.name }
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::field_not_found, code = "FLUX")]
    pub struct FieldNotFound {
        #[primary_span]
        span: Span,
        fld: Ident,
        def_kind: &'static str,
        def_name: String,
        #[subdiagnostic]
        def_note: Option<DefSpanNote>,
    }

    impl FieldNotFound {
        pub fn new(tcx: TyCtxt, map: &fhir::Map, def_id: DefId, fld: Ident) -> Self {
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            let def_name = tcx.def_path_str(def_id);
            let def_note = DefSpanNote::new(tcx, map, def_id);
            Self { span: fld.span, fld, def_kind, def_name, def_note }
        }
    }

    #[derive(Subdiagnostic)]
    #[note(desugar::def_span_note)]
    struct DefSpanNote {
        #[primary_span]
        sp: MultiSpan,
        def_kind: &'static str,
        has_params: bool,
    }

    impl DefSpanNote {
        fn new(tcx: TyCtxt, map: &fhir::Map, def_id: DefId) -> Option<Self> {
            let mut sp = MultiSpan::from_span(tcx.def_ident_span(def_id)?);
            let refined_by = map.refined_by(def_id)?;
            if !refined_by.params.is_empty() {
                sp.push_span_label(refined_by.span, "");
            }
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            Some(Self { sp, def_kind, has_params: !refined_by.params.is_empty() })
        }
    }

    #[derive(Diagnostic)]
    #[diag(desugar::invalid_unrefined_param, code = "FLUX")]
    pub struct InvalidUnrefinedParam {
        #[primary_span]
        #[label]
        pub span: Span,
        pub var: Ident,
        #[label(desugar::defined_here)]
        pub def_span: Span,
    }

    impl InvalidUnrefinedParam {
        pub fn new(def: Ident, var: Ident) -> Self {
            Self { def_span: def.span, var, span: var.span }
        }
    }
}
