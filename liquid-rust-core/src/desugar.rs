/// This module has the code that converts DefFnSig to FnSpec
use crate::{
    diagnostics::{errors, Diagnostics},
    subst::Subst,
    ty::{BaseTy, Constr, Expr, ExprKind, FnSig, Lit, Param, Pred, Refine, Sort, Ty, Var},
};
// use crate::ty::{self, Constr, Expr, Ident, Name, Param, Sort, Ty};
use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_syntax::{
    ast,
    surface::{self, DefFnSig, DefPath, DefTy, Layout},
};
pub use rustc_middle::ty::Variance;
pub use rustc_span::symbol::Ident;
use rustc_span::{
    symbol::{self, kw},
    Span,
};

/// A `BindIn` is the information obtained from a single input-param binding
#[derive(Debug)]
struct BindIn {
    /// pure name corresponding to binder
    gen: Option<Param>,
    /// top-level (pure) constraint corresponding to binder
    exp: Option<Expr>,
    /// type of the binder
    typ: Ty,
    /// location corresponding to (reference) binder
    loc: Option<(crate::ty::Ident, Ty)>,
}

enum ResolvedPath {
    Base(crate::ty::BaseTy),
    Float(crate::ty::FloatTy),
}

struct Desugar {
    prms: Vec<Param>,
    reqs: Vec<Constr>,
    args: Vec<Ty>,
}

fn is_float(path: &DefPath) -> bool {
    match path.ident {
        Layout::Float(_) => true,
        _ => false,
    }
}

fn is_refinable(path: &DefPath) -> bool {
    /* !is_generic(path) && */
    !is_float(path)
}

fn is_bool(path: &DefPath) -> bool {
    match path.ident {
        Layout::Bool => true,
        _ => false,
    }
}

fn convert_path(
    p: DefPath,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<ResolvedPath, ErrorReported> {
    match p.ident {
        Layout::Bool => Ok(ResolvedPath::Base(BaseTy::Bool)),
        Layout::Int(i) => Ok(ResolvedPath::Base(BaseTy::Int(i))),
        Layout::Uint(u) => Ok(ResolvedPath::Base(BaseTy::Uint(u))),
        Layout::Float(f) => Ok(ResolvedPath::Float(f)),
        Layout::Adt(a) => {
            let args = match p.args {
                None => diag.emit_err(errors::InvalidAdt { span: p.span }).raise(),
                Some(tys) => convert_tys(tys, subst, diag),
            };
            Ok(ResolvedPath::Base(BaseTy::Adt(a, args?)))
        }
        _ => diag.emit_err(errors::DesugarError { span: p.span }).raise(),
    }
}

fn convert_tys(
    tys: Vec<DefTy>,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<Vec<Ty>, ErrorReported> {
    let mut res = vec![];
    for ty in tys.into_iter() {
        let ty_ = convert_ty(ty, subst, diag)?;
        res.push(ty_);
    }
    Ok(res)
}

fn convert_base(
    p: DefPath,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<Ty, ErrorReported> {
    match convert_path(p, subst, diag)? {
        ResolvedPath::Float(fty) => Ok(Ty::Float(fty)),
        ResolvedPath::Base(bty) => Ok(Ty::Exists(bty, Pred::TRUE)),
    }
}

fn convert_exists(
    bind: ast::Ident,
    path: DefPath,
    pred: ast::Expr,
    span: Span,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<Ty, ErrorReported> {
    match convert_path(path, subst, diag)? {
        ResolvedPath::Float(_) => err_refined_float(span, diag),
        ResolvedPath::Base(bty) => {
            let pred = desugar_exists(bind, pred, subst, diag)?;
            Ok(Ty::Exists(bty, pred))
        }
    }
}

fn convert_ty(t: DefTy, subst: &mut Subst, diag: &mut Diagnostics) -> Result<Ty, ErrorReported> {
    match t.kind {
        surface::TyKind::Base(p) => convert_base(p, subst, diag),
        surface::TyKind::Exists { bind, path, pred } => {
            convert_exists(bind, path, pred, t.span, subst, diag)
        }
        surface::TyKind::AnonEx { .. } => {
            diag.emit_err(errors::DesugarError { span: t.span }).raise()
        }
        surface::TyKind::Named(_, t) => convert_ty(*t, subst, diag),

        surface::TyKind::Ref(surface::RefKind::Immut, t) => {
            Ok(Ty::ShrRef(Box::new(convert_ty(*t, subst, diag)?)))
        }
        surface::TyKind::Ref(_, t) => Ok(Ty::WeakRef(Box::new(convert_ty(*t, subst, diag)?))),
        surface::TyKind::Refine { path, refine } => {
            let refine = desugar_refine(refine, subst, diag)?;
            match convert_path(path, subst, diag)? {
                ResolvedPath::Float(_) => err_refined_float(t.span, diag),
                ResolvedPath::Base(bty) => Ok(Ty::Refine(bty, refine)),
            }
        }
        surface::TyKind::Param(a) => Ok(Ty::Param(a)),
    }
}

/// `convert_loc` returns the *known* version of the `ast::Ident` and fails otherwise
pub(crate) fn convert_loc(
    loc: ast::Ident,
    subst: &Subst,
    diag: &mut Diagnostics,
) -> Result<crate::ty::Ident, ErrorReported> {
    if let Some(name) = subst.get_loc(loc.name) {
        Ok(crate::ty::Ident { name, source_info: (loc.span, loc.name) })
    } else {
        diag.emit_err(errors::UnresolvedVar::new(loc)).raise()
    }
}

// HACK(ranjitjhala) need better way to "embed" rust types to sort
fn mk_sort(path: &DefPath) -> Sort {
    if is_bool(path) {
        Sort::Bool
    } else {
        Sort::Int
    }
}

pub(crate) fn desugar_pure(
    sym: symbol::Ident,
    sort: Sort,
    name_gen: &IndexGen<crate::ty::Name>,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<Param, ErrorReported> {
    let fresh = name_gen.fresh();
    if subst.insert_expr(sym.name, Var::Free(fresh)).is_some() {
        diag.emit_err(errors::DuplicateParam::new(sym)).raise()
    } else {
        let name = crate::ty::Ident { name: fresh, source_info: (sym.span, sym.name) };
        Ok(Param { name, sort })
    }
}

/// Code to desugar ast::Expr into Expr, see [NOTE:Subst] for the enforced invariants

pub(crate) fn desugar_expr(
    expr: ast::Expr,
    subst: &Subst,
    diagnostics: &mut Diagnostics,
) -> Result<Expr, ErrorReported> {
    let kind = match expr.kind {
        ast::ExprKind::Var(ident) => {
            ExprKind::Var(desugar_var(ident, subst, diagnostics)?, ident.name, ident.span)
        }
        ast::ExprKind::Literal(lit) => ExprKind::Literal(desugar_lit(lit, diagnostics)?),
        ast::ExprKind::BinaryOp(op, e1, e2) => {
            let e1 = desugar_expr(*e1, subst, diagnostics);
            let e2 = desugar_expr(*e2, subst, diagnostics);
            ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
        }
    };
    Ok(Expr { kind, span: Some(expr.span) })
}

fn desugar_var(
    var: ast::Ident,
    subst: &Subst,
    diagnostics: &mut Diagnostics,
) -> Result<crate::ty::Var, ErrorReported> {
    match subst.get_expr(var.name) {
        Some(var) => Ok(var),
        None => {
            diagnostics
                .emit_err(errors::UnresolvedVar::new(var))
                .raise()
        }
    }
}

fn desugar_lit(lit: ast::Lit, diagnostics: &mut Diagnostics) -> Result<Lit, ErrorReported> {
    match lit.kind {
        ast::LitKind::Integer => {
            match lit.symbol.as_str().parse::<i128>() {
                Ok(n) => Ok(Lit::Int(n)),
                Err(_) => {
                    diagnostics
                        .emit_err(errors::IntTooLarge { span: lit.span })
                        .raise()
                }
            }
        }
        ast::LitKind::Bool => Ok(Lit::Bool(lit.symbol == kw::True)),
        _ => {
            diagnostics
                .emit_err(errors::UnexpectedLiteral { span: lit.span })
                .raise()
        }
    }
}

pub(crate) fn desugar_refine(
    refine: ast::Refine,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<Refine, ErrorReported> {
    let exprs = refine
        .exprs
        .into_iter()
        .map(|e| desugar_expr(e, subst, diag))
        .try_collect_exhaust()?;
    Ok(Refine { exprs, span: refine.span })
}

pub(crate) fn desugar_exists(
    bind: ast::Ident,
    pred: ast::Expr,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<Pred, ErrorReported> {
    subst.push_expr_layer();
    subst.insert_expr(bind.name, crate::ty::Var::Bound(0));
    let e = desugar_expr(pred, subst, diag);
    subst.pop_expr_layer();
    Ok(Pred::Expr(e?))
}

pub(crate) fn desugar_loc(
    loc: ast::Ident,
    name_gen: &IndexGen<crate::ty::Name>,
    subst: &mut Subst,
) -> crate::ty::Ident {
    let fresh = name_gen.fresh();
    subst.insert_loc(loc.name, fresh);
    crate::ty::Ident { name: fresh, source_info: (loc.span, loc.name) }
}

fn mk_generic(
    x: symbol::Ident,
    path: &DefPath,
    pred: Option<ast::Expr>,
    name_gen: &IndexGen<crate::ty::Name>,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<(Param, Option<Expr>), ErrorReported> {
    let sort = mk_sort(path);
    let param = desugar_pure(x, sort, name_gen, subst, diag)?;
    let expr = match pred {
        None => None,
        Some(p) => Some(desugar_expr(p, subst, diag)?),
    };
    Ok((param, expr))
}

fn mk_singleton(
    x: symbol::Ident,
    subst: &Subst,
    diag: &mut Diagnostics,
) -> Result<Refine, ErrorReported> {
    let span = x.span;
    let ast_expr = ast::Expr { kind: ast::ExprKind::Var(x), span };
    let e = desugar_expr(ast_expr, subst, diag)?;
    Ok(Refine { exprs: vec![e], span })
}

fn err_refined_float<T>(span: Span, diag: &mut Diagnostics) -> Result<T, ErrorReported> {
    diag.emit_err(errors::RefinedFloat { span }).raise()
}

impl BindIn {
    fn from_path(
        x: symbol::Ident,
        single: bool,
        p: DefPath,
        pred: Option<ast::Expr>,
        name_gen: &IndexGen<crate::ty::Name>,
        subst: &mut Subst,
        diag: &mut Diagnostics,
    ) -> Result<BindIn, ErrorReported> {
        if single && is_refinable(&p) {
            let (param, exp) = mk_generic(x, &p, pred, name_gen, subst, diag)?;
            let refine = mk_singleton(x, subst, diag)?;
            let typ = match convert_path(p, subst, diag)? {
                ResolvedPath::Float(fty) => Ty::Float(fty),
                ResolvedPath::Base(bty) => Ty::Refine(bty, refine),
            };
            Ok(BindIn { gen: Some(param), exp, typ, loc: None })
        } else {
            let typ = convert_base(p, subst, diag)?;
            Ok(BindIn { gen: None, exp: None, typ, loc: None })
        }
    }

    fn from_ty(
        x: symbol::Ident,
        single: bool,
        ty: DefTy,
        name_gen: &IndexGen<crate::ty::Name>,
        subst: &mut Subst,
        diag: &mut Diagnostics,
    ) -> Result<BindIn, ErrorReported> {
        match ty.kind {
            surface::TyKind::AnonEx { path, pred } => {
                BindIn::from_path(x, single, path, Some(pred), name_gen, subst, diag)
            }

            surface::TyKind::Base(path) => {
                BindIn::from_path(x, single, path, None, name_gen, subst, diag)
            }
            surface::TyKind::Refine { path, refine } => {
                let refine = desugar_refine(refine, subst, diag)?;
                let ty = match convert_path(path, subst, diag)? {
                    ResolvedPath::Float(_) => err_refined_float(ty.span, diag),
                    ResolvedPath::Base(bty) => Ok(Ty::Refine(bty, refine)),
                };
                Ok(BindIn { gen: None, exp: None, typ: ty?, loc: None })
            }
            surface::TyKind::Exists { bind, path, pred } => {
                let typ = convert_exists(bind, path, pred, ty.span, subst, diag)?;
                Ok(BindIn { gen: None, exp: None, typ, loc: None })
            }
            surface::TyKind::Named(n, t) => BindIn::from_ty(n, true, *t, name_gen, subst, diag),
            surface::TyKind::Ref(surface::RefKind::Mut, t) => {
                let loc = desugar_loc(x, name_gen, subst);
                let b = BindIn::from_ty(x, false, *t, name_gen, subst, diag)?;
                let typ = Ty::StrgRef(loc);
                Ok(BindIn { gen: b.gen, exp: b.exp, typ, loc: Some((loc, b.typ)) })
            }
            surface::TyKind::Ref(surface::RefKind::Immut, t) => {
                let b = BindIn::from_ty(x, false, *t, name_gen, subst, diag)?;
                let typ = Ty::ShrRef(Box::new(b.typ));
                Ok(BindIn { gen: b.gen, exp: b.exp, typ, loc: None })
            }
            surface::TyKind::Ref(surface::RefKind::Weak, t) => {
                let b = BindIn::from_ty(x, false, *t, name_gen, subst, diag)?;
                let typ = Ty::WeakRef(Box::new(b.typ));
                Ok(BindIn { gen: b.gen, exp: b.exp, typ, loc: None })
            }
            surface::TyKind::Param(a) => {
                let typ = Ty::Param(a);
                Ok(BindIn { gen: None, exp: None, typ, loc: None })
            }
        }
    }
}

impl Desugar {
    fn desugar_inputs(
        &mut self,
        in_sigs: Vec<(rustc_span::symbol::Ident, DefTy)>,
        name_gen: &IndexGen<crate::ty::Name>,
        subst: &mut Subst,
        diag: &mut Diagnostics,
    ) -> Result<(), ErrorReported> {
        for (x, ty) in in_sigs {
            let b_in = BindIn::from_ty(x, true, ty, name_gen, subst, diag)?;
            if let Some(g) = b_in.gen {
                self.prms.push(g);
            }
            if let Some(e) = b_in.exp {
                self.reqs.push(Constr::Pred(e))
            }
            if let Some((loc, ty)) = b_in.loc {
                self.prms.push(Param { name: loc, sort: Sort::Loc });
                self.reqs.push(Constr::Type(loc, ty));
            }
            self.args.push(b_in.typ);
        }
        Ok(())
    }
}

pub(crate) fn desugar(
    dsig: DefFnSig,
    name_gen: &IndexGen<crate::ty::Name>,
    subst: &mut Subst,
    diag: &mut Diagnostics,
) -> Result<FnSig, ErrorReported> {
    let mut me = Desugar { prms: vec![], args: vec![], reqs: vec![] };

    // walk over the input types
    me.desugar_inputs(dsig.requires, name_gen, subst, diag)?;

    // add the "where" clause
    if let Some(e) = dsig.wherep {
        let e_ = desugar_expr(e, &subst, diag)?;
        me.reqs.push(Constr::Pred(e_));
    }

    // translate the output store
    let ensures = dsig
        .ensures
        .into_iter()
        .map(|(loc, ty)| {
            let loc = convert_loc(loc, subst, diag)?;
            let ty = convert_ty(ty, subst, diag)?;
            Ok(Constr::Type(loc, ty))
        })
        .try_collect_exhaust()?;

    let ret = convert_ty(dsig.returns, subst, diag)?;

    Ok(FnSig { params: me.prms, requires: me.reqs, args: me.args, ret, ensures })
}
