// /// This module has the code that converts DefFnSig to FnSpec
// use crate::{
//     diagnostics::{errors, Diagnostics},
//     subst::Subst,
//     ty::{BaseTy, Constr, Expr, ExprKind, FnSig, Lit, Param, Pred, Refine, Sort, Ty, Var},
// };
// // use crate::ty::{self, Constr, Expr, Ident, Name, Param, Sort, Ty};
// use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
// use liquid_rust_syntax::{
//     ast,
//     surface::{self, ResFnSig, ResPath, ResPathKind, ResTy},
// };
// pub use rustc_middle::ty::Variance;
// pub use rustc_span::symbol::Ident;
// use rustc_span::{
//     symbol::{self, kw},
//     Span,
// };

// /// A `BindIn` is the information obtained from a single input-param binding
// #[derive(Debug)]
// struct BindIn {
//     /// pure name corresponding to binder
//     gen: Option<Param>,
//     /// top-level (pure) constraint corresponding to binder
//     exp: Option<Expr>,
//     /// type of the binder
//     typ: Ty,
//     /// location corresponding to (reference) binder
//     loc: Option<(crate::ty::Ident, Ty)>,
// }

// /// [NOTE:Resolve-Phase] As some pure-names may be "used" before they are "defined",
// /// e.g. see `tests/pos/surface/scope00.rs`, we structure the resolving into two phases.
// ///   1. Use an erased-DefFnSig to `Gather` generics and build `Subst`
// ///   2. Use the refined-DefFnSig to `Translate` into a `core::FnSig` using `Subst`
// enum Phase {
//     Gather,
//     Translate,
// }

// enum ResolvedPath {
//     Base(crate::ty::BaseTy),
//     Float(crate::ty::FloatTy),
// }

// struct Desugar {
//     prms: Vec<Param>,
//     reqs: Vec<Constr>,
//     args: Vec<Ty>,
// }

// fn is_refinable(path: &ResPath) -> bool {
//     /* !is_generic(path) && */
//     !path.is_float()
// }

// fn convert_path(
//     path: ResPath,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<ResolvedPath, ErrorReported> {
//     match path.kind {
//         ResPathKind::Bool => Ok(ResolvedPath::Base(BaseTy::Bool)),
//         ResPathKind::Int(int_ty) => Ok(ResolvedPath::Base(BaseTy::Int(int_ty))),
//         ResPathKind::Uint(uint_ty) => Ok(ResolvedPath::Base(BaseTy::Uint(uint_ty))),
//         ResPathKind::Float(float_ty) => Ok(ResolvedPath::Float(float_ty)),
//         ResPathKind::Adt(def_id) => {
//             Ok(ResolvedPath::Base(BaseTy::Adt(def_id, convert_tys(path.args, subst, diag)?)))
//         }
//         _ => {
//             let msg = "convert_path".to_string();
//             diag.emit_err(errors::DesugarError { span: path.span, msg })
//                 .raise()
//         }
//     }
// }

// fn convert_tys(
//     tys: Vec<ResTy>,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Vec<Ty>, ErrorReported> {
//     let mut res = vec![];
//     for ty in tys.into_iter() {
//         let ty_ = convert_ty(ty, subst, diag)?;
//         res.push(ty_);
//     }
//     Ok(res)
// }

// fn convert_base(
//     p: ResPath,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Ty, ErrorReported> {
//     match convert_path(p, subst, diag)? {
//         ResolvedPath::Float(fty) => Ok(Ty::Float(fty)),
//         ResolvedPath::Base(bty) => Ok(Ty::Exists(bty, Pred::TRUE)),
//     }
// }

// fn convert_exists(
//     bind: ast::Ident,
//     path: ResPath,
//     pred: ast::Expr,
//     span: Span,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Ty, ErrorReported> {
//     match convert_path(path, subst, diag)? {
//         ResolvedPath::Float(_) => err_refined_float(span, diag),
//         ResolvedPath::Base(bty) => {
//             let pred = desugar_exists(bind, pred, subst, diag)?;
//             Ok(Ty::Exists(bty, pred))
//         }
//     }
// }

// fn convert_ty(t: ResTy, subst: &mut Subst, diag: &mut Diagnostics) -> Result<Ty, ErrorReported> {
//     match t.kind {
//         surface::TyKind::Path(p) => convert_base(p, subst, diag),
//         surface::TyKind::Exists { bind, path, pred } => {
//             convert_exists(bind, path, pred, t.span, subst, diag)
//         }
//         surface::TyKind::AnonEx { .. } => {
//             let msg = "convert_ty".to_string();
//             diag.emit_err(errors::DesugarError { span: t.span, msg })
//                 .raise()
//         }
//         surface::TyKind::Named(_, t) => convert_ty(*t, subst, diag),

//         surface::TyKind::Ref(surface::RefKind::Immut, t) => {
//             Ok(Ty::ShrRef(Box::new(convert_ty(*t, subst, diag)?)))
//         }
//         surface::TyKind::Ref(_, t) => Ok(Ty::WeakRef(Box::new(convert_ty(*t, subst, diag)?))),
//         surface::TyKind::Refine { path, refine } => {
//             let refine = desugar_refine(refine, subst, diag)?;
//             match convert_path(path, subst, diag)? {
//                 ResolvedPath::Float(_) => err_refined_float(t.span, diag),
//                 ResolvedPath::Base(bty) => Ok(Ty::Refine(bty, refine)),
//             }
//         }
//     }
// }

// /// `convert_loc` returns the *known* version of the `ast::Ident` and fails otherwise
// pub(crate) fn convert_loc(
//     loc: ast::Ident,
//     subst: &Subst,
//     diag: &mut Diagnostics,
// ) -> Result<crate::ty::Ident, ErrorReported> {
//     if let Some(name) = subst.get_loc(loc.name) {
//         Ok(crate::ty::Ident { name, source_info: (loc.span, loc.name) })
//     } else {
//         diag.emit_err(errors::UnresolvedVar::new(loc)).raise()
//     }
// }

// // HACK(ranjitjhala) need better way to "embed" rust types to sort
// fn mk_sort(path: &ResPath) -> Sort {
//     if path.is_bool() {
//         Sort::Bool
//     } else {
//         Sort::Int
//     }
// }

// pub(crate) fn desugar_pure(
//     sym: symbol::Ident,
//     sort: Sort,
//     name_gen: &IndexGen<crate::ty::Name>,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Param, ErrorReported> {
//     let fresh = name_gen.fresh();
//     if subst.insert_expr(sym.name, Var::Free(fresh)).is_some() {
//         let msg = "already used".to_string();
//         diag.emit_err(errors::BadParam::new(sym, msg)).raise()
//     } else {
//         let name = crate::ty::Ident { name: fresh, source_info: (sym.span, sym.name) };
//         Ok(Param { name, sort })
//     }
// }

// /// `desugar_pure_translate` is used in the `Translate` phase *after*
// /// we have `Gather`ed all the pure-names in the `Subst`.
// /// See [NOTE:Resolve-Phase]
// fn desugar_pure_translate(
//     sym: symbol::Ident,
//     sort: Sort,
//     name_gen: &IndexGen<crate::ty::Name>,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Param, ErrorReported> {
//     let fresh_cand = name_gen.fresh();
//     match subst.insert_expr(sym.name, Var::Free(fresh_cand)) {
//         Some(Var::Free(fresh)) => {
//             let name = crate::ty::Ident { name: fresh, source_info: (sym.span, sym.name) };
//             Ok(Param { name, sort })
//         }
//         _ => {
//             let msg = "not defined".to_string();
//             diag.emit_err(errors::BadParam::new(sym, msg)).raise()
//         }
//     }
// }

// /// Code to desugar ast::Expr into Expr, see [NOTE:Subst] for the enforced invariants
// pub(crate) fn desugar_expr(
//     expr: ast::Expr,
//     subst: &Subst,
//     diagnostics: &mut Diagnostics,
// ) -> Result<Expr, ErrorReported> {
//     let kind = match expr.kind {
//         ast::ExprKind::Var(ident) => {
//             ExprKind::Var(desugar_var(ident, subst, diagnostics)?, ident.name, ident.span)
//         }
//         ast::ExprKind::Literal(lit) => ExprKind::Literal(desugar_lit(lit, diagnostics)?),
//         ast::ExprKind::BinaryOp(op, e1, e2) => {
//             let e1 = desugar_expr(*e1, subst, diagnostics);
//             let e2 = desugar_expr(*e2, subst, diagnostics);
//             ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
//         }
//     };
//     Ok(Expr { kind, span: Some(expr.span) })
// }

// fn desugar_var(
//     var: ast::Ident,
//     subst: &Subst,
//     diagnostics: &mut Diagnostics,
// ) -> Result<crate::ty::Var, ErrorReported> {
//     match subst.get_expr(var.name) {
//         Some(var) => Ok(var),
//         None => {
//             diagnostics
//                 .emit_err(errors::UnresolvedVar::new(var))
//                 .raise()
//         }
//     }
// }

// fn desugar_lit(lit: ast::Lit, diagnostics: &mut Diagnostics) -> Result<Lit, ErrorReported> {
//     match lit.kind {
//         ast::LitKind::Integer => {
//             match lit.symbol.as_str().parse::<i128>() {
//                 Ok(n) => Ok(Lit::Int(n)),
//                 Err(_) => {
//                     diagnostics
//                         .emit_err(errors::IntTooLarge { span: lit.span })
//                         .raise()
//                 }
//             }
//         }
//         ast::LitKind::Bool => Ok(Lit::Bool(lit.symbol == kw::True)),
//         _ => {
//             diagnostics
//                 .emit_err(errors::UnexpectedLiteral { span: lit.span })
//                 .raise()
//         }
//     }
// }

// pub(crate) fn desugar_refine(
//     refine: ast::Refine,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Refine, ErrorReported> {
//     let exprs = refine
//         .exprs
//         .into_iter()
//         .map(|e| desugar_expr(e, subst, diag))
//         .try_collect_exhaust()?;
//     Ok(Refine { exprs, span: refine.span })
// }

// pub(crate) fn desugar_exists(
//     bind: ast::Ident,
//     pred: ast::Expr,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Pred, ErrorReported> {
//     subst.push_expr_layer();
//     subst.insert_expr(bind.name, crate::ty::Var::Bound(0));
//     let e = desugar_expr(pred, subst, diag);
//     subst.pop_expr_layer();
//     Ok(Pred::Expr(e?))
// }

// pub(crate) fn desugar_loc(
//     loc: ast::Ident,
//     name_gen: &IndexGen<crate::ty::Name>,
//     subst: &mut Subst,
// ) -> crate::ty::Ident {
//     let fresh = name_gen.fresh();
//     subst.insert_loc(loc.name, fresh);
//     crate::ty::Ident { name: fresh, source_info: (loc.span, loc.name) }
// }

// fn mk_generic(
//     phase: Phase,
//     x: symbol::Ident,
//     path: &ResPath,
//     pred: Option<ast::Expr>,
//     name_gen: &IndexGen<crate::ty::Name>,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<(Param, Option<Expr>), ErrorReported> {
//     let sort = mk_sort(path);
//     let param = match phase {
//         Phase::Gather => desugar_pure(x, sort, name_gen, subst, diag)?,
//         Phase::Translate => desugar_pure_translate(x, sort, name_gen, subst, diag)?,
//     };
//     let expr = match pred {
//         None => None,
//         Some(p) => Some(desugar_expr(p, subst, diag)?),
//     };
//     Ok((param, expr))
// }

// fn mk_singleton(
//     x: symbol::Ident,
//     subst: &Subst,
//     diag: &mut Diagnostics,
// ) -> Result<Refine, ErrorReported> {
//     let span = x.span;
//     let ast_expr = ast::Expr { kind: ast::ExprKind::Var(x), span };
//     let e = desugar_expr(ast_expr, subst, diag)?;
//     Ok(Refine { exprs: vec![e], span })
// }

// fn err_refined_float<T>(span: Span, diag: &mut Diagnostics) -> Result<T, ErrorReported> {
//     diag.emit_err(errors::RefinedFloat { span }).raise()
// }

// impl BindIn {
//     fn from_path(
//         phase: Phase,
//         x: symbol::Ident,
//         single: bool,
//         p: ResPath,
//         pred: Option<ast::Expr>,
//         name_gen: &IndexGen<crate::ty::Name>,
//         subst: &mut Subst,
//         diag: &mut Diagnostics,
//     ) -> Result<BindIn, ErrorReported> {
//         if single && is_refinable(&p) {
//             let (param, exp) = mk_generic(phase, x, &p, pred, name_gen, subst, diag)?;
//             let refine = mk_singleton(x, subst, diag)?;
//             let typ = match convert_path(p, subst, diag)? {
//                 ResolvedPath::Float(fty) => Ty::Float(fty),
//                 ResolvedPath::Base(bty) => Ty::Refine(bty, refine),
//             };
//             let res = Ok(BindIn { gen: Some(param), exp, typ, loc: None });
//             res
//         } else {
//             let typ = convert_base(p, subst, diag)?;
//             Ok(BindIn { gen: None, exp: None, typ, loc: None })
//         }
//     }

//     fn from_ty(
//         phase: Phase,
//         x: symbol::Ident,
//         single: bool,
//         ty: ResTy,
//         name_gen: &IndexGen<crate::ty::Name>,
//         subst: &mut Subst,
//         diag: &mut Diagnostics,
//     ) -> Result<BindIn, ErrorReported> {
//         match ty.kind {
//             surface::TyKind::AnonEx { path, pred } => {
//                 BindIn::from_path(phase, x, single, path, Some(pred), name_gen, subst, diag)
//             }
//             surface::TyKind::Path(path) => {
//                 BindIn::from_path(phase, x, single, path, None, name_gen, subst, diag)
//             }
//             surface::TyKind::Refine { path, refine } => {
//                 let refine = desugar_refine(refine, subst, diag)?;
//                 let ty = match convert_path(path, subst, diag)? {
//                     ResolvedPath::Float(_) => err_refined_float(ty.span, diag),
//                     ResolvedPath::Base(bty) => Ok(Ty::Refine(bty, refine)),
//                 };
//                 Ok(BindIn { gen: None, exp: None, typ: ty?, loc: None })
//             }
//             surface::TyKind::Exists { bind, path, pred } => {
//                 let typ = convert_exists(bind, path, pred, ty.span, subst, diag)?;
//                 Ok(BindIn { gen: None, exp: None, typ, loc: None })
//             }
//             surface::TyKind::Named(n, t) => {
//                 BindIn::from_ty(phase, n, true, *t, name_gen, subst, diag)
//             }
//             surface::TyKind::Ref(surface::RefKind::Mut, t) => {
//                 let loc = desugar_loc(x, name_gen, subst);
//                 let b = BindIn::from_ty(phase, x, false, *t, name_gen, subst, diag)?;
//                 let typ = Ty::StrgRef(loc);
//                 Ok(BindIn { gen: b.gen, exp: b.exp, typ, loc: Some((loc, b.typ)) })
//             }
//             surface::TyKind::Ref(surface::RefKind::Immut, t) => {
//                 let b = BindIn::from_ty(phase, x, false, *t, name_gen, subst, diag)?;
//                 let typ = Ty::ShrRef(Box::new(b.typ));
//                 Ok(BindIn { gen: b.gen, exp: b.exp, typ, loc: None })
//             }
//             surface::TyKind::Ref(surface::RefKind::Weak, t) => {
//                 let b = BindIn::from_ty(phase, x, false, *t, name_gen, subst, diag)?;
//                 let typ = Ty::WeakRef(Box::new(b.typ));
//                 Ok(BindIn { gen: b.gen, exp: b.exp, typ, loc: None })
//             }
//         }
//     }
// }

// impl Desugar {
//     fn desugar_inputs(
//         &mut self,
//         in_sigs: Vec<(rustc_span::symbol::Ident, ResTy)>,
//         name_gen: &IndexGen<crate::ty::Name>,
//         subst: &mut Subst,
//         diag: &mut Diagnostics,
//     ) -> Result<(), ErrorReported> {
//         // See [NOTE:Resolve-Phase]
//         for (x, ty) in in_sigs.iter() {
//             BindIn::from_ty(Phase::Gather, *x, true, ty, name_gen, subst, diag)?;
//         }

//         for (x, ty) in in_sigs {
//             let b_in = BindIn::from_ty(Phase::Translate, x, true, ty, name_gen, subst, diag)?;
//             if let Some(g) = b_in.gen {
//                 self.prms.push(g);
//             }
//             if let Some(e) = b_in.exp {
//                 self.reqs.push(Constr::Pred(e))
//             }
//             if let Some((loc, ty)) = b_in.loc {
//                 self.prms.push(Param { name: loc, sort: Sort::Loc });
//                 self.reqs.push(Constr::Type(loc, ty));
//             }
//             self.args.push(b_in.typ);
//         }
//         Ok(())
//     }
// }

// pub(crate) fn desugar(
//     dsig: ResFnSig,
//     name_gen: &IndexGen<crate::ty::Name>,
//     subst: &mut Subst,
//     diag: &mut Diagnostics,
// ) -> Result<FnSig, ErrorReported> {
//     let mut me = Desugar { prms: vec![], args: vec![], reqs: vec![] };

//     // walk over the input types
//     me.desugar_inputs(dsig.requires, name_gen, subst, diag)?;

//     // add the "where" clause
//     if let Some(e) = dsig.wherep {
//         let e_ = desugar_expr(e, &subst, diag)?;
//         me.reqs.push(Constr::Pred(e_));
//     }

//     // translate the output store
//     let ensures = dsig
//         .ensures
//         .into_iter()
//         .map(|(loc, ty)| {
//             let loc = convert_loc(loc, subst, diag)?;
//             let ty = convert_ty(ty, subst, diag)?;
//             Ok(Constr::Type(loc, ty))
//         })
//         .try_collect_exhaust()?;

//     let ret = convert_ty(dsig.returns, subst, diag)?;

//     Ok(FnSig { params: me.prms, requires: me.reqs, args: me.args, ret, ensures })
// }

use itertools::Itertools;
use liquid_rust_common::index::IndexGen;
use liquid_rust_syntax::surface::{self, ResArg, ResFnSig, ResPath, ResPathKind, ResTy};
use rustc_hash::FxHashMap;
use rustc_span::{symbol::kw, Symbol};

use crate::ty::{
    BaseTy, Constr, Expr, ExprKind, FnSig, Ident, Lit, Name, Param, Pred, Refine, Sort, Ty, Var,
};

pub struct Desugar {
    map: FxHashMap<Symbol, Name>,
    params: Vec<Param>,
    name_gen: IndexGen<Name>,
    requires: Vec<Constr>,
}

impl Desugar {
    pub fn desugar(fn_sig: ResFnSig) -> FnSig {
        let mut desugar = Desugar {
            map: FxHashMap::default(),
            params: vec![],
            name_gen: IndexGen::new(),
            requires: vec![],
        };

        desugar.gather_params(&fn_sig);

        let args = fn_sig
            .args
            .into_iter()
            .map(|arg| desugar.desugar_arg(arg))
            .collect_vec();

        if let Some(e) = fn_sig.requires {
            let e = desugar.desugar_expr(e, None);
            desugar.requires.push(Constr::Pred(e));
        }

        let ret = desugar.desugar_ty(fn_sig.returns);

        let ensures = fn_sig
            .ensures
            .into_iter()
            .map(|(bind, ty)| {
                let source_info = (bind.span, bind.name);
                let loc = Ident { name: desugar.map[&bind.name], source_info };
                let ty = desugar.desugar_ty(ty);
                Constr::Type(loc, ty)
            })
            .collect_vec();

        FnSig { params: desugar.params, requires: desugar.requires, args, ret, ensures }
    }

    pub fn desugar_arg(&mut self, arg: ResArg) -> Ty {
        match arg {
            surface::Arg::Indexed(bind, path, pred) => {
                if let Some(pred) = pred {
                    self.requires
                        .push(Constr::Pred(self.desugar_expr(pred, None)));
                }
                let bty = self.desugar_path_into_bty(path);
                let var = self.desugar_var(bind, None);
                let indices = Refine { exprs: vec![var], span: bind.span };
                Ty::Refine(bty, indices)
            }
            surface::Arg::StrgRef(loc, ty) => {
                let source_info = (loc.span, loc.name);
                let loc = Ident { name: self.map[&loc.name], source_info };
                let ty = self.desugar_ty(ty);
                self.requires.push(Constr::Type(loc, ty));
                Ty::StrgRef(loc)
            }
            surface::Arg::Ty(ty) => self.desugar_ty(ty),
        }
    }

    pub fn desugar_ty(&mut self, ty: ResTy) -> Ty {
        match ty.kind {
            surface::TyKind::Path(ResPath { kind: ResPathKind::Float(float_ty), .. }) => {
                Ty::Float(float_ty)
            }
            surface::TyKind::Path(ResPath { kind: ResPathKind::Param(param_ty), .. }) => {
                Ty::Param(param_ty)
            }
            surface::TyKind::Path(path) => {
                let bty = self.desugar_path_into_bty(path);
                Ty::Exists(bty, Pred::TRUE)
            }
            surface::TyKind::Indexed { path, indices } => {
                let bty = self.desugar_path_into_bty(path);
                let indices = self.desugar_indices(indices);
                Ty::Refine(bty, indices)
            }
            surface::TyKind::Exists { bind, path, pred } => {
                let bty = self.desugar_path_into_bty(path);
                let pred = self.desugar_expr(pred, Some(bind.name));
                Ty::Exists(bty, Pred::Expr(pred))
            }
            surface::TyKind::Ref(surface::RefKind::Immut, ty) => {
                Ty::ShrRef(Box::new(self.desugar_ty(*ty)))
            }
            surface::TyKind::Ref(surface::RefKind::Mut, ty) => {
                Ty::WeakRef(Box::new(self.desugar_ty(*ty)))
            }
            surface::TyKind::StrgRef(loc, ty) => {
                let source_info = (loc.span, loc.name);
                let loc = Ident { name: self.map[&loc.name], source_info };
                let ty = self.desugar_ty(*ty);
                self.requires.push(Constr::Type(loc, ty));
                Ty::StrgRef(loc)
            }
        }
    }

    pub fn desugar_indices(&self, indices: surface::Indices) -> Refine {
        let exprs = indices
            .indices
            .into_iter()
            .map(|index| {
                match index {
                    surface::Index::Bind(ident) => self.desugar_var(ident, None),

                    surface::Index::Expr(expr) => self.desugar_expr(expr, None),
                }
            })
            .collect();
        Refine { exprs, span: indices.span }
    }

    fn desugar_path_into_bty(&mut self, path: ResPath) -> BaseTy {
        match path.kind {
            ResPathKind::Bool => BaseTy::Bool,
            ResPathKind::Int(int_ty) => BaseTy::Int(int_ty),
            ResPathKind::Uint(uint_ty) => BaseTy::Uint(uint_ty),
            ResPathKind::Adt(def_id) => {
                let substs = path
                    .args
                    .into_iter()
                    .map(|ty| self.desugar_ty(ty))
                    .collect();
                BaseTy::Adt(def_id, substs)
            }
            ResPathKind::Float(..) | ResPathKind::Param(..) => {
                panic!("invalid")
            }
        }
    }

    pub(crate) fn desugar_expr(&self, expr: surface::Expr, bound: Option<Symbol>) -> Expr {
        let kind = match expr.kind {
            surface::ExprKind::Var(ident) => return self.desugar_var(ident, bound),
            surface::ExprKind::Literal(lit) => ExprKind::Literal(self.desugar_lit(lit)),
            surface::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.desugar_expr(*e1, bound);
                let e2 = self.desugar_expr(*e2, bound);
                ExprKind::BinaryOp(op, Box::new(e1), Box::new(e2))
            }
        };
        Expr { kind, span: Some(expr.span) }
    }

    fn desugar_lit(&self, lit: surface::Lit) -> Lit {
        match lit.kind {
            surface::LitKind::Integer => {
                match lit.symbol.as_str().parse::<i128>() {
                    Ok(n) => Lit::Int(n),
                    Err(_) => {
                        panic!("integer too large")
                    }
                }
            }
            surface::LitKind::Bool => Lit::Bool(lit.symbol == kw::True),
            _ => panic!("UnexpectedLiteral"),
        }
    }

    fn desugar_var(&self, indent: surface::Ident, bound: Option<Symbol>) -> Expr {
        // TODO(nilehmann) consider bound variables
        let var = if Some(indent.name) == bound {
            Var::Bound(0)
        } else {
            Var::Free(self.map[&indent.name])
        };
        let kind = ExprKind::Var(var, indent.name, indent.span);
        Expr { kind, span: Some(indent.span) }
    }

    // Gather parameters

    fn gather_params(&mut self, fn_sig: &ResFnSig) {
        for arg in &fn_sig.args {
            self.arg_gather_params(arg);
        }
    }

    fn arg_gather_params(&mut self, arg: &ResArg) {
        match arg {
            surface::Arg::Indexed(bind, path, _) => {
                let sort = guess_sort(path);
                self.push_param(*bind, sort);
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.push_param(*loc, Sort::Loc);
                self.ty_gather_params(ty);
            }
            surface::Arg::Ty(ty) => self.ty_gather_params(ty),
        }
    }

    fn ty_gather_params(&mut self, ty: &ResTy) {
        match &ty.kind {
            surface::TyKind::Indexed { path, indices } => {
                let sort = guess_sort(path);
                for index in &indices.indices {
                    if let surface::Index::Bind(bind) = index {
                        self.push_param(*bind, sort);
                    }
                }
            }
            surface::TyKind::StrgRef(_, ty) | surface::TyKind::Ref(_, ty) => {
                self.ty_gather_params(ty);
            }
            surface::TyKind::Path(_) | surface::TyKind::Exists { .. } => {}
        }
    }

    fn push_param(&mut self, ident: surface::Ident, sort: Sort) {
        let fresh = self.name_gen.fresh();
        let source_info = (ident.span, ident.name);

        self.map.insert(ident.name, fresh);
        self.params
            .push(Param { name: Ident { name: fresh, source_info }, sort });
    }
}

// HACK(nilehmann) use sort as declared in GlobalEnv
fn guess_sort(path: &ResPath) -> Sort {
    match path.kind {
        ResPathKind::Bool => Sort::Bool,
        ResPathKind::Int(_) => Sort::Int,
        ResPathKind::Uint(_) => Sort::Int,
        ResPathKind::Adt(_) => Sort::Int,
        ResPathKind::Float(_) => todo!("refined float"),
        ResPathKind::Param(_) => todo!("refined param"),
    }
}
