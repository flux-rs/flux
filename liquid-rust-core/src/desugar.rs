use std::iter;

use itertools::Itertools;
use liquid_rust_common::index::IndexGen;
use liquid_rust_syntax::surface::{self, Res};
use rustc_hash::FxHashMap;
use rustc_span::{symbol::kw, Symbol};

use crate::ty::{
    AdtDefs, BaseTy, Constr, Expr, ExprKind, FnSig, Ident, Lit, Name, Param, Pred, Refine, Sort,
    Ty, Var,
};

pub struct Desugar<'a> {
    adt_defs: &'a AdtDefs,
    map: FxHashMap<Symbol, Name>,
    params: Vec<Param>,
    name_gen: IndexGen<Name>,
    requires: Vec<Constr>,
}

impl Desugar<'_> {
    pub fn desugar(adt_defs: &AdtDefs, fn_sig: surface::FnSig<Res>) -> FnSig {
        let mut desugar = Desugar {
            adt_defs,
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

    pub fn desugar_arg(&mut self, arg: surface::Arg<Res>) -> Ty {
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

    pub fn desugar_ty(&mut self, ty: surface::Ty<Res>) -> Ty {
        match ty.kind {
            surface::TyKind::Path(surface::Path { ident: Res::Float(float_ty), .. }) => {
                Ty::Float(float_ty)
            }
            surface::TyKind::Path(surface::Path { ident: Res::Param(param_ty), .. }) => {
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
            surface::TyKind::Ref(surface::RefKind::Shr, ty) => {
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

    fn desugar_path_into_bty(&mut self, path: surface::Path<Res>) -> BaseTy {
        match path.ident {
            Res::Bool => BaseTy::Bool,
            Res::Int(int_ty) => BaseTy::Int(int_ty),
            Res::Uint(uint_ty) => BaseTy::Uint(uint_ty),
            Res::Adt(def_id) => {
                let substs = path
                    .args
                    .into_iter()
                    .map(|ty| self.desugar_ty(ty))
                    .collect();
                BaseTy::Adt(def_id, substs)
            }
            Res::Float(..) | Res::Param(..) => {
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

    fn gather_params(&mut self, fn_sig: &surface::FnSig<Res>) {
        for arg in &fn_sig.args {
            self.arg_gather_params(arg);
        }
    }

    fn arg_gather_params(&mut self, arg: &surface::Arg<Res>) {
        match arg {
            surface::Arg::Indexed(bind, path, _) => {
                let sorts = self.sorts(path);
                assert_eq!(sorts.len(), 1);
                self.push_param(*bind, sorts[0]);
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.push_param(*loc, Sort::Loc);
                self.ty_gather_params(ty);
            }
            surface::Arg::Ty(ty) => self.ty_gather_params(ty),
        }
    }

    fn ty_gather_params(&mut self, ty: &surface::Ty<Res>) {
        match &ty.kind {
            surface::TyKind::Indexed { path, indices } => {
                let sorts = self.sorts(path);
                assert_eq!(indices.indices.len(), sorts.len());
                for (index, sort) in iter::zip(&indices.indices, sorts) {
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

    fn sorts(&self, path: &surface::Path<Res>) -> Vec<Sort> {
        match path.ident {
            Res::Bool => vec![Sort::Bool],
            Res::Int(_) => vec![Sort::Int],
            Res::Uint(_) => vec![Sort::Int],
            Res::Adt(def_id) => {
                if let Some(adt_def) = def_id.as_local().and_then(|did| self.adt_defs.get(did)) {
                    adt_def.sorts()
                } else {
                    vec![]
                }
            }
            Res::Float(_) => todo!("refined float"),
            Res::Param(_) => todo!("refined param"),
        }
    }
}
