use std::iter;

use itertools::Itertools;
use liquid_rust_common::{index::IndexGen, iter::IterExt};
use liquid_rust_syntax::{
    ast,
    surface::{self, Res},
};
use rustc_errors::ErrorReported;
use rustc_hash::FxHashMap;
use rustc_session::Session;
use rustc_span::{sym, symbol::kw, Symbol};

use crate::ty::{
    AdtDef, BaseTy, Constr, Expr, ExprKind, FnSig, Ident, Indices, Lit, Name, Param, Pred,
    Qualifier, RefinedByMap, Sort, Ty, Var,
};

pub fn desugar_qualifier(
    sess: &Session,
    qualifier: ast::Qualifier,
) -> Result<Qualifier, ErrorReported> {
    let mut cx = DesugarCtxt::new(sess);
    for param in qualifier.args {
        cx.push_param(param.name, resolve_sort(param.sort));
    }
    let name = qualifier.name.name.to_ident_string();
    let expr = cx.desugar_expr(qualifier.expr, None);

    Ok(Qualifier { name, args: cx.params, expr: expr? })
}

pub fn desugar_params(params: &surface::Params) -> Vec<Param> {
    let name_gen = IndexGen::new();
    params
        .params
        .iter()
        .map(|param| {
            let fresh = name_gen.fresh();
            let name = Ident { name: fresh, source_info: (param.name.span, param.name.name) };
            Param { name, sort: resolve_sort(param.sort) }
        })
        .collect_vec()
}

pub fn desugar_adt(sess: &Session, adt_def: surface::AdtDef<Res>) -> Result<AdtDef, ErrorReported> {
    let mut cx = DesugarCtxt::new(sess);

    for param in adt_def.refined_by.into_iter().flatten() {
        cx.push_param(param.name, resolve_sort(param.sort));
    }

    if adt_def.opaque {
        Ok(AdtDef::Opaque { refined_by: cx.params })
    } else {
        let fields = adt_def
            .fields
            .into_iter()
            .map(|ty| cx.desugar_ty(ty.unwrap()))
            .try_collect_exhaust()?;
        Ok(AdtDef::Transparent { refined_by: cx.params, fields })
    }
}

pub fn desugar_fn_sig(
    sess: &Session,
    refined_by: &impl RefinedByMap,
    fn_sig: surface::FnSig<Res>,
) -> Result<FnSig, ErrorReported> {
    let mut desugar = DesugarCtxt::new(sess);

    desugar.gather_params(&fn_sig, refined_by);

    if let Some(e) = fn_sig.requires {
        let e = desugar.desugar_expr(e, None)?;
        desugar.requires.push(Constr::Pred(e));
    }

    let args = fn_sig
        .args
        .into_iter()
        .map(|arg| desugar.desugar_arg(arg))
        .try_collect_exhaust();

    let ret = desugar.desugar_ty(fn_sig.returns);

    let ensures = fn_sig
        .ensures
        .into_iter()
        .map(|(bind, ty)| {
            let source_info = (bind.span, bind.name);
            let loc = Ident { name: desugar.map[&bind.name], source_info };
            let ty = desugar.desugar_ty(ty)?;
            Ok(Constr::Type(loc, ty))
        })
        .try_collect_exhaust();

    Ok(FnSig {
        params: desugar.params,
        requires: desugar.requires,
        args: args?,
        ret: ret?,
        ensures: ensures?,
    })
}

struct DesugarCtxt<'a> {
    sess: &'a Session,
    name_gen: IndexGen<Name>,
    map: FxHashMap<Symbol, Name>,
    params: Vec<Param>,
    requires: Vec<Constr>,
}

impl DesugarCtxt<'_> {
    fn new(sess: &Session) -> DesugarCtxt {
        DesugarCtxt {
            sess,
            name_gen: IndexGen::new(),
            map: FxHashMap::default(),
            params: vec![],
            requires: vec![],
        }
    }

    fn desugar_arg(&mut self, arg: surface::Arg<Res>) -> Result<Ty, ErrorReported> {
        match arg {
            surface::Arg::Indexed(bind, path, pred) => {
                if let Some(pred) = pred {
                    self.requires
                        .push(Constr::Pred(self.desugar_expr(pred, None)?));
                }
                let bty = self.desugar_path_into_bty(path);
                let var = self.desugar_var(bind, None)?;
                let indices = Indices { exprs: vec![var], span: bind.span };
                Ok(Ty::Indexed(bty?, indices))
            }
            surface::Arg::StrgRef(loc, ty) => {
                let source_info = (loc.span, loc.name);
                let loc = Ident { name: self.map[&loc.name], source_info };
                let ty = self.desugar_ty(ty)?;
                self.requires.push(Constr::Type(loc, ty));
                Ok(Ty::Ptr(loc))
            }
            surface::Arg::Ty(ty) => self.desugar_ty(ty),
        }
    }

    fn desugar_ty(&mut self, ty: surface::Ty<Res>) -> Result<Ty, ErrorReported> {
        let ty = match ty.kind {
            surface::TyKind::Path(surface::Path { ident: Res::Float(float_ty), .. }) => {
                Ty::Float(float_ty)
            }
            surface::TyKind::Path(surface::Path { ident: Res::Param(param_ty), .. }) => {
                Ty::Param(param_ty)
            }
            surface::TyKind::Path(path) => {
                let bty = self.desugar_path_into_bty(path)?;
                Ty::Exists(bty, Pred::TRUE)
            }
            surface::TyKind::Indexed { path, indices } => {
                let bty = self.desugar_path_into_bty(path);
                let indices = self.desugar_indices(indices);
                Ty::Indexed(bty?, indices?)
            }
            surface::TyKind::Exists { bind, path, pred } => {
                let bty = self.desugar_path_into_bty(path);
                let pred = self.desugar_expr(pred, Some(bind.name));
                Ty::Exists(bty?, Pred::Expr(pred?))
            }
            surface::TyKind::Ref(rk, ty) => Ty::Ref(rk, Box::new(self.desugar_ty(*ty)?)),
            surface::TyKind::StrgRef(loc, ty) => {
                let source_info = (loc.span, loc.name);
                let loc = Ident { name: self.map[&loc.name], source_info };
                let ty = self.desugar_ty(*ty)?;
                self.requires.push(Constr::Type(loc, ty));
                Ty::Ptr(loc)
            }
        };
        Ok(ty)
    }

    fn desugar_indices(&self, indices: surface::Indices) -> Result<Indices, ErrorReported> {
        let exprs = indices
            .indices
            .into_iter()
            .map(|index| {
                match index {
                    surface::Index::Bind(ident) => self.desugar_var(ident, None),

                    surface::Index::Expr(expr) => self.desugar_expr(expr, None),
                }
            })
            .try_collect_exhaust()?;
        Ok(Indices { exprs, span: indices.span })
    }

    fn desugar_path_into_bty(&mut self, path: surface::Path<Res>) -> Result<BaseTy, ErrorReported> {
        let bty = match path.ident {
            Res::Bool => BaseTy::Bool,
            Res::Int(int_ty) => BaseTy::Int(int_ty),
            Res::Uint(uint_ty) => BaseTy::Uint(uint_ty),
            Res::Adt(def_id) => {
                let substs = path
                    .args
                    .into_iter()
                    .map(|ty| self.desugar_ty(ty))
                    .try_collect_exhaust()?;
                BaseTy::Adt(def_id, substs)
            }
            Res::Float(..) | Res::Param(..) => {
                panic!("invalid")
            }
        };
        Ok(bty)
    }

    pub(crate) fn desugar_expr(
        &self,
        expr: surface::Expr,
        bound: Option<Symbol>,
    ) -> Result<Expr, ErrorReported> {
        let kind = match expr.kind {
            surface::ExprKind::Var(ident) => return self.desugar_var(ident, bound),
            surface::ExprKind::Literal(lit) => ExprKind::Literal(self.desugar_lit(lit)),
            surface::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.desugar_expr(*e1, bound);
                let e2 = self.desugar_expr(*e2, bound);
                ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
            }
        };
        Ok(Expr { kind, span: Some(expr.span) })
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

    fn desugar_var(
        &self,
        ident: surface::Ident,
        bound: Option<Symbol>,
    ) -> Result<Expr, ErrorReported> {
        let var = if Some(ident.name) == bound {
            Var::Bound(0)
        } else if let Some(&name) = self.map.get(&ident.name) {
            Var::Free(name)
        } else {
            return Err(self.sess.emit_err(errors::UnresolvedVar::new(ident)));
        };
        let kind = ExprKind::Var(var, ident.name, ident.span);
        Ok(Expr { kind, span: Some(ident.span) })
    }

    fn push_param(&mut self, ident: surface::Ident, sort: Sort) {
        // TODO(nilehmann) report error if param already exists
        let fresh = self.name_gen.fresh();
        let source_info = (ident.span, ident.name);

        self.map.insert(ident.name, fresh);
        self.params
            .push(Param { name: Ident { name: fresh, source_info }, sort });
    }

    // Gather parameters

    fn gather_params(&mut self, fn_sig: &surface::FnSig<Res>, refined_by: &impl RefinedByMap) {
        for arg in &fn_sig.args {
            self.arg_gather_params(arg, refined_by);
        }
    }

    fn arg_gather_params(&mut self, arg: &surface::Arg<Res>, refined_by: &impl RefinedByMap) {
        match arg {
            surface::Arg::Indexed(bind, path, _) => {
                let sorts = self.sorts(path, refined_by);
                assert_eq!(sorts.len(), 1);
                self.push_param(*bind, sorts[0]);
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.push_param(*loc, Sort::Loc);
                self.ty_gather_params(ty, refined_by);
            }
            surface::Arg::Ty(ty) => self.ty_gather_params(ty, refined_by),
        }
    }

    fn ty_gather_params(&mut self, ty: &surface::Ty<Res>, refined_by: &impl RefinedByMap) {
        match &ty.kind {
            surface::TyKind::Indexed { path, indices } => {
                let sorts = self.sorts(path, refined_by);
                assert_eq!(indices.indices.len(), sorts.len());
                for (index, sort) in iter::zip(&indices.indices, sorts) {
                    if let surface::Index::Bind(bind) = index {
                        self.push_param(*bind, sort);
                    }
                }
            }
            surface::TyKind::StrgRef(_, ty) | surface::TyKind::Ref(_, ty) => {
                self.ty_gather_params(ty, refined_by);
            }
            surface::TyKind::Path(_) | surface::TyKind::Exists { .. } => {}
        }
    }

    fn sorts(&self, path: &surface::Path<Res>, refined_by: &impl RefinedByMap) -> Vec<Sort> {
        match path.ident {
            Res::Bool => vec![Sort::Bool],
            Res::Int(_) => vec![Sort::Int],
            Res::Uint(_) => vec![Sort::Int],
            Res::Adt(def_id) => {
                if let Some(params) = refined_by.get(def_id) {
                    params.iter().map(|param| param.sort).collect()
                } else {
                    vec![]
                }
            }
            Res::Float(_) => todo!("refined float"),
            Res::Param(_) => todo!("refined param"),
        }
    }
}

fn resolve_sort(sort: surface::Ident) -> Sort {
    if sort.name == SORTS.int {
        Sort::Int
    } else if sort.name == sym::bool {
        Sort::Bool
    } else {
        todo!("cannot resolve sort")
    }
}

struct Sorts {
    int: Symbol,
}

static SORTS: std::lazy::SyncLazy<Sorts> =
    std::lazy::SyncLazy::new(|| Sorts { int: Symbol::intern("int") });

mod errors {
    // use crate::surface;
    use rustc_macros::SessionDiagnostic;
    use rustc_span::{symbol::Ident, Span};

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedVar {
        #[message = "cannot find value `{var}` in this scope"]
        #[label = "not found in this scope"]
        pub span: Span,
        pub var: Ident,
    }

    impl UnresolvedVar {
        pub fn new(var: Ident) -> Self {
            Self { span: var.span, var }
        }
    }
}
