use std::iter;

use liquid_rust_common::{index::IndexGen, iter::IterExt};
use liquid_rust_syntax::surface::{self, Res};
use rustc_errors::ErrorReported;
use rustc_hash::FxHashMap;
use rustc_session::Session;
use rustc_span::{sym, symbol::kw, Symbol};

use crate::ty::{
    AdtDef, AdtSortsMap, BaseTy, Constr, Expr, ExprKind, FnSig, Ident, Indices, Lit, Name, Param,
    Pred, Qualifier, Sort, Ty, Var,
};

pub fn desugar_qualifier(
    sess: &Session,
    qualifier: surface::Qualifier,
) -> Result<Qualifier, ErrorReported> {
    let mut params = ParamsCtxt::new(sess);
    params.insert_params(qualifier.args)?;
    let name = qualifier.name.name.to_ident_string();
    let expr = params.desugar_expr(qualifier.expr, None);

    Ok(Qualifier { name, args: params.params, expr: expr? })
}

pub fn resolve_sorts(sess: &Session, params: &surface::Params) -> Result<Vec<Sort>, ErrorReported> {
    params
        .params
        .iter()
        .map(|param| resolve_sort(sess, param.sort))
        .try_collect_exhaust()
}

pub fn desugar_struct_def(
    sess: &Session,
    adt_def: surface::StructDef<Res>,
) -> Result<AdtDef, ErrorReported> {
    let mut params = ParamsCtxt::new(sess);
    params.insert_params(adt_def.refined_by.into_iter().flatten())?;

    let mut cx = DesugarCtxt::with_params(params);

    if adt_def.opaque {
        Ok(AdtDef::Opaque { refined_by: cx.params.params })
    } else {
        let fields = adt_def
            .fields
            .into_iter()
            .map(|ty| cx.desugar_ty(ty.unwrap()))
            .try_collect_exhaust()?;
        Ok(AdtDef::Transparent { refined_by: cx.params.params, fields })
    }
}

pub fn desugar_enum_def(
    sess: &Session,
    adt_def: surface::EnumDef,
) -> Result<AdtDef, ErrorReported> {
    let mut params = ParamsCtxt::new(sess);
    params.insert_params(adt_def.refined_by.into_iter().flatten())?;

    if adt_def.opaque {
        Ok(AdtDef::Opaque { refined_by: params.params })
    } else {
        panic!("transparent enums are not supported yet")
    }
}

pub fn desugar_fn_sig(
    sess: &Session,
    refined_by: &impl AdtSortsMap,
    fn_sig: surface::FnSig<Res>,
) -> Result<FnSig, ErrorReported> {
    let mut params = ParamsCtxt::new(sess);
    params.gather_fn_sig_params(&fn_sig, refined_by)?;

    let mut desugar = DesugarCtxt::with_params(params);

    if let Some(e) = fn_sig.requires {
        let e = desugar.params.desugar_expr(e, None)?;
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
            let loc = desugar.params.desugar_ident(bind);
            let ty = desugar.desugar_ty(ty);
            Ok(Constr::Type(loc?, ty?))
        })
        .try_collect_exhaust();

    Ok(FnSig {
        params: desugar.params.params,
        requires: desugar.requires,
        args: args?,
        ret: ret?,
        ensures: ensures?,
    })
}

struct DesugarCtxt<'a> {
    params: ParamsCtxt<'a>,
    requires: Vec<Constr>,
}

struct ParamsCtxt<'a> {
    sess: &'a Session,
    name_gen: IndexGen<Name>,
    map: FxHashMap<Symbol, Name>,
    params: Vec<Param>,
}

impl<'a> DesugarCtxt<'a> {
    fn with_params(params: ParamsCtxt) -> DesugarCtxt {
        DesugarCtxt { params, requires: vec![] }
    }

    fn desugar_arg(&mut self, arg: surface::Arg<Res>) -> Result<Ty, ErrorReported> {
        match arg {
            surface::Arg::Indexed(bind, path, pred) => {
                if let Some(pred) = pred {
                    self.requires
                        .push(Constr::Pred(self.params.desugar_expr(pred, None)?));
                }
                let bty = self.desugar_path_into_bty(path);
                let var = self.params.desugar_var(bind, None)?;
                let indices = Indices { exprs: vec![var], span: bind.span };
                Ok(Ty::Indexed(bty?, indices))
            }
            surface::Arg::StrgRef(loc, ty) => {
                let loc = self.params.desugar_ident(loc)?;
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
                let pred = self.params.desugar_expr(pred, Some(bind.name));
                Ty::Exists(bty?, Pred::Expr(pred?))
            }
            surface::TyKind::Ref(rk, ty) => Ty::Ref(rk, Box::new(self.desugar_ty(*ty)?)),
            surface::TyKind::StrgRef(loc, ty) => {
                let loc = self.params.desugar_ident(loc)?;
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
                    surface::Index::Bind(ident) => self.params.desugar_var(ident, None),
                    surface::Index::Expr(expr) => self.params.desugar_expr(expr, None),
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
}

fn resolve_sort(sess: &Session, sort: surface::Ident) -> Result<Sort, ErrorReported> {
    if sort.name == SORTS.int {
        Ok(Sort::Int)
    } else if sort.name == sym::bool {
        Ok(Sort::Bool)
    } else {
        Err(sess.emit_err(errors::UnresolvedSort::new(sort)))
    }
}

impl ParamsCtxt<'_> {
    fn new(sess: &Session) -> ParamsCtxt {
        ParamsCtxt { sess, name_gen: IndexGen::new(), map: FxHashMap::default(), params: vec![] }
    }

    fn desugar_expr(
        &self,
        expr: surface::Expr,
        bound: Option<Symbol>,
    ) -> Result<Expr, ErrorReported> {
        let kind = match expr.kind {
            surface::ExprKind::Var(ident) => return self.desugar_var(ident, bound),
            surface::ExprKind::Literal(lit) => ExprKind::Literal(self.desugar_lit(lit)?),
            surface::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.desugar_expr(*e1, bound);
                let e2 = self.desugar_expr(*e2, bound);
                ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
            }
        };
        Ok(Expr { kind, span: Some(expr.span) })
    }

    fn desugar_lit(&self, lit: surface::Lit) -> Result<Lit, ErrorReported> {
        match lit.kind {
            surface::LitKind::Integer => {
                match lit.symbol.as_str().parse::<i128>() {
                    Ok(n) => Ok(Lit::Int(n)),
                    Err(_) => Err(self.sess.emit_err(errors::IntTooLarge { span: lit.span })),
                }
            }
            surface::LitKind::Bool => Ok(Lit::Bool(lit.symbol == kw::True)),
            _ => {
                Err(self
                    .sess
                    .emit_err(errors::UnexpectedLiteral { span: lit.span }))
            }
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

    fn desugar_ident(&self, ident: surface::Ident) -> Result<Ident, ErrorReported> {
        if let Some(&name) = self.map.get(&ident.name) {
            let source_info = (ident.span, ident.name);
            Ok(Ident { name, source_info })
        } else {
            Err(self.sess.emit_err(errors::UnresolvedVar::new(ident)))
        }
    }

    fn push_param(&mut self, ident: surface::Ident, sort: Sort) -> Result<(), ErrorReported> {
        let fresh = self.name_gen.fresh();
        let source_info = (ident.span, ident.name);

        if self.map.insert(ident.name, fresh).is_some() {
            return Err(self.sess.emit_err(errors::DuplicateParam::new(ident)));
        };
        self.params
            .push(Param { name: Ident { name: fresh, source_info }, sort });

        Ok(())
    }

    fn insert_params(
        &mut self,
        params: impl IntoIterator<Item = surface::Param>,
    ) -> Result<(), ErrorReported> {
        for param in params {
            self.push_param(param.name, resolve_sort(self.sess, param.sort)?)?;
        }
        Ok(())
    }

    fn gather_fn_sig_params(
        &mut self,
        fn_sig: &surface::FnSig<Res>,
        adt_sorts: &impl AdtSortsMap,
    ) -> Result<(), ErrorReported> {
        for arg in &fn_sig.args {
            self.arg_gather_params(arg, adt_sorts)?;
        }
        Ok(())
    }

    fn arg_gather_params(
        &mut self,
        arg: &surface::Arg<Res>,
        adt_sorts: &impl AdtSortsMap,
    ) -> Result<(), ErrorReported> {
        match arg {
            surface::Arg::Indexed(bind, path, _) => {
                let sorts = self.sorts(path, adt_sorts)?;
                assert_eq!(sorts.len(), 1);
                self.push_param(*bind, sorts[0])?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.push_param(*loc, Sort::Loc)?;
                self.ty_gather_params(ty, adt_sorts)?;
            }
            surface::Arg::Ty(ty) => self.ty_gather_params(ty, adt_sorts)?,
        }
        Ok(())
    }

    fn ty_gather_params(
        &mut self,
        ty: &surface::Ty<Res>,
        adt_sorts: &impl AdtSortsMap,
    ) -> Result<(), ErrorReported> {
        match &ty.kind {
            surface::TyKind::Indexed { path, indices } => {
                let sorts = self.sorts(path, adt_sorts)?;
                assert_eq!(indices.indices.len(), sorts.len());
                for (index, sort) in iter::zip(&indices.indices, sorts) {
                    if let surface::Index::Bind(bind) = index {
                        self.push_param(*bind, *sort)?;
                    }
                }
                Ok(())
            }
            surface::TyKind::StrgRef(_, ty) | surface::TyKind::Ref(_, ty) => {
                self.ty_gather_params(ty, adt_sorts)
            }
            surface::TyKind::Path(_) | surface::TyKind::Exists { .. } => Ok(()),
        }
    }

    fn sorts<'a>(
        &self,
        path: &surface::Path<Res>,
        adt_sorts: &'a impl AdtSortsMap,
    ) -> Result<&'a [Sort], ErrorReported> {
        match path.ident {
            Res::Bool => Ok(&[Sort::Bool]),
            Res::Int(_) => Ok(&[Sort::Int]),
            Res::Uint(_) => Ok(&[Sort::Int]),
            Res::Adt(def_id) => Ok(adt_sorts.get(def_id).unwrap_or(&[])),
            Res::Float(_) => Err(self.sess.emit_err(errors::RefinedFloat { span: path.span })),
            Res::Param(_) => {
                Err(self
                    .sess
                    .emit_err(errors::RefinedTypeParam { span: path.span }))
            }
        }
    }
}

struct Sorts {
    int: Symbol,
}

static SORTS: std::lazy::SyncLazy<Sorts> =
    std::lazy::SyncLazy::new(|| Sorts { int: Symbol::intern("int") });

mod errors {
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

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DuplicateParam {
        #[message = "the name `{name}` is already used as a parameter"]
        #[label = "already used"]
        span: Span,
        name: Ident,
    }

    impl DuplicateParam {
        pub fn new(name: Ident) -> Self {
            Self { span: name.span, name }
        }
    }
    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnresolvedSort {
        #[message = "cannot find sort `{sort}` in this scope"]
        #[label = "not found in this scope"]
        pub span: Span,
        pub sort: Ident,
    }

    impl UnresolvedSort {
        pub fn new(sort: Ident) -> Self {
            Self { span: sort.span, sort }
        }
    }
    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct IntTooLarge {
        #[message = "integer literal is too large"]
        pub span: Span,
    }
    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct UnexpectedLiteral {
        #[message = "unexpected literal"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RefinedTypeParam {
        #[message = "type parameters cannot be refined"]
        #[label = "refined type parameter"]
        pub span: Span,
    }
    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct RefinedFloat {
        #[message = "float cannot be refined"]
        #[label = "refined float"]
        pub span: Span,
    }
}
