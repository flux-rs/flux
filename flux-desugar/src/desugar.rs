use std::iter;

use flux_common::{index::IndexGen, iter::IterExt};
use flux_errors::FluxSession;
use flux_middle::{
    core::{
        AdtSortsMap, BaseTy, BinOp, Constraint, EnumDef, Expr, ExprKind, FnSig, Ident, Index,
        Indices, Lit, Name, Param, Qualifier, RefKind, Sort, StructDef, StructKind, Ty, VariantDef,
    },
    global_env::ConstInfo,
};
use flux_syntax::surface::{self, Path, Res};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::{sym, symbol::kw, Symbol};

pub fn desugar_qualifier(
    sess: &FluxSession,
    consts: &[ConstInfo],
    qualifier: surface::Qualifier,
) -> Result<Qualifier, ErrorGuaranteed> {
    let mut params = ParamsCtxt::new(sess, consts);
    params.insert_params(qualifier.args)?;
    let name = qualifier.name.name.to_ident_string();
    let expr = params.desugar_expr(qualifier.expr);

    Ok(Qualifier { name, args: params.params, expr: expr? })
}

pub fn resolve_sorts(
    sess: &FluxSession,
    params: &surface::Params,
) -> Result<Vec<Sort>, ErrorGuaranteed> {
    params
        .params
        .iter()
        .map(|param| resolve_sort(sess, param.sort))
        .try_collect_exhaust()
}

pub fn desugar_struct_def(
    sess: &FluxSession,
    consts: &[ConstInfo],
    adt_def: surface::StructDef<Res>,
) -> Result<StructDef, ErrorGuaranteed> {
    let def_id = adt_def.def_id.to_def_id();
    let mut params = ParamsCtxt::new(sess, consts);
    params.insert_params(adt_def.refined_by.into_iter().flatten())?;

    let mut cx = DesugarCtxt::with_params(params);

    let kind = if adt_def.opaque {
        StructKind::Opaque
    } else {
        let fields = adt_def
            .fields
            .into_iter()
            .map(|ty| ty.map(|ty| cx.desugar_ty(ty)).transpose())
            .try_collect_exhaust()?;
        StructKind::Transparent { fields }
    };
    let refined_by = cx.params.params;
    Ok(StructDef { def_id, kind, refined_by })
}

pub fn desugar_enum_def(
    sess: &FluxSession,
    consts: &[ConstInfo],
    adt_sorts: &impl AdtSortsMap,
    enum_def: surface::EnumDef<Res>,
) -> Result<EnumDef, ErrorGuaranteed> {
    let mut params = ParamsCtxt::new(sess, consts);
    params.insert_params(enum_def.refined_by.into_iter().flatten())?;
    let def_id = enum_def.def_id.to_def_id();
    let refined_by = params.params;
    let variants = enum_def
        .variants
        .into_iter()
        .map(|variant| desugar_variant(sess, adt_sorts, consts, variant))
        .try_collect_exhaust()?;

    Ok(EnumDef { def_id, refined_by, variants })
}

fn desugar_variant(
    sess: &FluxSession,
    adt_sorts: &impl AdtSortsMap,
    consts: &[ConstInfo],
    variant: surface::VariantDef<Res>,
) -> Result<VariantDef, ErrorGuaranteed> {
    let mut params = ParamsCtxt::new(sess, consts);
    for ty in &variant.fields {
        params.ty_gather_params(ty, adt_sorts)?;
    }
    let mut desugar = DesugarCtxt::with_params(params);

    let fields = variant
        .fields
        .into_iter()
        .map(|ty| desugar.desugar_ty(ty))
        .try_collect_exhaust()?;

    let ret = desugar.desugar_ty(variant.ret)?;

    Ok(VariantDef { params: desugar.params.params, fields, ret })
}

pub fn desugar_fn_sig(
    sess: &FluxSession,
    refined_by: &impl AdtSortsMap,
    consts: &[ConstInfo],
    fn_sig: surface::FnSig<Res>,
) -> Result<FnSig, ErrorGuaranteed> {
    let mut params = ParamsCtxt::new(sess, consts);
    params.gather_fn_sig_params(&fn_sig, refined_by)?;
    let mut desugar = DesugarCtxt::with_params(params);

    if let Some(e) = fn_sig.requires {
        let e = desugar.params.desugar_expr(e)?;
        desugar.requires.push(Constraint::Pred(e));
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
            Ok(Constraint::Type(loc?, ty?))
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

pub struct DesugarCtxt<'a> {
    params: ParamsCtxt<'a>,
    requires: Vec<Constraint>,
}

struct ParamsCtxt<'a> {
    sess: &'a FluxSession,
    name_gen: IndexGen<Name>,
    name_map: FxHashMap<Symbol, Name>,
    field_map: FxHashMap<(Symbol, Symbol), Name>,
    dot_map: FxHashMap<Symbol, Vec<Name>>,
    const_map: FxHashMap<Symbol, DefId>,
    params: Vec<Param>,
}

impl<'a> DesugarCtxt<'a> {
    fn with_params(params: ParamsCtxt) -> DesugarCtxt {
        DesugarCtxt { params, requires: vec![] }
    }

    fn desugar_arg(&mut self, arg: surface::Arg<Res>) -> Result<Ty, ErrorGuaranteed> {
        match arg {
            surface::Arg::Indexed(bind, path, pred) => {
                if let Some(pred) = pred {
                    self.requires
                        .push(Constraint::Pred(self.params.desugar_expr(pred)?));
                }
                let bty = self.desugar_path_into_bty(path);

                let indices = Indices { indices: self.desugar_bind(bind)?, span: bind.span };
                // let idx = Index { expr: self.params.desugar_var(bind)?, is_binder: true };
                // let indices = Indices { indices: vec![idx], span: bind.span };

                Ok(Ty::Indexed(bty?, indices))
            }
            surface::Arg::StrgRef(loc, ty) => {
                let loc = self.params.desugar_ident(loc)?;
                let ty = self.desugar_ty(ty)?;
                self.requires.push(Constraint::Type(loc, ty));
                Ok(Ty::Ptr(loc))
            }
            surface::Arg::Ty(ty) => self.desugar_ty(ty),
            surface::Arg::Alias(..) => panic!("Unexpected-Alias in desugar!"),
        }
    }

    fn desugar_ty(&mut self, ty: surface::Ty<Res>) -> Result<Ty, ErrorGuaranteed> {
        let ty = match ty.kind {
            surface::TyKind::Path(surface::Path { ident: Res::Float(float_ty), .. }) => {
                Ty::Float(float_ty)
            }
            surface::TyKind::Path(surface::Path { ident: Res::Param(param_ty), .. }) => {
                Ty::Param(param_ty)
            }
            surface::TyKind::Path(path) => {
                let bty = self.desugar_path_into_bty(path)?;
                Ty::BaseTy(bty)
            }
            surface::TyKind::Indexed { path, indices } => {
                let bty = self.desugar_path_into_bty(path);
                let indices = self.desugar_indices(indices);
                Ty::Indexed(bty?, indices?)
            }
            surface::TyKind::Exists { bind, path, pred } => {
                let bty = self.desugar_path_into_bty(path);

                let fresh = self.params.fresh();
                let pred = self
                    .params
                    .with_name_map(bind.name, fresh, |params| params.desugar_expr(pred));

                let binders = vec![Ident { name: fresh, source_info: (bind.span, bind.name) }];
                Ty::Exists(bty?, binders, pred?)
            }
            surface::TyKind::Ref(rk, ty) => {
                Ty::Ref(desugar_ref_kind(rk), Box::new(self.desugar_ty(*ty)?))
            }
            surface::TyKind::StrgRef(loc, ty) => {
                let loc = self.params.desugar_ident(loc)?;
                let ty = self.desugar_ty(*ty)?;
                self.requires.push(Constraint::Type(loc, ty));
                Ty::Ptr(loc)
            }
            surface::TyKind::Unit => Ty::Tuple(vec![]),
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.params.desugar_expr(pred)?;
                let ty = self.desugar_ty(*ty)?;
                Ty::Constr(pred, Box::new(ty))
            }
            surface::TyKind::Array(ty, len) => {
                let span = len.span;
                let Lit::Int(len) = self.params.desugar_lit(len)? else {
                    return Err(self.params.sess.emit_err(errors::InvalidArrayLen { span }))
                };
                let len: usize = len
                    .try_into()
                    .map_err(|_| self.params.sess.emit_err(errors::InvalidArrayLen { span }))?;

                let ty = self.desugar_ty(*ty)?;
                Ty::Array(Box::new(ty), len)
            }
        };
        Ok(ty)
    }

    fn desugar_indices(&self, indices: surface::Indices) -> Result<Indices, ErrorGuaranteed> {
        let mut exprs = vec![];
        for idx in indices.indices {
            let idxs = self.desugar_index(idx)?;
            for e in idxs {
                exprs.push(e)
            }
        }
        Ok(Indices { indices: exprs, span: indices.span })
    }

    fn desugar_bind(
        &self,
        ident: rustc_span::symbol::Ident,
    ) -> Result<Vec<Index>, ErrorGuaranteed> {
        match self.params.dot_map.get(&ident.name) {
            Some(names) => {
                let indices = names
                    .iter()
                    .map(|name| {
                        let kind = ExprKind::Var(*name, ident.name, ident.span);
                        Index { expr: Expr { kind, span: Some(ident.span) }, is_binder: true }
                    })
                    .collect();
                Ok(indices)
            }

            None => Ok(vec![Index { expr: self.params.desugar_var(ident)?, is_binder: true }]),
        }
    }

    fn desugar_index(&self, idx: surface::Index) -> Result<Vec<Index>, ErrorGuaranteed> {
        match idx {
            surface::Index::Bind(ident) => self.desugar_bind(ident),
            surface::Index::Expr(expr) => {
                Ok(vec![Index { expr: self.params.desugar_expr(expr)?, is_binder: false }])
            }
        }
    }

    fn desugar_path_into_bty(
        &mut self,
        path: surface::Path<Res>,
    ) -> Result<BaseTy, ErrorGuaranteed> {
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

fn desugar_ref_kind(rk: surface::RefKind) -> RefKind {
    match rk {
        surface::RefKind::Mut => RefKind::Mut,
        surface::RefKind::Shr => RefKind::Shr,
    }
}

fn resolve_sort(sess: &FluxSession, sort: surface::Ident) -> Result<Sort, ErrorGuaranteed> {
    if sort.name == SORTS.int {
        Ok(Sort::Int)
    } else if sort.name == sym::bool {
        Ok(Sort::Bool)
    } else {
        Err(sess.emit_err(errors::UnresolvedSort::new(sort)))
    }
}

impl ParamsCtxt<'_> {
    fn new<'a>(sess: &'a FluxSession, consts: &[ConstInfo]) -> ParamsCtxt<'a> {
        let const_map: FxHashMap<Symbol, DefId> = consts
            .iter()
            .map(|const_info| (const_info.sym, const_info.def_id))
            .collect();
        ParamsCtxt {
            sess,
            name_gen: IndexGen::new(),
            name_map: FxHashMap::default(),
            dot_map: FxHashMap::default(),
            field_map: FxHashMap::default(),
            params: vec![],
            const_map,
        }
    }

    fn desugar_expr(&self, expr: surface::Expr) -> Result<Expr, ErrorGuaranteed> {
        let kind = match expr.kind {
            surface::ExprKind::Var(ident) => return self.desugar_var(ident),
            surface::ExprKind::Literal(lit) => ExprKind::Literal(self.desugar_lit(lit)?),
            surface::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.desugar_expr(*e1);
                let e2 = self.desugar_expr(*e2);
                ExprKind::BinaryOp(desugar_bin_op(op), Box::new(e1?), Box::new(e2?))
            }
            surface::ExprKind::Dot(e, fld) => return self.desugar_dot(*e, fld),
        };
        Ok(Expr { kind, span: Some(expr.span) })
    }

    fn fresh(&self) -> Name {
        self.name_gen.fresh()
    }

    fn with_name_map<R>(&mut self, symb: Symbol, name: Name, f: impl FnOnce(&mut Self) -> R) -> R {
        let old = self.name_map.insert(symb, name);
        let r = f(self);
        if let Some(old) = old {
            self.name_map.insert(symb, old);
        } else {
            self.name_map.remove(&symb);
        }
        r
    }

    fn desugar_lit(&self, lit: surface::Lit) -> Result<Lit, ErrorGuaranteed> {
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

    fn desugar_var(&self, ident: surface::Ident) -> Result<Expr, ErrorGuaranteed> {
        if let Some(&name) = self.name_map.get(&ident.name) {
            let kind = ExprKind::Var(name, ident.name, ident.span);
            return Ok(Expr { kind, span: Some(ident.span) });
        }
        if let Some(&did) = self.const_map.get(&ident.name) {
            let kind = ExprKind::Const(did, ident.span);
            return Ok(Expr { kind, span: Some(ident.span) });
        }
        // let dn = &self.dot_map;
        // panic!("TRACE: {ident:?} {dn:?}");
        Err(self.sess.emit_err(errors::UnresolvedVar::new(ident)))
    }

    fn desugar_dot(
        &self,
        expr: surface::Expr,
        fld: surface::Ident,
    ) -> Result<Expr, ErrorGuaranteed> {
        if let surface::ExprKind::Var(ident) = expr.kind {
            if let Some(&name) = self.field_map.get(&(ident.name, fld.name)) {
                let kind = ExprKind::Var(name, ident.name, ident.span);
                return Ok(Expr { kind, span: Some(ident.span) });
            }
            return Err(self
                .sess
                .emit_err(errors::UnresolvedDotField::new(ident, fld)));
        }
        Err(self
            .sess
            .emit_err(errors::InvalidDotVar { span: expr.span }))
    }

    fn desugar_ident(&self, ident: surface::Ident) -> Result<Ident, ErrorGuaranteed> {
        if let Some(&name) = self.name_map.get(&ident.name) {
            let source_info = (ident.span, ident.name);
            Ok(Ident { name, source_info })
        } else {
            Err(self.sess.emit_err(errors::UnresolvedVar::new(ident)))
        }
    }

    fn push_dot_param(
        &mut self,
        ident: surface::Ident,
        fld: Symbol,
        sort: Sort,
    ) -> Result<Name, ErrorGuaranteed> {
        let fresh = self.name_gen.fresh();
        let source_info = (ident.span, ident.name);
        if self.field_map.insert((ident.name, fld), fresh).is_some() {
            return Err(self.sess.emit_err(errors::DuplicateParam::new(ident)));
        };
        self.params
            .push(Param { name: Ident { name: fresh, source_info }, sort });
        Ok(fresh)
    }

    fn push_param(&mut self, ident: surface::Ident, sort: Sort) -> Result<(), ErrorGuaranteed> {
        let fresh = self.name_gen.fresh();
        let source_info = (ident.span, ident.name);

        if self.name_map.insert(ident.name, fresh).is_some() {
            return Err(self.sess.emit_err(errors::DuplicateParam::new(ident)));
        };
        self.params
            .push(Param { name: Ident { name: fresh, source_info }, sort });

        Ok(())
    }

    fn push_bind(
        &mut self,
        ident: surface::Ident,
        path: &Path<Res>,
        adt_sorts: &impl AdtSortsMap,
    ) -> Result<(), ErrorGuaranteed> {
        let sorts = self.sorts(path, adt_sorts)?;
        let slen = sorts.len();
        // TODO error message
        assert!(slen >= 1);
        if slen == 1 {
            self.push_param(ident, sorts[0])?;
        } else if slen > 1 {
            let fields = self.fields(path, adt_sorts)?;
            // TODO error message
            assert_eq!(slen, fields.len());
            let mut fresh_names = vec![];
            for (fld, sort) in iter::zip(fields, sorts) {
                let fld_name = self.push_dot_param(ident, *fld, *sort)?;
                fresh_names.push(fld_name);
            }
            if self.dot_map.insert(ident.name, fresh_names).is_some() {
                return Err(self.sess.emit_err(errors::DuplicateParam::new(ident)));
            };
        }
        Ok(())
    }

    fn insert_params(
        &mut self,
        params: impl IntoIterator<Item = surface::Param>,
    ) -> Result<(), ErrorGuaranteed> {
        for param in params {
            self.push_param(param.name, resolve_sort(self.sess, param.sort)?)?;
        }
        Ok(())
    }

    fn gather_fn_sig_params(
        &mut self,
        fn_sig: &surface::FnSig<Res>,
        adt_sorts: &impl AdtSortsMap,
    ) -> Result<(), ErrorGuaranteed> {
        for arg in &fn_sig.args {
            self.arg_gather_params(arg, adt_sorts)?;
        }
        Ok(())
    }

    fn arg_gather_params(
        &mut self,
        arg: &surface::Arg<Res>,
        adt_sorts: &impl AdtSortsMap,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            surface::Arg::Indexed(bind, path, _) => {
                self.push_bind(*bind, path, adt_sorts)?;
            }
            surface::Arg::StrgRef(loc, ty) => {
                self.push_param(*loc, Sort::Loc)?;
                self.ty_gather_params(ty, adt_sorts)?;
            }
            surface::Arg::Ty(ty) => self.ty_gather_params(ty, adt_sorts)?,
            surface::Arg::Alias(..) => panic!("alias are not allowed after expansion"),
        }
        Ok(())
    }

    fn single_bind(indices: &Vec<surface::Index>) -> Option<surface::Ident> {
        if indices.len() == 1 {
            if let surface::Index::Bind(ident) = indices[0] {
                return Some(ident);
            }
        }
        return None;
    }

    fn ty_gather_params(
        &mut self,
        ty: &surface::Ty<Res>,
        adt_sorts: &impl AdtSortsMap,
    ) -> Result<(), ErrorGuaranteed> {
        match &ty.kind {
            surface::TyKind::Indexed { path, indices } => {
                if let Some(ident) = ParamsCtxt::single_bind(&indices.indices) {
                    self.push_bind(ident, path, adt_sorts)?;
                } else {
                    let sorts = self.sorts(path, adt_sorts)?;
                    assert_eq!(indices.indices.len(), sorts.len());
                    for (index, sort) in iter::zip(&indices.indices, sorts) {
                        if let surface::Index::Bind(bind) = index {
                            self.push_param(*bind, *sort)?;
                        }
                    }
                }
                Ok(())
            }
            surface::TyKind::StrgRef(_, ty)
            | surface::TyKind::Ref(_, ty)
            | surface::TyKind::Array(ty, _) => self.ty_gather_params(ty, adt_sorts),
            surface::TyKind::Constr(_, ty) => self.ty_gather_params(ty, adt_sorts),
            surface::TyKind::Path(path) => {
                for ty in &path.args {
                    self.ty_gather_params(ty, adt_sorts)?;
                }
                Ok(())
            }
            surface::TyKind::Exists { .. } | surface::TyKind::Unit => Ok(()),
        }
    }

    fn fields<'a>(
        &self,
        path: &surface::Path<Res>,
        adt_sorts: &'a impl AdtSortsMap,
    ) -> Result<&'a [Symbol], ErrorGuaranteed> {
        match path.ident {
            Res::Adt(def_id) => Ok(adt_sorts.get_fields(def_id).unwrap_or(&[])),
            _ => Ok(&[]),
        }
    }

    fn sorts<'a>(
        &self,
        path: &surface::Path<Res>,
        adt_sorts: &'a impl AdtSortsMap,
    ) -> Result<&'a [Sort], ErrorGuaranteed> {
        match path.ident {
            Res::Bool => Ok(&[Sort::Bool]),
            Res::Int(_) | Res::Uint(_) => Ok(&[Sort::Int]),
            Res::Adt(def_id) => Ok(adt_sorts.get_sorts(def_id).unwrap_or(&[])),
            Res::Float(_) => Err(self.sess.emit_err(errors::RefinedFloat { span: path.span })),
            Res::Param(_) => {
                Err(self
                    .sess
                    .emit_err(errors::RefinedTypeParam { span: path.span }))
            }
        }
    }
}

fn desugar_bin_op(op: surface::BinOp) -> BinOp {
    match op {
        surface::BinOp::Iff => BinOp::Iff,
        surface::BinOp::Imp => BinOp::Imp,
        surface::BinOp::Or => BinOp::Or,
        surface::BinOp::And => BinOp::And,
        surface::BinOp::Eq => BinOp::Eq,
        surface::BinOp::Gt => BinOp::Gt,
        surface::BinOp::Ge => BinOp::Ge,
        surface::BinOp::Lt => BinOp::Lt,
        surface::BinOp::Le => BinOp::Le,
        surface::BinOp::Add => BinOp::Add,
        surface::BinOp::Sub => BinOp::Sub,
        surface::BinOp::Mod => BinOp::Mod,
        surface::BinOp::Mul => BinOp::Mul,
    }
}

struct Sorts {
    int: Symbol,
}

static SORTS: std::sync::LazyLock<Sorts> =
    std::sync::LazyLock::new(|| Sorts { int: Symbol::intern("int") });

mod errors {
    use flux_macros::SessionDiagnostic;
    use rustc_span::{symbol::Ident, Span};

    #[derive(SessionDiagnostic)]
    #[error(desugar::unresolved_var, code = "FLUX")]
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

    #[derive(SessionDiagnostic)]
    #[error(desugar::duplicate_param, code = "FLUX")]
    pub struct DuplicateParam {
        #[primary_span]
        #[label]
        span: Span,
        name: Ident,
    }

    impl DuplicateParam {
        pub fn new(name: Ident) -> Self {
            Self { span: name.span, name }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error(desugar::unresolved_sort, code = "FLUX")]
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

    #[derive(SessionDiagnostic)]
    #[error(desugar::int_too_large, code = "FLUX")]
    pub struct IntTooLarge {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(desugar::unexpected_literal, code = "FLUX")]
    pub struct UnexpectedLiteral {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(desugar::refined_type_param, code = "FLUX")]
    pub struct RefinedTypeParam {
        #[primary_span]
        #[label]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(desugar::refined_float, code = "FLUX")]
    pub struct RefinedFloat {
        #[primary_span]
        #[label]
        pub span: Span,
    }

    // TODO(nilehmann) this probably should be part of the code that checks
    // if a flux signature is a valid refinement of a rust signature
    #[derive(SessionDiagnostic)]
    #[error(desugar::invalid_array_len, code = "FLUX")]
    pub struct InvalidArrayLen {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(desugar::invalid_dot_var, code = "FLUX")]
    pub struct InvalidDotVar {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(desugar::unresolved_dot_field, code = "FLUX")]
    pub struct UnresolvedDotField {
        #[primary_span]
        pub span: Span,
        ident: Ident,
        field: Ident,
    }
    impl UnresolvedDotField {
        pub fn new(ident: Ident, field: Ident) -> Self {
            Self { span: ident.span, ident, field }
        }
    }
}
