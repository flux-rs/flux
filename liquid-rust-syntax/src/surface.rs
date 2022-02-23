pub use rustc_ast::token::LitKind;
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ast::{self, Expr, GenericParam};

#[derive(Debug)]
pub struct FnSig {
    /// example: `l: i32@n`
    pub requires: Vec<(Ident, Ty)>,
    /// example `i32{v:v >= 0}`
    pub returns: Ty,
    /// example: `*x: i32{v:v = n+1}`
    pub ensures: Vec<(Ident, Ty)>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind {
    /// ty
    Base(Path),

    /// ty{b:e}
    Exists { bind: Ident, path: Path, pred: Expr },

    /// ty{e}, the param binder is used e.g. x: i32{0 < x}
    AnonEx { path: Path, pred: Expr },

    /// named: n@t
    Named(Ident, Box<Ty>),

    /// reference
    Ref(RefKind, Box<Ty>),
}

#[derive(Debug)]
pub struct Path {
    /// vec
    pub ident: Ident,
    /// <nat>
    pub args: Option<Vec<Ty>>,
    pub span: Span,
}

#[derive(Debug)]
pub enum RefKind {
    Mut,
    Immut,
}

struct Desugar {
    generics: Vec<ast::GenericParam>,
    args: Vec<ast::Ty>,
    reqs: Vec<(Ident, ast::Ty)>,
}

/// A `BindIn` is the information obtained from a single input-param binding
struct BindIn {
    gen: Option<GenericParam>,
    ty: ast::Ty,
    loc: Option<(Ident, ast::Ty)>,
}

fn convert_path(p: Path) -> ast::Path {
    ast::Path {
        ident: p.ident,
        span: p.span,
        args: p.args.map(|ts| ts.into_iter().map(convert_ty).collect()),
    }
}

fn convert_tykind(t: TyKind) -> ast::TyKind {
    match t {
        TyKind::Base(p) => ast::TyKind::BaseTy(convert_path(p)),
        TyKind::Exists { bind, path, pred } => {
            ast::TyKind::Exists { bind, path: convert_path(path), pred }
        }
        TyKind::AnonEx { .. } => {
            panic!("Unexpected input in convert_tykind!")
        }
        TyKind::Named(_, t) => {
            let ty = convert_ty(*t);
            ty.kind
        }
        TyKind::Ref(_, t) => ast::TyKind::WeakRef(Box::new(convert_ty(*t))),
    }
}

fn convert_ty(t: Ty) -> ast::Ty {
    ast::Ty { kind: convert_tykind(t.kind), span: t.span }
}

fn is_bool(path: &Path) -> bool {
    path.ident.as_str() == "bool"
}

// HACK(ranjitjhala) need better way to "embed" rust types to sort
fn mk_sort(path: &Path, span: Span) -> Ident {
    let sort_name = if is_bool(path) { "bool" } else { "int" };
    Ident { name: rustc_span::Symbol::intern(sort_name), span }
}

fn mk_singleton(x: Ident) -> ast::Refine {
    let e = Expr { kind: ast::ExprKind::Var(x), span: x.span };
    ast::Refine { exprs: vec![e], span: x.span }
}

fn mk_generic(x: Ident, path: &Path, pred: Option<Expr>) -> ast::GenericParam {
    ast::GenericParam { name: x, sort: mk_sort(path, x.span), pred }
}

impl BindIn {
    fn from_path(x: Ident, path: Path, span: Span, pred: Option<Expr>) -> BindIn {
        let gen = Some(mk_generic(x, &path, pred));
        let path = convert_path(path);
        let refine = mk_singleton(x);
        let kind = ast::TyKind::RefineTy { path, refine };
        let ty = ast::Ty { kind, span };
        BindIn { gen, ty, loc: None }
    }

    fn from_ty(x: Ident, ty: Ty) -> BindIn {
        match ty.kind {
            TyKind::AnonEx { path, pred } => BindIn::from_path(x, path, ty.span, Some(pred)),
            TyKind::Base(path) => BindIn::from_path(x, path, ty.span, None),
            TyKind::Exists { bind, path, pred } => {
                let path = convert_path(path);
                let kind = ast::TyKind::Exists { bind, path, pred };
                let ty = ast::Ty { kind, span: ty.span };
                BindIn { gen: None, ty, loc: None }
            }
            TyKind::Named(n, t) => BindIn::from_ty(n, *t),
            TyKind::Ref(RefKind::Mut, t) => {
                let b = BindIn::from_ty(x, *t);
                let ty = ast::Ty { kind: ast::TyKind::StrgRef(x), span: ty.span };
                BindIn { gen: b.gen, ty, loc: Some((x, b.ty)) }
            }
            TyKind::Ref(RefKind::Immut, t) => {
                let b = BindIn::from_ty(x, *t);
                let ty = ast::Ty { kind: ast::TyKind::ShrRef(Box::new(b.ty)), span: ty.span };
                BindIn { gen: b.gen, ty, loc: None }
            }
        }
    }
}

impl Desugar {
    fn desugar_inputs(&mut self, in_sigs: Vec<(Ident, Ty)>) {
        for (x, ty) in in_sigs {
            let b_in = BindIn::from_ty(x, ty);
            if let Some(g) = b_in.gen {
                self.generics.push(g);
            }
            if let Some(l) = b_in.loc {
                self.reqs.push(l);
            }
            self.args.push(b_in.ty);
        }
    }

    pub fn desugar(ssig: FnSig) -> ast::FnSig {
        let mut me = Self { generics: vec![], args: vec![], reqs: vec![] };

        // walk over the input types
        me.desugar_inputs(ssig.requires);

        let ensures = ssig
            .ensures
            .into_iter()
            .map(|(x, ty)| (x, convert_ty(ty)))
            .collect();

        ast::FnSig {
            generics: ast::Generics { params: me.generics, span: ssig.span },
            args: me.args,
            requires: me.reqs,
            ret: convert_ty(ssig.returns),
            ensures,
            span: ssig.span,
        }
    }
}

pub fn desugar(ssig: FnSig) -> ast::FnSig {
    Desugar::desugar(ssig)
}
