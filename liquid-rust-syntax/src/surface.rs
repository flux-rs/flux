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

// #[derive(Debug)]
// pub struct NamedTy {
//     pub kind: NamedTyKind,
//     pub span: Span,
// }

// #[derive(Debug)]
// pub enum NamedTyKind {
//     /// For inputs
//     NamedBase(Ident, Ty),

//     /// For outputs
//     AnonBase(Ty),

//     /// For inputs and outputs
//     Ref(RefKind, Box<NamedTy>),
// }

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
        args: match p.args {
            Some(ts) => Some(ts.into_iter().map(convert_ty).collect()),
            None => None,
        },
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

fn mk_sort(span: Span) -> Ident {
    Ident { name: rustc_span::Symbol::intern("int"), span }
}

fn mk_singleton(x: Ident) -> ast::Refine {
    let e = Expr { kind: ast::ExprKind::Var(x), span: x.span };
    ast::Refine { exprs: vec![e], span: x.span }
}

fn mk_generic(x: Ident, pred: Option<Expr>) -> ast::GenericParam {
    ast::GenericParam { name: x, sort: mk_sort(x.span), pred }
}

fn ident_loc(x: Ident) -> Ident {
    let mut star = String::from("*");
    star.push_str(x.name.as_str());
    let name = rustc_span::Symbol::intern(&star);
    Ident { name, span: x.span }
}

fn path_bind_in(x: Ident, path: Path, span: Span, pred: Option<Expr>) -> BindIn {
    let gen = Some(mk_generic(x, pred));
    let path = convert_path(path);
    let refine = mk_singleton(x);
    let kind = ast::TyKind::RefineTy { path, refine };
    let ty = ast::Ty { kind, span };
    BindIn { gen, ty, loc: None }
}

fn bind_in(x: Ident, ty: Ty) -> BindIn {
    match ty.kind {
        TyKind::AnonEx { path, pred } => path_bind_in(x, path, ty.span, Some(pred)),
        TyKind::Base(path) => path_bind_in(x, path, ty.span, None),
        TyKind::Exists { bind, path, pred } => {
            let path = convert_path(path);
            let kind = ast::TyKind::Exists { bind, path, pred };
            let ty = ast::Ty { kind, span: ty.span };
            BindIn { gen: None, ty, loc: None }
        }
        TyKind::Named(n, t) => bind_in(n, *t),
        TyKind::Ref(_, t) => {
            let b = bind_in(x, *t);
            let l = ident_loc(x);
            let ty = ast::Ty { kind: ast::TyKind::StrgRef(l), span: ty.span };
            BindIn { gen: b.gen, ty, loc: Some((l, b.ty)) }
        }
    }
}

impl Desugar {
    fn desugar_inputs(&mut self, in_sigs: Vec<(Ident, Ty)>) {
        for (x, ty) in in_sigs {
            let b_in = bind_in(x, ty);
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
