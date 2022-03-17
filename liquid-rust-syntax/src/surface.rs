pub use rustc_ast::token::LitKind;
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ast::{self, Expr, GenericParam, Refine};

#[derive(Debug)]
pub struct FnSig<T> {
    /// example: `l: i32@n`
    pub requires: Vec<(Ident, Ty<T>)>,
    /// example `i32{v:v >= 0}`
    pub returns: Ty<T>,
    /// example: `*x: i32{v:v = n+1}`
    pub ensures: Vec<(Ident, Ty<T>)>,
    /// example: `where n > 0`
    pub wherep: Option<Expr>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub struct Ty<T> {
    pub kind: TyKind<T>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<T> {
    /// ty
    Base(Path<T>),

    /// t[e]
    Refine { path: Path<T>, refine: Refine },

    /// ty{b:e}
    Exists { bind: Ident, path: Path<T>, pred: Expr },

    /// ty{e}, the param binder is used e.g. x: i32{0 < x}
    AnonEx { path: Path<T>, pred: Expr },

    /// named: n@t
    Named(Ident, Box<Ty<T>>),

    /// reference
    Ref(RefKind, Box<Ty<T>>),
}

#[derive(Debug)]
pub struct Path<T> {
    /// vec
    // pub ident: Ident,
    pub ident: T,
    /// <nat>
    pub args: Option<Vec<Ty<T>>>,
    pub span: Span,
}

#[derive(Debug)]
pub enum RefKind {
    Weak,
    Mut,
    Immut,
}

struct Desugar {
    generics: Vec<ast::GenericParam>,
    args: Vec<ast::Ty>,
    reqs: Vec<(Ident, ast::Ty)>,
}

/// A `BindIn` is the information obtained from a single input-param binding
#[derive(Debug)]
struct BindIn {
    gen: Option<GenericParam>,
    ty: ast::Ty,
    loc: Option<(Ident, ast::Ty)>,
}

pub type BarePath   = Path<Ident>;
pub type BareTyKind = TyKind<Ident>;
pub type BareTy     = Ty<Ident>;
pub type BareFnSig  = FnSig<Ident>;

fn convert_path(p: BarePath) -> ast::Path {
    ast::Path {
        ident: p.ident,
        span: p.span,
        args: p.args.map(|ts| ts.into_iter().map(convert_ty).collect()),
    }
}

fn convert_tykind(t: BareTyKind) -> ast::TyKind {
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
        TyKind::Ref(RefKind::Immut, t) => ast::TyKind::ShrRef(Box::new(convert_ty(*t))),
        TyKind::Ref(_, t) => ast::TyKind::WeakRef(Box::new(convert_ty(*t))),
        TyKind::Refine { path, refine } => {
            let path = convert_path(path);
            ast::TyKind::RefineTy { path, refine }
        }
    }
}

fn convert_ty(t: BareTy) -> ast::Ty {
    ast::Ty { kind: convert_tykind(t.kind), span: t.span }
}

fn is_bool(path: &BarePath) -> bool {
    path.ident.as_str() == "bool"
}

// HACK(ranjitjhala) need better way to determine if Path is a Type-Param
fn is_generic(path: &BarePath) -> bool {
    let str = path.ident.as_str();
    if let Some(c) = str.chars().next() {
        c.is_uppercase() && str.len() == 1
    } else {
        false
    }
}

fn is_float(path: &BarePath) -> bool {
    path.ident.as_str() == "f32" || path.ident.as_str() == "f64"
}

fn is_refinable(path: &BarePath) -> bool {
    !is_generic(path) && !is_float(path)
}

// HACK(ranjitjhala) need better way to "embed" rust types to sort
fn mk_sort(path: &BarePath, span: Span) -> Ident {
    let sort_name = if is_bool(path) { "bool" } else { "int" };
    Ident { name: rustc_span::Symbol::intern(sort_name), span }
}

fn mk_singleton(x: Ident) -> ast::Refine {
    let e = Expr { kind: ast::ExprKind::Var(x), span: x.span };
    ast::Refine { exprs: vec![e], span: x.span }
}

fn mk_generic(x: Ident, path: &BarePath, pred: Option<Expr>) -> ast::GenericParam {
    ast::GenericParam { name: x, sort: mk_sort(path, x.span), pred }
}

fn strengthen_pred(p: Option<Expr>, e: Expr) -> Expr {
    match p {
        None => e,
        Some(pe) => {
            let span = pe.span;
            let kind = ast::ExprKind::BinaryOp(ast::BinOp::And, Box::new(pe), Box::new(e));
            Expr { kind, span }
        }
    }
}

impl BindIn {
    fn from_path(x: Ident, single: bool, p: BarePath, span: Span, pred: Option<Expr>) -> BindIn {
        if single && is_refinable(&p) {
            let gen = Some(mk_generic(x, &p, pred));
            let path = convert_path(p);
            let refine = mk_singleton(x);
            let kind = ast::TyKind::RefineTy { path, refine };
            let ty = ast::Ty { kind, span };
            BindIn { gen, ty, loc: None }
        } else {
            let path = convert_path(p);
            let kind = ast::TyKind::BaseTy(path);
            let ty = ast::Ty { kind, span };
            BindIn { gen: None, ty, loc: None }
        }
    }

    fn from_ty(x: Ident, single: bool, ty: BareTy) -> BindIn {
        match ty.kind {
            TyKind::AnonEx { path, pred } => {
                BindIn::from_path(x, single, path, ty.span, Some(pred))
            }
            TyKind::Base(path) => BindIn::from_path(x, single, path, ty.span, None),
            TyKind::Refine { path, refine } => {
                let path = convert_path(path);
                let kind = ast::TyKind::RefineTy { path, refine };
                let ty = ast::Ty { kind, span: ty.span };
                BindIn { gen: None, ty, loc: None }
            }
            TyKind::Exists { bind, path, pred } => {
                let path = convert_path(path);
                let kind = ast::TyKind::Exists { bind, path, pred };
                let ty = ast::Ty { kind, span: ty.span };
                BindIn { gen: None, ty, loc: None }
            }
            TyKind::Named(n, t) => BindIn::from_ty(n, true, *t),
            TyKind::Ref(RefKind::Mut, t) => {
                let b = BindIn::from_ty(x, false, *t);
                let ty = ast::Ty { kind: ast::TyKind::StrgRef(x), span: ty.span };
                BindIn { gen: b.gen, ty, loc: Some((x, b.ty)) }
            }
            TyKind::Ref(RefKind::Immut, t) => {
                let b = BindIn::from_ty(x, false, *t);
                let ty = ast::Ty { kind: ast::TyKind::ShrRef(Box::new(b.ty)), span: ty.span };
                BindIn { gen: b.gen, ty, loc: None }
            }
            TyKind::Ref(RefKind::Weak, t) => {
                let b = BindIn::from_ty(x, false, *t);
                let ty = ast::Ty { kind: ast::TyKind::WeakRef(Box::new(b.ty)), span: ty.span };
                BindIn { gen: b.gen, ty, loc: None }
            }
        }
    }
}

impl Desugar {
    fn desugar_inputs(&mut self, in_sigs: Vec<(Ident, BareTy)>) {
        for (x, ty) in in_sigs {
            let b_in = BindIn::from_ty(x, true, ty);
            if let Some(g) = b_in.gen {
                self.generics.push(g);
            }
            if let Some(l) = b_in.loc {
                self.reqs.push(l);
            }
            self.args.push(b_in.ty);
        }
    }

    pub fn desugar(ssig: BareFnSig) -> ast::FnSig {
        let mut me = Self { generics: vec![], args: vec![], reqs: vec![] };

        // walk over the input types
        me.desugar_inputs(ssig.requires);

        // Add the "where" clause to the last GenericParam
        if let Some(e) = ssig.wherep {
            if let Some(mut g) = me.generics.pop() {
                g.pred = Some(strengthen_pred(g.pred, e));
                me.generics.push(g);
            } else {
                panic!("'where' clause without generic params! {:?}", e.span);
            }
        }

        // translate the output store
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

pub fn desugar(ssig: BareFnSig) -> ast::FnSig {
    Desugar::desugar(ssig)
}
