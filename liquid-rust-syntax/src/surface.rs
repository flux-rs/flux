pub use rustc_ast::token::LitKind;
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ast::{Expr, self, GenericParam};

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
    gen : Option<GenericParam>, 
    ty  : ast::Ty, 
    loc : Option<(Ident, ast::Ty)>
}


// /// nameTy(x, t) adds a default named binder
// fn nameTy(x:Ident, nTy: &NamedTy) -> NamedTy {
//     let span = nTy.span;
//     let kind =  match nTy.kind {     
//         NamedTyKind::AnonBase(t) => NamedTyKind::NamedBase(x, t),
//         _ => nTy.kind,     
//     }; 
//     NamedTy { kind, span } 
// }

// fn mk_generic(x: &Ident, _ty: &Ty) -> ast::GenericParam { 
//     let name = *x;
//     let sort = Ident { name: rustc_span::Symbol::intern("int"), span: name.span };
//     ast::GenericParam { name, sort, pred: None }
// } 

// fn generic_param(x: &Ident, nTy: &NamedTy) -> Option<ast::GenericParam> {
//     match &nTy.kind {
//         NamedTyKind::NamedBase(n, ty) => Some(mk_generic(&n, &ty)),
//         NamedTyKind::AnonBase(ty) => Some(mk_generic(x, &ty)),
//         NamedTyKind::Ref(_, _) => None,
//     }
// }

fn convert_path(p:Path) -> ast::Path {
    todo!()
}

fn convert_ty(t:Ty) -> ast::Ty {
    todo!()
}

fn mk_sort(span:Span) -> Ident {
    Ident { name: rustc_span::Symbol::intern("int"), span }
}

fn mk_singleton(x:Ident) -> Expr {
    Expr { kind: ast::ExprKind::Var(x), span: x.span }
}

fn ident_loc(x:Ident) -> Ident { 
    let mut star = String::from("*");
    star.push_str(x.name.as_str());
    let name = rustc_span::Symbol::intern(&star);
    Ident { name, span: x.span }
}

fn bind_in(x: Ident, ty: Ty) -> BindIn {
    match ty.kind {
        TyKind::AnonEx { path, pred } => {
            // make the generic
            let gen = Some(ast::GenericParam { 
                name: x, 
                sort: mk_sort(x.span), 
                pred: Some(pred) 
            });
            // convert the path into a singleton-ty
            let path = convert_path(path);
            let refine = mk_singleton(x);
            let kind = ast::TyKind::RefineTy{ path, refine };
            let ty = ast::Ty { kind, span: ty.span };
            BindIn { gen, ty, loc: None }
        },
        TyKind::Base(p) => { 
            let path = convert_path(p);
            let kind = ast::TyKind::BaseTy(path);
            let ty = ast::Ty { kind, span: ty.span };
            BindIn { gen: None, loc: None, ty }
        },
        TyKind::Exists { bind, path, pred } => { 
            let path = convert_path(path);
            let kind = ast::TyKind::Exists { bind, path, pred };
            let ty = ast::Ty { kind, span: ty.span };
            BindIn { gen: None, ty, loc: None }
        },
        TyKind::Named(n, t) => { 
            bind_in(n, *t) 
        },
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
            if let Some(l)  = b_in.loc {  
                self.reqs.push(l); 
            }
            self.args.push(b_in.ty); 
        }
    }

    pub fn desugar(ssig: FnSig) -> ast::FnSig {

        let mut me = Self { generics: vec![], args: vec![], reqs: vec![], };

        // walk over the input types
        me.desugar_inputs(ssig.requires);

        // build output types
        // let ret = convert_ty(ssig.returns);

        // build ensures
        let mut ensures = vec![];
        for (x, ty) in ssig.ensures {
            ensures.push((x, convert_ty(ty)))
        }

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



// fn gather_generics(sIns: Vec<(Ident, NamedTy)>, span:Span) -> ast::Generics {
//     let mut params = vec![];
//     for (x, nTy) in sIns.iter() {
//         if let Some(gen) = generic_param(x, nTy) {
//             params.push(gen);
//         }
//     }
//     ast::Generics { params, span }
// }

// fn desugar_inputs(ssig: FnSig) -> (ast::Generics, Vec<(Ident, ast::Ty)> ,Vec<ast::Ty>) {

//   // add `@binders` to inputs without names
//   // let named_inputs = ssig.requires.iter().map(|x_ty| { (x_ty.0, nameTy(x_ty.0, &x_ty.1)) }).collect();

//   // generics 
//   let generics = gather_generics(ssig.requires, ssig.span);

//   // locations
//   let locations = todo!();
  
//   // tybinds
//   let binds = todo!();

//   (generics, locations, binds)
// } 

// fn desugar_outputs(sRet: Ty, sEns: Vec<(Ident, NamedTy)>) -> (ast::Ty, Vec<(Ident, ast::Ty)>) {
//   todo!()
// }

pub fn desugar(ssig: FnSig) -> ast::FnSig {
    Desugar::desugar(ssig)
}

