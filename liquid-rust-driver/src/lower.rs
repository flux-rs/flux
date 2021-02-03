//! Lowering refinement annotations into the core IR.

use std::iter::FromIterator;

use liquid_rust_core::{
    ast::{
        pred::{Place, Var},
        FnTy, Heap, Pred, Refine, Ty,
    },
    names::Field,
    ty::{BinOp, Location, UnOp},
};
use liquid_rust_parser::ast;
use quickscope::ScopeMap;

pub struct LowerCtx<'src> {
    vars: ScopeMap<Var<ast::Ident<'src>>, Var>,
    locs: usize,
    fields: usize,
}

impl<'src> LowerCtx<'src> {
    pub fn new() -> Self {
        LowerCtx {
            vars: ScopeMap::new(),
            locs: 0,
            fields: 0,
        }
    }

    fn fresh_location(&mut self) -> Location {
        self.locs += 1;
        Location::new(self.locs - 1)
    }

    fn fresh_field(&mut self) -> Field {
        self.fields += 1;
        Field::new(self.fields - 1)
    }
}

pub trait Lower<'src> {
    type Output;

    fn lower(self, lcx: &mut LowerCtx<'src>) -> Self::Output;
}

impl Lower<'_> for ast::UnOp {
    type Output = UnOp;

    fn lower(self, _lcx: &mut LowerCtx<'_>) -> Self::Output {
        match self.kind {
            ast::UnOpKind::Not => UnOp::Not,
            ast::UnOpKind::Neg => unimplemented!(),
        }
    }
}

impl Lower<'_> for ast::BinOp {
    type Output = BinOp;

    fn lower(self, _lcx: &mut LowerCtx<'_>) -> Self::Output {
        // TODO: Support iff (<=>)?
        match self.kind {
            ast::BinOpKind::Add => BinOp::Add,
            ast::BinOpKind::Sub => BinOp::Sub,
            ast::BinOpKind::Lt => BinOp::Lt,
            ast::BinOpKind::Le => BinOp::Le,
            ast::BinOpKind::Eq => BinOp::Eq,
            ast::BinOpKind::Ge => BinOp::Ge,
            ast::BinOpKind::Gt => BinOp::Gt,
            _ => unimplemented!(),
        }
    }
}

impl<'src> Lower<'src> for ast::Predicate<'src> {
    type Output = Pred;

    fn lower(self, lcx: &mut LowerCtx<'src>) -> Self::Output {
        match self.kind {
            ast::PredicateKind::Lit(c) => Pred::Constant(c),
            ast::PredicateKind::Place(p) => {
                let base = *lcx.vars.get(&p.place.base).expect("Lower: Var not found");
                let projs = p.place.projs;
                Pred::Place(Place { base, projs })
            }
            ast::PredicateKind::UnaryOp(uo, bp) => {
                Pred::UnaryOp(uo.lower(lcx), Box::new((*bp).lower(lcx)))
            }
            ast::PredicateKind::BinaryOp(bop, ba, bb) => Pred::BinaryOp(
                bop.lower(lcx),
                Box::new(ba.lower(lcx)),
                Box::new(bb.lower(lcx)),
            ),
        }
    }
}

impl<'src> Lower<'src> for ast::Ty<'src> {
    type Output = Ty;

    fn lower(self, lcx: &mut LowerCtx<'src>) -> Self::Output {
        match self.kind {
            ast::TyKind::Base(b) => Ty::Refine(b, Refine::Pred(Pred::tt())),
            ast::TyKind::Refined(Some(i), b, p) => {
                lcx.vars.push_layer();
                lcx.vars.define(Var::Location(Location::new(i)), Var::Nu);
                let p = p.lower(lcx);
                lcx.vars.pop_layer();
                Ty::Refine(b, Refine::Pred(p))
            }
            ast::TyKind::Refined(None, b, p) => Ty::Refine(b, Refine::Pred(p.lower(lcx))),
            ast::TyKind::Tuple(fs) => {
                lcx.vars.push_layer();
                let mut tup = Vec::new();
                for (f, ty) in fs {
                    let fresh = lcx.fresh_field();
                    lcx.vars.push_layer();
                    lcx.vars.define(Var::Field(f.clone()), Var::Nu);
                    tup.push((fresh, ty.lower(lcx)));
                    lcx.vars.pop_layer();
                    lcx.vars.define(Var::Field(f), Var::Field(fresh));
                }
                lcx.vars.pop_layer();
                Ty::Tuple(tup)
            }
        }
    }
}

impl<'src> Lower<'src> for ast::FnTy<'src> {
    type Output = FnTy;

    fn lower(self, lcx: &mut LowerCtx<'src>) -> Self::Output {
        let args = self.kind.args;
        let out = *self.kind.output;

        let mut inputs = Vec::new();
        let mut in_heap = Vec::new();
        let mut out_heap = Vec::new();

        // We then iterate through each of the args and lower each of them.
        for (ident, ty) in args {
            // We lower the target type
            lcx.vars.push_layer();
            lcx.vars
                .define(Var::Location(Location::new(ident.clone())), Var::Nu);
            let ty = ty.lower(lcx);
            lcx.vars.pop_layer();

            // Generate a fresh location which will be used in the input
            // heap
            let loc = lcx.fresh_location();
            lcx.vars
                .define(Var::Location(Location::new(ident)), Var::Location(loc));

            // We then insert the arg into the inputs and the heap.
            inputs.push(loc);
            in_heap.push((loc, ty.clone()));
        }

        // Afterwards, we lower the output.

        let output = lcx.fresh_location();
        out_heap.push((output, out.lower(lcx)));

        // TODO: regions
        let regions = vec![];

        FnTy {
            in_heap: Heap::from_iter(in_heap),
            inputs,
            out_heap: Heap::from_iter(out_heap),
            output,
            regions,
        }
    }
}
