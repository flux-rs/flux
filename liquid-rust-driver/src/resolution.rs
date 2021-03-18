use liquid_rust_common::index::IndexGen;
use liquid_rust_lrir::ty::{self, Path, Var};
use liquid_rust_parser::ast;
use quickscope::ScopeMap;

pub struct Resolver<'src, 'a> {
    tcx: &'a ty::TyCtxt,
    vars: ScopeMap<&'src str, Var>,
    var_gen: IndexGen,
}

impl<'src, 'a> Resolver<'src, 'a> {
    pub fn new(tcx: &'a ty::TyCtxt) -> Self {
        Self {
            tcx,
            vars: ScopeMap::new(),
            var_gen: IndexGen::new(),
        }
    }

    pub fn resolve(&mut self, fn_decl: ast::FnDecl<'src>) -> ty::FnDecl {
        let mut requires = Vec::new();
        let mut inputs = Vec::new();

        for (ident, ty) in fn_decl.inputs {
            self.vars.push_layer();
            self.vars.define(ident.symbol, Var::Nu);
            let ty = ty.resolve(self);
            self.vars.pop_layer();

            let fresh_gv = self.var_gen.fresh();
            self.vars.define(ident.symbol, Var::Ghost(fresh_gv));

            requires.push((fresh_gv, ty));
            inputs.push(fresh_gv);
        }

        let output_gv = self.var_gen.fresh();
        let output_ty = match fn_decl.output {
            Some(ty) => ty.resolve(self),
            None => self.tcx.types.unit(),
        };
        let ensures = vec![(output_gv, output_ty)];
        let output = output_gv;

        ty::FnDecl {
            requires,
            inputs,
            ensures,
            output,
        }
    }
}

trait Resolve<'src> {
    type Output;

    fn resolve(self, cx: &mut Resolver<'src, '_>) -> Self::Output;
}

impl<'src> Resolve<'src> for ast::Predicate<'src> {
    type Output = ty::Pred;

    fn resolve(self, cx: &mut Resolver<'src, '_>) -> Self::Output {
        let tcx = cx.tcx;
        match self.kind {
            // FIXME: We should have a uniform way to represent constants.
            ast::PredicateKind::Lit(ast::Literal::Bool(b)) => tcx.mk_const(b.into()),
            ast::PredicateKind::Lit(ast::Literal::Int(i)) => tcx.mk_const(i.into()),
            ast::PredicateKind::UnaryOp(un_op, op) => {
                let un_op = match un_op.kind {
                    ast::UnOpKind::Not => ty::UnOp::Not,
                    ast::UnOpKind::Neg => ty::UnOp::Neg,
                };
                let op = op.resolve(cx);
                tcx.mk_un_op(un_op, op)
            }
            ast::PredicateKind::BinaryOp(bin_op, op1, op2) => {
                let bin_op = match bin_op.kind {
                    ast::BinOpKind::Add => ty::BinOp::Add,
                    ast::BinOpKind::Sub => ty::BinOp::Sub,
                    ast::BinOpKind::Mul => ty::BinOp::Mul,
                    ast::BinOpKind::Div => ty::BinOp::Div,
                    ast::BinOpKind::Rem => ty::BinOp::Rem,
                    ast::BinOpKind::And => ty::BinOp::And,
                    ast::BinOpKind::Or => ty::BinOp::Or,
                    // FIXME: fill with typechecking info
                    ast::BinOpKind::Eq => ty::BinOp::Eq(ty::BaseTy::Int),
                    ast::BinOpKind::Neq => ty::BinOp::Neq(ty::BaseTy::Int),
                    ast::BinOpKind::Lt => ty::BinOp::Lt,
                    ast::BinOpKind::Gt => ty::BinOp::Gt,
                    ast::BinOpKind::Lte => ty::BinOp::Lte,
                    ast::BinOpKind::Gte => ty::BinOp::Gte,
                };
                let op1 = op1.resolve(cx);
                let op2 = op2.resolve(cx);
                tcx.mk_bin_op(bin_op, op1, op2)
            }
            ast::PredicateKind::Path(ident, projection) => {
                let path = Path {
                    base: cx.vars[ident.symbol],
                    projs: projection,
                };
                tcx.mk_path(path)
            }
        }
    }
}

impl<'src> Resolve<'src> for ast::Ty<'src> {
    type Output = ty::Ty;

    fn resolve(self, cx: &mut Resolver<'src, '_>) -> Self::Output {
        let tcx = cx.tcx;
        match self.kind {
            ast::TyKind::Base(bty) => {
                let bty = map_base_ty(bty);
                tcx.mk_refine(bty, tcx.preds.tt())
            }
            ast::TyKind::Refined(refine) => {
                cx.vars.push_layer();
                cx.vars.define(refine.variable.symbol, Var::Nu);
                let pred = refine.refinement.resolve(cx);
                cx.vars.pop_layer();
                tcx.mk_refine(map_base_ty(refine.base_ty), pred)
            }
            ast::TyKind::Tuple(tup) => {
                cx.vars.push_layer();
                let tup = tup
                    .into_iter()
                    .map(|(fld, ty)| {
                        let fresh_fld = cx.var_gen.fresh();
                        if let Some(ident) = fld {
                            cx.vars.push_layer();
                            cx.vars.define(ident.symbol, Var::Nu);
                            let ty = ty.resolve(cx);
                            cx.vars.pop_layer();
                            cx.vars.define(ident.symbol, Var::Field(fresh_fld));
                            (fresh_fld, ty)
                        } else {
                            (fresh_fld, ty.resolve(cx))
                        }
                    })
                    .collect();
                cx.vars.pop_layer();
                tcx.mk_tuple(tup)
            }
        }
    }
}

fn map_base_ty(ty: ast::BaseTy) -> ty::BaseTy {
    match ty {
        ast::BaseTy::Bool => ty::BaseTy::Bool,
        ast::BaseTy::Int => ty::BaseTy::Int,
    }
}
