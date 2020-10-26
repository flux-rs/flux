use rustc_middle::ty::{Ty, TyKind};

pub use crate::refinements::{
    common::{BaseTy, BinOp, IntTy, Literal, UintTy, UnOp},
    ty, Context,
};

#[derive(Debug, Eq, PartialEq)]
pub struct Variable(pub String);

#[derive(Debug)]
pub enum Predicate {
    Var(Variable),
    Lit(Literal),
    BinApp(BinOp, Box<Self>, Box<Self>),
    UnApp(UnOp, Box<Self>),
    Cond(Box<Self>, Box<Self>, Box<Self>),
    App(Variable, Vec<Self>),
}

impl<'tcx> Predicate {
    fn lower(self, tcx: &Context<'tcx>) -> ty::Predicate {
        match self {
            Self::Var(var) => {
                let var = tcx.get_var(var);

                ty::Predicate::Var(var)
            }
            Self::Lit(lit) => ty::Predicate::Lit(lit),
            Self::BinApp(bin_op, op1, op2) => {
                let op1 = op1.lower(tcx);
                let op2 = op2.lower(tcx);

                ty::Predicate::BinApp(bin_op, Box::new(op1), Box::new(op2))
            }
            Self::UnApp(un_op, op) => {
                let op = op.lower(tcx);

                ty::Predicate::UnApp(un_op, Box::new(op))
            }
            Self::Cond(if_pred, then_pred, else_pred) => {
                let if_pred = if_pred.lower(tcx);
                let then_pred = then_pred.lower(tcx);
                let else_pred = else_pred.lower(tcx);

                ty::Predicate::Cond(Box::new(if_pred), Box::new(then_pred), Box::new(else_pred))
            }
            Self::App(func, args) => {
                let func = tcx.get_var(func);
                let args = args.into_iter().map(|arg| arg.lower(tcx)).collect();

                ty::Predicate::App(func, args)
            }
        }
    }
}

#[derive(Debug)]
pub enum RefinedTy {
    Base(BaseTy),
    RefBase(Variable, BaseTy, Predicate),
    RefFunc(Vec<(Variable, Self)>, Box<Self>),
}

impl<'tcx> RefinedTy {
    pub fn unify(self, ctx: &mut Context<'tcx>, rust_ty: Ty<'tcx>) -> ty::RefinedTy {
        match self {
            Self::Base(base_ty) => {
                base_ty.unify(rust_ty);

                let var = ctx.new_var();

                ty::RefinedTy::RefBase(var, base_ty, ty::Predicate::Lit(ty::Literal::Bool(true)))
            }

            Self::RefBase(var, base_ty, pred) => {
                base_ty.unify(rust_ty);

                let var = ctx.store_var(var);

                let pred = pred.lower(ctx);

                ty::RefinedTy::RefBase(var, base_ty, pred)
            }

            Self::RefFunc(args, ret_ty) => {
                if let TyKind::FnDef(def_id, _) = rust_ty.kind() {
                    let body = ctx.tcx.optimized_mir(*def_id);
                    let rust_args = body
                        .args_iter()
                        .map(|arg| body.local_decls[arg].ty)
                        .collect::<Vec<_>>();
                    let rust_ret_ty = body.return_ty();

                    assert_eq!(rust_args.len(), args.len());

                    let args: Vec<(ty::Variable, ty::RefinedTy)> = args
                        .into_iter()
                        .zip(rust_args.into_iter())
                        .map(|((arg, arg_ty), rust_arg_ty)| {
                            let arg = ctx.store_var(arg);

                            let arg_ty = arg_ty.unify(ctx, rust_arg_ty);

                            (arg, arg_ty)
                        })
                        .collect();

                    let ret_ty = ret_ty.unify(ctx, rust_ret_ty);

                    ty::RefinedTy::RefFunc(args, Box::new(ret_ty))
                } else {
                    panic!("Cannot unify function type with non-function type.")
                }
            }
        }
    }
}
