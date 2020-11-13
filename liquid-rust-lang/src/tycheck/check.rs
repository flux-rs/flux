use crate::{
    ir::{BasicBlock, BlockId, Func, Terminator},
    ty::{BaseTy, Predicate, Ty},
    tycheck::{Constraint, Synth, TyContextAt},
};

fn begin_rule<'tcx, T: Check<'tcx> + std::fmt::Display>(rule: &str, term: &T, ty: &Ty) {
    log::info!("Running {} for `{}` with `{}`", rule, term, ty);
}

fn end_rule<'tcx, T: Check<'tcx> + std::fmt::Display>(
    rule: &str,
    term: &T,
    ty: &Ty,
    constraint: Constraint,
) -> Constraint {
    log::info!(
        "{} for `{}` with `{}` returns `{}`",
        rule,
        term,
        constraint,
        ty
    );
    constraint
}

pub(super) trait Check<'tcx> {
    fn check(&self, ctx: &TyContextAt<'tcx>, ty: &Ty) -> Constraint;
}

impl<'tcx> Check<'tcx> for Terminator {
    fn check(&self, ctx: &TyContextAt<'tcx>, ty: &Ty) -> Constraint {
        match self {
            // Chk-Ret
            Self::Return => {
                begin_rule("Chk-Ret", self, ty);
                let ret_local = ctx.func().ret_local;
                end_rule("Chk-Ret", self, ty, ctx.check(&ret_local, ty))
            }
            // Chk-Goto
            Self::Goto(bb) => {
                begin_rule("Chk-Goto", self, ty);
                end_rule("Chk-Goto", self, ty, ctx.check(bb, ty))
            }
            _ => todo!(),
        }
    }
}

// Chk-Syn
impl<'tcx, T: Synth<'tcx> + std::fmt::Display> Check<'tcx> for T {
    fn check(&self, ctx: &TyContextAt<'tcx>, ty: &Ty) -> Constraint {
        begin_rule("Chk-Syn", self, ty);
        let (syn_constr, syn_ty) = ctx.synth(self);
        let sub_constr = ctx.is_subtype(&syn_ty, ty);
        end_rule("Chk-Syn", self, ty, syn_constr & sub_constr)
    }
}

// Chk-BlkId
impl<'tcx> Check<'tcx> for BlockId {
    fn check(&self, ctx: &TyContextAt<'tcx>, ty: &Ty) -> Constraint {
        begin_rule("Chk-Blk", self, ty);
        let block = ctx
            .func()
            .basic_blocks
            .get(self)
            .expect("BlockIds should always map to a Block.");

        end_rule("Chk-Blk", self, ty, ctx.check(block, ty))
    }
}

// Chk-Blk
impl<'tcx> Check<'tcx> for BasicBlock {
    fn check(&self, ctx: &TyContextAt<'tcx>, ty: &Ty) -> Constraint {
        let BasicBlock(statements, terminator) = self;

        let mut constraint = Constraint::from(true);

        if !statements.is_empty() {
            let unit = ctx.refined(BaseTy::Unit);
            for statement in statements {
                constraint = constraint & ctx.check(statement, &unit);
            }
        }

        constraint & ctx.check(terminator, ty)
    }
}

// Chk-Func
impl<'tcx> Check<'tcx> for Func {
    fn check(&self, ctx: &TyContextAt<'tcx>, ty: &Ty) -> Constraint {
        match ty {
            Ty::RefFunc(args, ret_ty) => {
                if args.len() != self.args.len() {
                    panic!("Arity mismatch");
                }

                let mut constraint = Constraint::from(true);

                for ((var, var_ty), (local, local_ty)) in args.iter().zip(self.args.iter()) {
                    ctx.annotate_local(*local, *var, var_ty.clone());
                    constraint = constraint & ctx.is_subtype(var_ty, &ctx.refined(*local_ty));
                }

                constraint =
                    constraint & ctx.is_subtype(ret_ty.as_ref(), &ctx.refined(self.ret_ty));

                ctx.annotate_local(self.ret_local, ctx.new_variable(), ctx.refined(self.ret_ty));

                for &(local, local_ty) in &self.locals {
                    let local = ctx.store_local(local);

                    let var = ctx.new_variable();
                    let ty = Ty::RefBase(var, local_ty, Predicate::from(var).eq(local));

                    ctx.annotate_variable(local, ty);
                }

                constraint & ctx.check(&self.initial_block, ret_ty.as_ref())
            }
            _ => panic!("Expected function type"),
        }
    }
}
