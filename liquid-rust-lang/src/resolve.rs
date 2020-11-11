use crate::{ast, ty, tycheck::TyCtx};

#[derive(Debug)]
pub enum ResolveError {
    BaseMismatch(ty::BaseTy, ty::BaseTy),
    ArityMismatch(usize, usize),
    UnboundedVar(ast::Variable),
}

pub struct ResolveCtx<'tcx> {
    vars: Vec<(ast::Variable, ty::Variable)>,
    tcx: &'tcx mut TyCtx,
}

impl<'tcx> ResolveCtx<'tcx> {
    pub(crate) fn new(tcx: &'tcx mut TyCtx) -> Self {
        Self {
            vars: Vec::new(),
            tcx,
        }
    }

    fn solve_var(&self, var: ast::Variable) -> Result<ty::Variable, ResolveError> {
        for (ast_var, ty_var) in self.vars.iter().rev() {
            if *ast_var == var {
                return Ok(*ty_var);
            }
        }
        Err(ResolveError::UnboundedVar(var))
    }

    fn store_var(&mut self, ast_var: ast::Variable) -> ty::Variable {
        let var = self.tcx.new_var();
        self.vars.push((ast_var, var));
        var
    }

    pub(crate) fn resolve_ty(&mut self, ast_ty: &ast::Ty) -> Result<ty::Ty, ResolveError> {
        match ast_ty {
            ast::Ty::Base(base_ty) => {
                Ok(ty::Ty::RefBase(self.tcx.new_var(), *base_ty, true.into()))
            }

            ast::Ty::RefBase(var, base_ty, pred) => {
                let var = self.store_var(var.clone());
                let pred = self.resolve_pred(pred)?;
                Ok(ty::Ty::RefBase(var, *base_ty, pred))
            }

            ast::Ty::RefFunc(args, ret_ty) => {
                let args = args
                    .iter()
                    .map(|(arg, arg_ty)| {
                        let var = self.tcx.new_var();
                        self.vars.push((arg.clone(), var));
                        Ok((var, self.resolve_ty(arg_ty)?))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let ret_ty = self.resolve_ty(ret_ty)?;

                Ok(ty::Ty::RefFunc(args, Box::new(ret_ty)))
            }
        }
    }

    fn resolve_pred(&mut self, pred: &ast::Predicate) -> Result<ty::Predicate, ResolveError> {
        let pred = match pred {
            ast::Predicate::Var(var) => ty::Predicate::Var(self.solve_var(var.clone())?),
            ast::Predicate::Lit(lit) => ty::Predicate::Lit(*lit),
            ast::Predicate::BinApp(bin_op, op_1, op_2) => {
                let op_1 = self.resolve_pred(op_1.as_ref())?;
                let op_2 = self.resolve_pred(op_2.as_ref())?;

                ty::Predicate::BinApp(*bin_op, Box::new(op_1), Box::new(op_2))
            }
            ast::Predicate::UnApp(un_op, op) => {
                let op = self.resolve_pred(op.as_ref())?;

                ty::Predicate::UnApp(*un_op, Box::new(op))
            }
            ast::Predicate::Cond(if_pred, do_pred, else_pred) => {
                let if_pred = self.resolve_pred(if_pred.as_ref())?;
                let do_pred = self.resolve_pred(do_pred.as_ref())?;
                let else_pred = self.resolve_pred(else_pred.as_ref())?;

                ty::Predicate::Cond(Box::new(if_pred), Box::new(do_pred), Box::new(else_pred))
            }
            ast::Predicate::App(func, args) => {
                let func = self.solve_var(func.clone())?;
                let args = args
                    .iter()
                    .map(|arg| self.resolve_pred(arg))
                    .collect::<Result<Vec<_>, _>>()?;

                ty::Predicate::App(func, args)
            }
        };

        Ok(pred)
    }
}
