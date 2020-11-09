use crate::{
    ast,
    ir::{Func, Local},
    ty, Generator,
};

#[derive(Debug)]
pub enum UnifyError {
    BaseMismatch(ty::BaseTy, ty::BaseTy),
    ArityMismatch(usize, usize),
    UnboundedVar(ast::Variable),
}

pub struct FnContext<'func> {
    bound_var_gen: Generator<ty::BoundVariable>,
    vars: Vec<(ast::Variable, ty::Variable)>,
    func: &'func Func,
}

impl<'func> FnContext<'func> {
    pub fn new(func: &'func Func) -> Self {
        Self {
            bound_var_gen: ty::BoundVariable::generator(),
            vars: Vec::new(),
            func,
        }
    }

    fn new_var(&mut self) -> ty::Variable {
        ty::Variable::Bounded(self.bound_var_gen.generate())
    }

    fn solve_var(&self, var: ast::Variable) -> Result<ty::Variable, UnifyError> {
        for (ast_var, ty_var) in self.vars.iter().rev() {
            if *ast_var == var {
                return Ok(*ty_var);
            }
        }
        Err(UnifyError::UnboundedVar(var))
    }

    fn store_var(&mut self, ast_var: ast::Variable) -> ty::Variable {
        let var = self.new_var();
        self.vars.push((ast_var, var));
        var
    }

    fn unify_ty(&self, ty: &ty::Ty, base_ty: &ty::BaseTy) -> Result<(), UnifyError> {
        match ty {
            ty::Ty::RefBase(_, ty, _) if ty == base_ty => Ok(()),
            _ty => panic!(),
        }
    }

    pub fn check_ty(&mut self, ast_ty: &ast::Ty) -> Result<ty::Ty, UnifyError> {
        let ty = self.lower_ty(ast_ty)?;
        match &ty {
            ty::Ty::RefFunc(args, ref_ty) => {
                let arity = args.len();
                if arity != self.func.arg_count {
                    return Err(UnifyError::ArityMismatch(arity, self.func.arg_count));
                }

                let mut func_args = self.func.local_decls.iter().take(arity + 1);
                let (_, func_ret_ty) = func_args.next().unwrap();

                for ((arg, arg_ty), (func_arg, func_arg_ty)) in args.iter().zip(func_args) {
                    assert_eq!(*arg, ty::Variable::Local(*func_arg));
                    self.unify_ty(arg_ty, func_arg_ty)?;
                }

                self.unify_ty(ref_ty, func_ret_ty)?;
            }
            _ => panic!(),
        }

        Ok(ty)
    }

    fn lower_ty(&mut self, ast_ty: &ast::Ty) -> Result<ty::Ty, UnifyError> {
        match ast_ty {
            ast::Ty::Base(base_ty) => Ok(ty::Ty::RefBase(
                self.new_var(),
                *base_ty,
                ty::Predicate::bool(true),
            )),

            ast::Ty::RefBase(var, base_ty, pred) => {
                let var = self.store_var(var.clone());
                let pred = self.lower_pred(pred)?;
                Ok(ty::Ty::RefBase(var, *base_ty, pred))
            }

            ast::Ty::RefFunc(args, ret_ty) => {
                let args = Local::args(args.len())
                    .zip(args.iter())
                    .map(|(local, (arg, arg_ty))| {
                        let local = ty::Variable::Local(local);
                        self.vars.push((arg.clone(), local));
                        Ok((local, self.lower_ty(arg_ty)?))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let ret_ty = self.lower_ty(ret_ty)?;

                Ok(ty::Ty::RefFunc(args, Box::new(ret_ty)))
            }
        }
    }

    fn lower_pred(&mut self, pred: &ast::Predicate) -> Result<ty::Predicate, UnifyError> {
        let pred = match pred {
            ast::Predicate::Var(var) => ty::Predicate::Var(self.solve_var(var.clone())?),
            ast::Predicate::Lit(lit) => ty::Predicate::Lit(*lit),
            ast::Predicate::BinApp(bin_op, op_1, op_2) => {
                let op_1 = self.lower_pred(op_1.as_ref())?;
                let op_2 = self.lower_pred(op_2.as_ref())?;

                ty::Predicate::BinApp(*bin_op, Box::new(op_1), Box::new(op_2))
            }
            ast::Predicate::UnApp(un_op, op) => {
                let op = self.lower_pred(op.as_ref())?;

                ty::Predicate::UnApp(*un_op, Box::new(op))
            }
            ast::Predicate::Cond(if_pred, do_pred, else_pred) => {
                let if_pred = self.lower_pred(if_pred.as_ref())?;
                let do_pred = self.lower_pred(do_pred.as_ref())?;
                let else_pred = self.lower_pred(else_pred.as_ref())?;

                ty::Predicate::Cond(Box::new(if_pred), Box::new(do_pred), Box::new(else_pred))
            }
            ast::Predicate::App(func, args) => {
                let func = self.solve_var(func.clone())?;
                let args = args
                    .iter()
                    .map(|arg| self.lower_pred(arg))
                    .collect::<Result<Vec<_>, _>>()?;

                ty::Predicate::App(func, args)
            }
        };

        Ok(pred)
    }
}
