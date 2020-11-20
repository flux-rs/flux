use std::{cell::RefCell, rc::Rc};

use liquid_rust_parser::ast;
use crate::{generator::Generator, ty};

pub type ResolveResult<'source, T> = Result<T, ResolveError<'source>>;

#[derive(Debug)]
pub enum ResolveError<'source> {
    BaseMismatch(ty::BaseTy, ty::BaseTy),
    ArityMismatch(usize, usize),
    UnboundedVar(ast::Variable<'source>),
}

pub struct ResolveCtx<'source> {
    vars: Vec<(ast::Variable<'source>, ty::Variable)>,
    var_generator: Rc<RefCell<Generator<ty::Variable>>>,
}

impl<'source> ResolveCtx<'source> {
    pub(crate) fn new(var_generator: Rc<RefCell<Generator<ty::Variable>>>) -> Self {
        Self {
            vars: Vec::new(),
            var_generator,
        }
    }

    fn solve_var(&self, var: ast::Variable<'source>) -> ResolveResult<'source, ty::Variable> {
        for (ast_var, ty_var) in self.vars.iter().rev() {
            if *ast_var == var {
                return Ok(*ty_var);
            }
        }
        Err(ResolveError::UnboundedVar(var))
    }

    pub fn new_variable(&self) -> ty::Variable {
        self.var_generator.borrow_mut().generate()
    }

    fn store_var(&mut self, ast_var: ast::Variable<'source>) -> ty::Variable {
        let var = self.new_variable();
        self.vars.push((ast_var, var));
        var
    }

    fn pop_var(&mut self) {
        self.vars.pop().unwrap();
    }

    pub(crate) fn resolve_ty(&mut self, ast_ty: &ast::Ty<'source>) -> ResolveResult<'source, ty::Ty> {
        match ast_ty {
            ast::Ty::Base(base_ty) => {
                Ok(ty::Ty::Refined(self.new_variable(), *base_ty, true.into()))
            }

            ast::Ty::Refined(var, base_ty, pred) => {
                let var = self.store_var(var.clone());
                let pred = self.resolve_pred(pred)?;
                self.pop_var();
                Ok(ty::Ty::Refined(var, *base_ty, pred))
            }

            ast::Ty::Func(args, ret_ty) => {
                let args = args
                    .iter()
                    .map(|(arg, arg_ty)| {
                        let var = self.store_var(arg.clone());
                        Ok((var, self.resolve_ty(arg_ty)?))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let ret_ty = self.resolve_ty(ret_ty)?;

                for _ in &args {
                    self.pop_var();
                }

                Ok(ty::Ty::Func(args, Box::new(ret_ty)))
            }
        }
    }

    fn resolve_pred(&mut self, pred: &ast::Predicate<'source>) -> ResolveResult<'source, ty::Predicate> {
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
        };

        Ok(pred)
    }
}
