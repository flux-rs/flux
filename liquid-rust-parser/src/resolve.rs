use crate::ast::{Predicate as AstPredicate, Ty as AstTy, Variable as AstVariable};

use liquid_rust_common::ty::{self, Argument};

type Variable = ty::Variable<Argument>;
type Predicate = ty::Predicate<Argument>;
type Ty = ty::Ty<Argument>;

#[derive(Default)]
pub(crate) struct ResolveCtx<'source> {
    scopes: Vec<Scope<'source>>,
}

impl<'source> ResolveCtx<'source> {
    pub(crate) fn resolve_ty(&mut self, ast_ty: &AstTy<'source>) -> Ty {
        match ast_ty {
            AstTy::Base(base_ty) => Ty::Refined(*base_ty, true.into()),
            AstTy::Refined(bounded_variable, base_ty, predicate) => {
                self.push_variable(*bounded_variable, Variable::Bounded);

                let predicate = self.resolve_predicate(predicate);

                self.pop_variable();

                Ty::Refined(*base_ty, predicate)
            }
            AstTy::Func(arguments, return_ty) => {
                let level = self.scopes.len();

                self.push_scope();

                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(pos, (ast_argument, ast_ty))| {
                        let ty = self.resolve_ty(ast_ty);

                        let argument = Argument::new(pos, level);
                        self.push_variable(*ast_argument, Variable::Free(argument));

                        (argument, ty)
                    })
                    .collect::<Vec<_>>();

                let return_ty = self.resolve_ty(return_ty.as_ref());

                for _ in 0..arguments.len() {
                    self.pop_variable();
                }

                self.pop_scope();

                Ty::Func(arguments, Box::new(return_ty))
            }
        }
    }

    fn resolve_predicate(&self, ast_predicate: &AstPredicate<'source>) -> Predicate {
        match ast_predicate {
            AstPredicate::Var(variable) => Predicate::Var(self.resolve_variable(*variable)),
            AstPredicate::Lit(literal) => Predicate::Lit(*literal),
            AstPredicate::UnApp(un_op, op) => {
                Predicate::UnApp(*un_op, Box::new(self.resolve_predicate(op.as_ref())))
            }
            AstPredicate::BinApp(bin_op, op1, op2) => Predicate::BinApp(
                *bin_op,
                Box::new(self.resolve_predicate(op1.as_ref())),
                Box::new(self.resolve_predicate(op2.as_ref())),
            ),
        }
    }

    fn scope(&self) -> &Scope<'source> {
        self.scopes
            .last()
            .expect("There should be at least one scope.")
    }

    fn scope_mut(&mut self) -> &mut Scope<'source> {
        self.scopes
            .last_mut()
            .expect("There should be at least one scope.")
    }

    fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop().expect("Stack for scopes is empty.");
    }

    fn resolve_variable(&self, ast_variable: AstVariable<'source>) -> Variable {
        self.scope().resolve_variable(ast_variable)
    }

    fn push_variable(&mut self, ast_variable: AstVariable<'source>, variable: Variable) {
        self.scope_mut().push_variable(ast_variable, variable);
    }

    fn pop_variable(&mut self) {
        self.scope_mut().pop_variable()
    }
}

#[derive(Default)]
struct Scope<'source> {
    stack: Vec<(AstVariable<'source>, Variable)>,
}

impl<'source> Scope<'source> {
    fn push_variable(&mut self, ast_variable: AstVariable<'source>, variable: Variable) {
        self.stack.push((ast_variable, variable));
    }

    fn pop_variable(&mut self) {
        self.stack
            .pop()
            .expect("Stack for the current scope is empty.");
    }

    fn resolve_variable(&self, ast_variable: AstVariable<'source>) -> Variable {
        for (ast_var, variable) in self.stack.iter().rev() {
            if *ast_var == ast_variable {
                return *variable;
            }
        }
        panic!("Variable `{:?}` is not in scope.", ast_variable)
    }
}
