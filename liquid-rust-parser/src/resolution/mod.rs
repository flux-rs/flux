//! Types and functions related to AST solving.
mod scope;
mod solve;

use scope::Scope;
use solve::Solve;
pub use solve::{ResolutionError, ResolutionErrorKind, ResolutionResult};

use crate::ast::{Ident, Ty as AstTy, TyKind as AstTyKind};

use liquid_rust_mir::ty::{Argument, BaseTy, FuncTy, Predicate, Ty};

/// Solve an AST representation of a type into a well-formed type.
pub fn solve_ty<'source>(ast_ty: &AstTy<'source>) -> ResolutionResult<'source, Ty> {
    ResolutionCtx::new().solve_ty(ast_ty)
}

/// A context used to solve AST terms into unambigous well-formed terms.
struct ResolutionCtx<'source> {
    /// A stack with the scopes introduced by each dependent function type.
    scopes: Vec<Scope<'source>>,
}

impl<'source> ResolutionCtx<'source> {
    /// Create a new empty resolution context.
    fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    /// Return an iterator of the existing scopes with their respective de Bruijn indices, i.e. the
    /// innermost scope has index 0.
    fn scopes(&mut self) -> impl Iterator<Item = (usize, &Scope<'source>)> {
        self.scopes.iter().rev().enumerate()
    }

    /// Return the innermost scope.
    ///
    /// This function panics if the stack with the scopes is empty.
    fn scope_mut(&mut self) -> &mut Scope<'source> {
        self.scopes
            .last_mut()
            .expect("There should be at least one scope.")
    }

    /// Push a new empty scope.
    fn push_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    /// Pop the innermost scope.
    ///
    /// This function panics if the stack with the scopes is empty.
    fn pop_scope(&mut self) {
        self.scopes.pop().expect("Stack for scopes is empty.");
    }

    /// Bind an identifier in the innermost scope.
    ///
    /// This function panics if the stack with the scopes is empty.
    fn bind_ident(&mut self, ident: &Ident<'source>, predicate: Predicate, base_ty: BaseTy) {
        self.scope_mut().bind_ident(ident, predicate, base_ty);
    }
    /// Free the latest bound identifier.
    ///
    /// This function panics if the stack with the scopes is empty.
    fn free_ident(&mut self) {
        self.scope_mut().free_ident()
    }

    /// Solve an AST term.
    fn solve<T: Solve<'source>>(
        &mut self,
        term: &T,
    ) -> ResolutionResult<'source, (T::Output, BaseTy)> {
        term.solve(self)
    }

    /// Solve an AST representation of a type into a concrete type.
    fn solve_ty(&mut self, ast_ty: &AstTy<'source>) -> ResolutionResult<'source, Ty> {
        match &ast_ty.kind {
            // solving an unrefined base type is just refining it with the `true` predicate.
            AstTyKind::Base(base_ty) => Ok(base_ty.refined()),
            AstTyKind::Refined(ident, base_ty, ast_pred) => {
                // bind the ident as the bound variable of the predicate in the current scope.
                self.bind_ident(ident, Predicate::Bound, *base_ty);
                // solve the predicate.
                let (predicate, ty) = self.solve(ast_pred)?;
                // if the predicate is not boolean, return an error.
                if ty != BaseTy::Bool {
                    return ResolutionErrorKind::NonBoolPredicate.into_err(ast_pred.span.clone());
                }
                // free the ident.
                self.free_ident();

                Ok(Ty::Refined(*base_ty, predicate))
            }
            AstTyKind::Func(arguments, return_ty) => {
                // Introduce a new scope.
                self.push_scope();

                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(pos, (ident, ast_ty))| {
                        // Solve the type of the argument before binding the argument because the
                        // latter cannot appear in the former.
                        let arg_ty = self.solve_ty(ast_ty)?;
                        // Liquid rust does not support higher-order functions yet. Return an error
                        // if the type of the argument is not a refined base type.
                        let base_ty = if let Some(base_ty) = arg_ty.get_base() {
                            base_ty
                        } else {
                            return ResolutionErrorKind::FuncArgument.into_err(ast_ty.span.clone());
                        };
                        // Bind the argument's identifier.
                        self.bind_ident(ident, Predicate::Arg(Argument::new(pos)), base_ty);

                        Ok(arg_ty)
                    })
                    .collect::<ResolutionResult<Vec<_>>>()?;
                // Solve the return type of the function.
                let return_ty = self.solve_ty(return_ty.as_ref())?;
                // Free all the arguments (this is not mandatory, we can skip this for performance).
                for _ in 0..arguments.len() {
                    self.free_ident();
                }
                // Remove the current scope.
                self.pop_scope();

                Ok(Ty::Func(FuncTy::new(arguments, return_ty)))
            }
        }
    }
}
