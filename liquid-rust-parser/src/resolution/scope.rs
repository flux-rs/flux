use liquid_rust_ty::{BaseTy, Variable};

use crate::ast::Ident;

/// A lexical scope.
///
/// This is an stack-backed representation of the scope created by either a refined base type or a
/// dependent function type.
pub struct Scope<'source> {
    stack: Vec<(&'source str, Variable, BaseTy)>,
}

impl<'source> Scope<'source> {
    /// Create an empty scope.
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    /// Bind an identifier to an specific variable and type.
    ///
    /// This identifier is pushed onto the top of the stack.
    pub fn bind_ident(&mut self, ident: &Ident<'source>, variable: Variable, base_ty: BaseTy) {
        self.stack.push((ident.symbol, variable, base_ty));
    }

    /// Free the identifier at the top of the scope's stack.
    ///
    /// This function panics if the scope is empty.
    pub fn free_ident(&mut self) {
        self.stack
            .pop()
            .expect("Stack for the current scope is empty.");
    }

    /// Get the variable and type for an identifier. Return `None` if the identifier is not in
    /// scope.
    ///
    /// If there is more than one variable for the same identifier, the latest bind done takes
    /// precedence.
    pub fn solve_ident(&self, ident: &Ident<'source>) -> Option<(Variable, BaseTy)> {
        for (symbol, variable, base_ty) in self.stack.iter().rev() {
            if symbol == &ident.symbol {
                return Some((*variable, *base_ty));
            }
        }
        None
    }
}
