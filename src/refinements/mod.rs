pub mod ast;
mod common;
pub mod parser;
pub mod ty;

use std::collections::HashMap;

use ty::{Constraint, RefinedTy, Variable};

pub struct Context {
    vars: HashMap<Variable, RefinedTy>,
}

impl Context {
    fn is_well_formed(&mut self, ty: &RefinedTy) -> bool {
        todo!()
    }

    fn is_valid(&mut self, constr: &Constraint) -> bool {
        todo!()
    }

    fn is_subtype(&mut self, ty1: &RefinedTy, ty2: RefinedTy) -> bool {
        todo!()
    }
}
