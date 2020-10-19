pub mod ast;
mod common;
pub mod parser;
pub mod ty;

use rustc_middle::{mir::Local, ty::TyCtxt};

pub struct Context<'tcx> {
    var_generator: Generator<ty::Variable>,
    vars: Vec<(ast::Variable, ty::Variable)>,
    locals: Vec<(ty::Variable, Local)>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Context<'tcx> {
    pub fn from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            var_generator: ty::Variable::generator(),
            vars: vec![],
            locals: vec![],
            tcx,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn new_var(&mut self) -> ty::Variable {
        self.var_generator.generate()
    }

    fn get_var(&self, var: ast::Variable) -> ty::Variable {
        for (ast_var, ty_var) in self.vars.iter().rev() {
            if *ast_var == var {
                return *ty_var;
            }
        }

        panic!()
    }

    fn store_var(&mut self, ast_var: ast::Variable) -> ty::Variable {
        let var = self.new_var();
        self.vars.push((ast_var, var));

        var
    }

    fn tag_local(&mut self, var: ty::Variable, local: Local) {
        self.locals.push((var, local));
    }

    fn is_well_formed(&mut self, ty: &ty::RefinedTy) -> bool {
        todo!()
    }

    fn is_valid(&mut self, constr: &ty::Constraint) -> bool {
        todo!()
    }

    fn is_subtype(&mut self, ty1: &ty::RefinedTy, ty2: ty::RefinedTy) -> bool {
        todo!()
    }
}

pub struct Generator<T> {
    count: usize,
    mapper: fn(usize) -> T,
}

impl<T> Generator<T> {
    pub fn new(mapper: fn(usize) -> T) -> Self {
        Self { count: 0, mapper }
    }

    pub fn generate(&mut self) -> T {
        let t = (self.mapper)(self.count);
        self.count += 1;
        t
    }
}
