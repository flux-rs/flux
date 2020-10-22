pub mod ast;
mod checking;
mod common;
pub mod parser;
mod synthesis;
pub mod ty;

use rustc_index::vec::IndexVec;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyCtxt;

use std::collections::HashMap;

use checking::Checking;
use synthesis::Synthesis;

pub struct Context<'tcx> {
    var_generator: Generator<ty::Variable>,
    vars: Vec<(ast::Variable, ty::Variable)>,
    ty_vars: HashMap<ty::Variable, ty::RefinedTy>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Context<'tcx> {
    pub fn from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            var_generator: ty::Variable::generator(),
            vars: vec![],
            ty_vars: HashMap::default(),
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

struct FnContext<'tcx> {
    ctx: &'tcx mut Context<'tcx>,
    vars: IndexVec<Local, ty::Variable>,
}

impl<'tcx> FnContext<'tcx> {
    fn synth(&mut self, t: impl Synthesis<'tcx>) -> (ty::Constraint, ty::RefinedTy) {
        t.synth(self)
    }

    fn check(&mut self, t: impl Checking<'tcx>, ty: &ty::RefinedTy) -> ty::Constraint {
        t.check(self, ty)
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
