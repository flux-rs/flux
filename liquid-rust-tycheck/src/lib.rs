mod check;
mod result;
mod synth;

use check::Check;
use result::{TyError, TyResult};
use synth::Synth;

use liquid_rust_common::{
    def_index,
    index::{Index, IndexMap},
    ir::{BBlock, BBlockId, Func, FuncId, Local, Operand, Program},
    ty,
};

use std::fmt;

def_index!(LocalVariable);

impl fmt::Display for LocalVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}

type Variable = ty::Variable<LocalVariable>;
type Predicate = ty::Predicate<LocalVariable>;
type Ty = ty::Ty<LocalVariable>;

pub fn check_program(program: &Program) {
    for (func_id, func) in program.iter() {
        if func.user_ty() {
            GlobEnv::new(program, func_id).check();
        }
    }
}

struct GlobEnv<'prog> {
    #[allow(dead_code)]
    program: &'prog Program,
    func: &'prog Func,
}

impl<'prog> GlobEnv<'prog> {
    fn new(program: &'prog Program, func_id: FuncId) -> Self {
        Self {
            program,
            func: program.get_func(func_id),
        }
    }

    fn get_bblock(&self, bb_id: BBlockId) -> &BBlock {
        self.func.get_bblock(bb_id)
    }

    fn check(self) {
        match self.func.ty() {
            ty::Ty::Func(args_ann_ty, return_ann_ty) => {
                assert_eq!(args_ann_ty.len(), self.func.arity(), "Arity mismatch.");

                let mut variables = Local::index_map();
                let mut types = LocalVariable::index_map();

                let return_ty: Ty = self.func.return_ty().refined();

                assert!(
                    return_ann_ty.shape_eq(&return_ty),
                    "Return type shape mismatch."
                );
                let return_var = types.insert(return_ty);
                assert_eq!(Local::first(), variables.insert(return_var));

                for ((_, ann_ty), (local, base_ty)) in args_ann_ty.iter().zip(self.func.arguments())
                {
                    assert!(
                        base_ty.refined::<LocalVariable>().shape_eq(ann_ty),
                        "Argument type shape mismatch."
                    );

                    let arg_ty = ann_ty
                        .clone()
                        .map(|arg| *variables.get(arg.as_local().unwrap()));
                    let arg_var = types.insert(arg_ty);
                    assert_eq!(local, variables.insert(arg_var));
                }

                for (local, base_ty) in self.func.temporaries() {
                    let variable = types.insert(base_ty.refined());
                    assert_eq!(local, variables.insert(variable));
                }

                let return_ty = return_ann_ty
                    .clone()
                    .map(|arg| *variables.get(arg.as_local().unwrap()));

                let mut env = Env::new(variables, types);

                self.func
                    .get_bblock(BBlockId::first())
                    .check(&self, &mut env, &return_ty)
                    .unwrap();
            }
            _ => {
                panic!("Expected function type.")
            }
        }
    }
}

struct Env {
    variables: IndexMap<Local, LocalVariable>,
    types: IndexMap<LocalVariable, Ty>,
}

impl Env {
    fn new(variables: IndexMap<Local, LocalVariable>, types: IndexMap<LocalVariable, Ty>) -> Self {
        Self { variables, types }
    }

    fn get_ty(&self, variable: LocalVariable) -> &Ty {
        self.types.get(variable)
    }

    fn resolve_local(&self, local: Local) -> LocalVariable {
        *self.variables.get(local)
    }

    fn resolve_operand(&self, operand: &Operand) -> Predicate {
        match operand {
            Operand::Local(local) => Predicate::Var(Variable::Free(self.resolve_local(*local))),
            Operand::Literal(literal) => Predicate::Lit(*literal),
        }
    }

    fn annotate_local(&mut self, local: Local, ty: Ty) {
        let variable = self.types.insert(ty);
        *self.variables.get_mut(local) = variable;
    }

    fn is_subtype(&self, ty1: &Ty, ty2: &Ty) -> TyResult {
        match (ty1, ty2) {
            // Sub-Base
            (Ty::Refined(base_ty1, predicate1), Ty::Refined(base_ty2, predicate2)) => {
                if base_ty1 != base_ty2 {
                    return Err(TyError::BaseMismatch(*base_ty1, *base_ty2));
                }
                self.emit_constraint(predicate1, predicate2);
                Ok(())
            }
            (Ty::Func(_, _), Ty::Func(_, _)) => {
                todo!()
            }
            _ => Err(TyError::ShapeMismatch(ty1.clone(), ty2.clone())),
        }
    }

    fn emit_constraint(&self, predicate1: &Predicate, predicate2: &Predicate) {
        // println!();
        //
        // for (i, (var, ty)) in self.types.iter().enumerate() {
        //     if let Ty::Refined(b, p) = ty {
        //         let base = match b {
        //             ty::BaseTy::Int(_) | ty::BaseTy::Uint(_) => "int",
        //             ty::BaseTy::Bool => "bool",
        //             _ => panic!(),
        //         };
        //         println!("bind {} {} : {{b : {} | {}}}", i, var, base, p)
        //     }
        // }
        //
        println!("{} => {}", predicate1, predicate2);
    }
}
