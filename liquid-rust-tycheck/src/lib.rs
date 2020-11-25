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
    ty::{self, BaseTy},
};
use liquid_rust_fixpoint::{Emit, Emitter};

use std::{cell::RefCell, fmt};

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
    let mut emitter = Emitter::new();

    for (func_id, func) in program.iter() {
        if func.user_ty() {
            emitter = GlobEnv::new(program, func_id, emitter).check();
        }
    }

    emitter.emit().unwrap();
}

struct GlobEnv<'prog> {
    #[allow(dead_code)]
    program: &'prog Program,
    func_id: FuncId,
    func: &'prog Func,
    emitter: RefCell<Emitter<GlobVariable>>,
}

impl<'prog> GlobEnv<'prog> {
    fn new(program: &'prog Program, func_id: FuncId, emitter: Emitter<GlobVariable>) -> Self {
        Self {
            program,
            func_id,
            func: program.get_func(func_id),
            emitter: RefCell::new(emitter),
        }
    }

    fn get_bblock(&self, bb_id: BBlockId) -> &BBlock {
        self.func.get_bblock(bb_id)
    }

    fn check(self) -> Emitter<GlobVariable> {
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
                let return_var = types.insert(return_ty.clone());
                assert_eq!(Local::first(), variables.insert(return_var));

                match return_ty.map(|var| GlobVariable(self.func_id, var)) {
                    ty::Ty::Refined(base_ty, predicate) => self.emitter.borrow_mut().add_bind(
                        GlobVariable(self.func_id, return_var),
                        base_ty,
                        predicate,
                    ),
                    ty::Ty::Func(..) => (),
                };

                for ((_, ann_ty), (local, base_ty)) in args_ann_ty.iter().zip(self.func.arguments())
                {
                    assert!(
                        base_ty.refined::<LocalVariable>().shape_eq(ann_ty),
                        "Argument type shape mismatch."
                    );

                    let arg_ty = ann_ty
                        .clone()
                        .map(|arg| *variables.get(arg.as_local().unwrap()));
                    let arg_var = types.insert(arg_ty.clone());
                    assert_eq!(local, variables.insert(arg_var));

                    match arg_ty.map(|var| GlobVariable(self.func_id, var)) {
                        ty::Ty::Refined(base_ty, predicate) => self.emitter.borrow_mut().add_bind(
                            GlobVariable(self.func_id, arg_var),
                            base_ty,
                            predicate,
                        ),
                        ty::Ty::Func(..) => (),
                    };
                }

                for (local, base_ty) in self.func.temporaries() {
                    let ty = base_ty.refined();
                    let variable = types.insert(ty.clone());
                    assert_eq!(local, variables.insert(variable));

                    match ty.map(|var| GlobVariable(self.func_id, var)) {
                        ty::Ty::Refined(base_ty, predicate) => self.emitter.borrow_mut().add_bind(
                            GlobVariable(self.func_id, variable),
                            base_ty,
                            predicate,
                        ),
                        ty::Ty::Func(..) => (),
                    };
                }

                let return_ty = return_ann_ty
                    .clone()
                    .map(|arg| *variables.get(arg.as_local().unwrap()));

                let mut env = Env::new(variables, types);

                self.func
                    .get_bblock(BBlockId::first())
                    .check(&self, &mut env, &return_ty)
                    .unwrap();

                self.emitter.into_inner()
            }
            _ => {
                panic!("Expected function type.")
            }
        }
    }

    fn emit_constraint(&self, base_ty: BaseTy, predicate1: &Predicate, predicate2: &Predicate) {
        let mut emitter = self.emitter.borrow_mut();
        emitter.add_constraint(
            base_ty,
            predicate1
                .clone()
                .map(|var| GlobVariable(self.func_id, var)),
            predicate2
                .clone()
                .map(|var| GlobVariable(self.func_id, var)),
        );
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

    fn annotate_local(&mut self, genv: &GlobEnv, local: Local, ty: Ty) {
        let variable = self.types.insert(ty.clone());
        *self.variables.get_mut(local) = variable;

        match ty.map(|var| GlobVariable(genv.func_id, var)) {
            ty::Ty::Refined(base_ty, predicate) => genv.emitter.borrow_mut().add_bind(
                GlobVariable(genv.func_id, variable),
                base_ty,
                predicate,
            ),
            ty::Ty::Func(..) => (),
        };
    }

    fn is_subtype(&self, genv: &GlobEnv, ty1: &Ty, ty2: &Ty) -> TyResult {
        match (ty1, ty2) {
            // Sub-Base
            (Ty::Refined(base_ty1, predicate1), Ty::Refined(base_ty2, predicate2)) => {
                if base_ty1 != base_ty2 {
                    return Err(TyError::BaseMismatch(*base_ty1, *base_ty2));
                }
                genv.emit_constraint(*base_ty1, predicate1, predicate2);

                Ok(())
            }
            (Ty::Func(_, _), Ty::Func(_, _)) => {
                todo!()
            }
            _ => Err(TyError::ShapeMismatch(ty1.clone(), ty2.clone())),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
struct GlobVariable(FuncId, LocalVariable);

impl Emit for GlobVariable {
    fn emit<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        write!(writer, "{}_{}", self.0, self.1)
    }
}
