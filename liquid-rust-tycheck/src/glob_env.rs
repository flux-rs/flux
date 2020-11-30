use crate::{
    check::Check,
    env::Env,
    ty::{GlobVariable, LocalVariable, Ty},
};

use liquid_rust_common::index::Index;
use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{BBlock, BBlockId, Func, FuncId, Local, Program};
use liquid_rust_ty as ty;

pub struct GlobEnv<'prog> {
    #[allow(dead_code)]
    program: &'prog Program,
    func_id: FuncId,
    func: &'prog Func,
}

impl<'prog> GlobEnv<'prog> {
    pub fn new(program: &'prog Program, func_id: FuncId) -> Self {
        Self {
            program,
            func_id,
            func: program.get_func(func_id),
        }
    }

    pub fn get_bblock(&self, bb_id: BBlockId) -> &BBlock {
        self.func.get_bblock(bb_id)
    }

    pub fn check(self, mut emitter: Emitter<GlobVariable>) -> Emitter<GlobVariable> {
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
                    ty::Ty::Refined(base_ty, predicate) => {
                        emitter.add_bind(GlobVariable(self.func_id, return_var), base_ty, predicate)
                    }
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
                        .map(|arg| *variables.get(Local::try_from_argument(arg).unwrap()));
                    let arg_var = types.insert(arg_ty.clone());
                    assert_eq!(local, variables.insert(arg_var));

                    match arg_ty.map(|var| GlobVariable(self.func_id, var)) {
                        ty::Ty::Refined(base_ty, predicate) => emitter.add_bind(
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
                        ty::Ty::Refined(base_ty, predicate) => emitter.add_bind(
                            GlobVariable(self.func_id, variable),
                            base_ty,
                            predicate,
                        ),
                        ty::Ty::Func(..) => (),
                    };
                }

                let return_ty = return_ann_ty
                    .clone()
                    .map(|arg| *variables.get(Local::try_from_argument(arg).unwrap()));

                let mut env = Env::new(self.func_id, variables, types, emitter);

                self.func
                    .get_bblock(BBlockId::first())
                    .check(&self, &mut env, &return_ty)
                    .unwrap();

                env.emitter()
            }
            _ => {
                panic!("Expected function type.")
            }
        }
    }
}
