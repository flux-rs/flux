use crate::{
    check::Check,
    env::Env,
    ty::{GlobVariable, LocalVariable, Predicate, Ty, Variable},
};

use liquid_rust_common::index::Index;
use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{BBlock, BBlockId, Func, FuncId, Local, Program};

pub struct GlobEnv<'prog> {
    #[allow(dead_code)]
    program: &'prog Program<LocalVariable>,
    func_id: FuncId,
    func: &'prog Func<LocalVariable>,
}

impl<'prog> GlobEnv<'prog> {
    pub fn new(program: &'prog Program<LocalVariable>, func_id: FuncId) -> Self {
        Self {
            program,
            func_id,
            func: program.get_func(func_id),
        }
    }

    pub fn get_bblock(&self, bb_id: BBlockId) -> &BBlock {
        self.func.get_bblock(bb_id)
    }

    pub fn get_func(&self, func_id: FuncId) -> &Func<LocalVariable> {
        self.program.get_func(func_id)
    }

    pub fn check(self, mut emitter: Emitter<GlobVariable>) -> Emitter<GlobVariable> {
        let arity = self.func.ty().arguments().len();
        assert_eq!(arity, self.func.arity());

        let ann_ty = self.func.ty().clone().project_args(|pos| {
            Predicate::Var(Variable::Free(LocalVariable::constructor(pos + 1)))
        });

        let args_ann_ty = ann_ty.arguments();
        let return_ann_ty = ann_ty.return_ty();

        let mut variables = Local::index_map();
        let mut types = LocalVariable::index_map();

        let return_ty = self.func.return_ty().refined();
        let return_var = types.insert(return_ty.clone());
        let return_local = variables.insert(return_var);
        assert_eq!(Local::first(), return_local);

        assert!(
            return_ann_ty.shape_eq(&return_ty),
            "Return type shape mismatch."
        );

        let mapper = GlobVariable::mapper(self.func_id);

        match return_ty {
            Ty::Refined(base_ty, pred) => {
                emitter.add_bind(mapper(return_var), base_ty, pred.map(mapper))
            }
            Ty::Func(..) => todo!(),
        }

        for (ann_ty, (local, base_ty)) in args_ann_ty.iter().zip(self.func.arguments()) {
            let ty = base_ty.refined();
            assert!(ty.shape_eq(ann_ty), "Argument type shape mismatch.");

            let variable = types.insert(ann_ty.clone());
            assert_eq!(local, variables.insert(variable));

            match ann_ty {
                Ty::Refined(base_ty, pred) => {
                    emitter.add_bind(mapper(variable), *base_ty, pred.clone().map(mapper))
                }
                Ty::Func(..) => todo!(),
            }
        }

        for (local, base_ty) in self.func.temporaries() {
            let ty = base_ty.refined();

            let variable = types.insert(ty.clone());
            assert_eq!(local, variables.insert(variable));

            match ty {
                Ty::Refined(base_ty, pred) => {
                    emitter.add_bind(mapper(variable), base_ty, pred.map(mapper))
                }
                Ty::Func(..) => todo!(),
            }
        }

        let mut env = Env::new(self.func_id, variables, types, emitter);

        self.func
            .get_bblock(BBlockId::first())
            .check(&self, &mut env, &return_ann_ty)
            .unwrap();

        env.emitter()
    }
}
