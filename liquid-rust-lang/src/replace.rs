use crate::ty::{Predicate, Ty, Variable};

pub trait Replace {
    fn replace(&mut self, y: Variable, z: Variable);
}

impl Replace for Ty {
    fn replace(&mut self, y: Variable, z: Variable) {
        match self {
            Ty::Refined(v, _, p) => {
                if *v != y {
                    p.replace(y, z);
                }
            }
            Ty::Func(args, ret_ty) => {
                for (arg, arg_ty) in args {
                    arg_ty.replace(y, z);
                    if *arg == y {
                        return;
                    }
                }
                ret_ty.replace(y, z);
            }
        }
    }
}

impl Replace for Predicate {
    fn replace(&mut self, y: Variable, z: Variable) {
        match self {
            Predicate::Var(var) => {
                if *var == y {
                    *var = z;
                }
            }
            Predicate::Lit(_) => {}
            Predicate::BinApp(_, op1, op2) => {
                op1.replace(y, z);
                op2.replace(y, z);
            }
            Predicate::UnApp(_, op) => {
                op.replace(y, z);
            }
            Predicate::App(func, args) => {
                if *func == y {
                    *func = z;
                }
                for arg in args {
                    arg.replace(y, z);
                }
            }
        }
    }
}
