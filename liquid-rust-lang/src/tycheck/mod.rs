mod check;
mod constraint;
mod synth;

use check::Check;
use constraint::Constraint;
use synth::Synth;

use std::collections::HashMap;

use crate::{
    ast::{Annotation, Ty as AstTy},
    generator::Generator,
    ir::{Func, FuncId, Local},
    resolve::{ResolveCtx, ResolveError},
    ty::{Ty, Variable},
};

pub struct TyCtx {
    funcs_ty: HashMap<FuncId, Ty>,
    funcs: HashMap<FuncId, Func>,
    var_gen: Generator<Variable>,
}

impl TyCtx {
    pub fn new(
        funcs: HashMap<FuncId, Func>,
        annotations: HashMap<FuncId, Vec<Annotation>>,
    ) -> Result<Self, ResolveError> {
        let mut tcx = Self {
            funcs_ty: HashMap::new(),
            funcs,
            var_gen: Variable::generator(),
        };

        for (func_id, anns) in annotations {
            for Annotation::Ty(ast_ty) in anns {
                let ty = tcx.resolve_ty(&ast_ty)?;
                println!("{:?} => {:?}", func_id, ty);
                tcx.funcs_ty.insert(func_id, ty);
            }
        }

        Ok(tcx)
    }

    fn resolve_ty(&mut self, ty: &AstTy) -> Result<Ty, ResolveError> {
        let mut rcx = ResolveCtx::new(self);
        rcx.resolve_ty(ty)
    }

    pub(crate) fn new_var(&mut self) -> Variable {
        self.var_gen.generate()
    }

    fn at<'a>(&'a mut self, func_id: FuncId) -> TyCtxAt<'a> {
        TyCtxAt {
            tcx: self,
            func_id,
            vars: HashMap::new(),
            vars_ty: HashMap::new(),
        }
    }
}

pub struct TyCtxAt<'tcx> {
    tcx: &'tcx mut TyCtx,
    func_id: FuncId,
    vars: HashMap<Local, Variable>,
    vars_ty: HashMap<Variable, Ty>,
}

impl<'tcx> TyCtxAt<'tcx> {
    pub(crate) fn new_var(&mut self) -> Variable {
        self.tcx.var_gen.generate()
    }

    fn func(&self) -> &Func {
        self.tcx.funcs.get(&self.func_id).expect("Orphan FuncId.")
    }

    fn check<T: Check<'tcx>>(&mut self, term: &T, ty: &Ty) -> Constraint {
        term.check(self, ty)
    }

    fn synth<T: Synth<'tcx>>(&mut self, term: &T) -> (Constraint, Ty) {
        term.synth(self)
    }
}

// impl<'func> FnContext<'func> {
//     fn sub(&mut self, ty1: &Ty, ty2: &Ty) -> Constraint {
//         match (ty1, ty2) {
//             (Ty::RefBase(v1, b1, p1), Ty::RefBase(v2, b2, p2)) if b1 == b2 => {
//                 let v1 = *v1;
//                 let v2 = *v2;
//                 let b = *b1;
//                 let p1 = p1.clone();
//                 let mut p2 = p2.clone();
//                 p2.replace(v2, v1);
//
//                 Constraint::Impl(v1, b, p1, Box::new(Constraint::Pred(p2)))
//             }
//             (Ty::RefFunc(args1, ret_ty1), Ty::RefFunc(args2, ret_ty2)) => {
//                 let arity = args1.len();
//                 assert_eq!(arity, args2.len(), "Arity mismatch for subtyping");
//
//                 let mut args1 = args1.clone();
//                 let mut args2 = args1.clone();
//
//                 let mut ret_ty1 = *ret_ty1.clone();
//
//                 for i in 0..arity {
//                     let (arg1, _) = args1[i];
//                     let (arg2, _) = args2[i];
//
//                     for j in (i + 1)..arity {
//                         let (_, arg_ty1) = &mut args1[j];
//                         arg_ty1.replace(arg1, arg2);
//                     }
//
//                     ret_ty1.replace(arg1, arg2);
//                 }
//
//                 let mut c0 = self.sub(&ret_ty1, ret_ty2.as_ref());
//
//                 for _ in 0..arity {
//                     let (_, arg_ty1) = args1.pop().unwrap();
//                     let (arg2, arg_ty2) = args2.pop().unwrap();
//
//                     let c1 = self.sub(&arg_ty2, &arg_ty1);
//
//                     c0 = Constraint::Conj(
//                         Box::new(c1),
//                         Box::new(Constraint::implication(arg2, arg_ty2, c0)),
//                     )
//                 }
//
//                 c0
//             }
//             _ => panic!("incompatible types for subtyping"),
//         }
//     }
//
//     fn check<T: Check<'func>>(&mut self, term: &T, ty: &Ty) -> Constraint {
//         term.check(self, ty)
//     }
//
//     fn synth<T: Synth<'func>>(&mut self, term: &T) -> (Constraint, Ty) {
//         term.synth(self)
//     }
// }
