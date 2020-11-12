use crate::{
    ast::{Annotation, Ty as AstTy},
    generator::Generator,
    ir::{Func, FuncId, Local},
    replace::Replace,
    resolve::{ResolveCtx, ResolveError},
    ty::{BaseTy, Ty, Variable},
    tycheck::{Check, Constraint, Synth},
};

use std::{cell::RefCell, collections::HashMap, rc::Rc};

pub struct TyContext {
    funcs_ty: HashMap<FuncId, Ty>,
    funcs: HashMap<FuncId, Func>,
    var_generator: Rc<RefCell<Generator<Variable>>>,
}

impl TyContext {
    pub fn new(
        funcs: HashMap<FuncId, Func>,
        annotations: HashMap<FuncId, Vec<Annotation>>,
    ) -> Result<Self, ResolveError> {
        let mut ctx = Self {
            funcs_ty: HashMap::new(),
            funcs,
            var_generator: Rc::new(RefCell::new(Variable::generator())),
        };

        println!("Type Annotations:");

        for (func_id, anns) in annotations {
            for Annotation::Ty(ast_ty) in anns {
                let ty = ctx.resolve_ty(&ast_ty)?;
                println!("{} : {}", func_id, ty);
                ctx.funcs_ty.insert(func_id, ty);
            }
        }

        for (func_id, ty) in &ctx.funcs_ty {
            let ctx = ctx.at(*func_id);
            let constr = ctx.check(ctx.func(), ty);
            println!("{}", constr);
        }

        Ok(ctx)
    }

    pub fn new_variable(&self) -> Variable {
        self.var_generator.borrow_mut().generate()
    }

    pub(crate) fn at(&self, func_id: FuncId) -> TyContextAt {
        TyContextAt::new(self, func_id)
    }

    fn resolve_ty(&self, ty: &AstTy) -> Result<Ty, ResolveError> {
        let mut rcx = ResolveCtx::new(Rc::clone(&self.var_generator));
        rcx.resolve_ty(ty)
    }
}

struct Env {
    vars: HashMap<Local, Variable>,
    vars_ty: HashMap<Variable, Ty>,
}

pub(crate) struct TyContextAt<'tcx> {
    ctx: &'tcx TyContext,
    func_id: FuncId,
    env: RefCell<Env>,
}

impl<'tcx> TyContextAt<'tcx> {
    fn new(ctx: &'tcx TyContext, func_id: FuncId) -> Self {
        Self {
            ctx,
            func_id,
            env: RefCell::new(Env {
                vars: HashMap::new(),
                vars_ty: HashMap::new(),
            }),
        }
    }

    pub(crate) fn new_variable(&self) -> Variable {
        self.ctx.new_variable()
    }

    pub(crate) fn annotate_variable(&self, var: Variable, ty: Ty) {
        self.env.borrow_mut().vars_ty.insert(var, ty);
    }

    pub(crate) fn annotate_local(&self, local: Local, var: Variable, ty: Ty) {
        let mut env = self.env.borrow_mut();
        env.vars.insert(local, var);
        env.vars_ty.insert(var, ty);
    }

    pub(crate) fn store_local(&self, local: Local) -> Variable {
        let var = self.ctx.new_variable();
        self.env.borrow_mut().vars.insert(local, var);
        var
    }

    pub(crate) fn func(&self) -> &Func {
        self.ctx
            .funcs
            .get(&self.func_id)
            .expect("FuncIds always map to a Func.")
    }

    pub(crate) fn type_of_local(&self, local: &Local) -> Ty {
        let env = self.env.borrow();

        let var = env
            .vars
            .get(local)
            .expect("Locals always map to a variable.");

        env.vars_ty
            .get(var)
            .expect("Variables always have a type.")
            .clone()
    }

    pub(crate) fn type_of_func(&self, func_id: &FuncId) -> Ty {
        self.ctx
            .funcs_ty
            .get(func_id)
            .expect("Orphan FuncId.")
            .clone()
    }

    pub(crate) fn refined(&self, base_ty: BaseTy) -> Ty {
        let var = self.new_variable();
        Ty::RefBase(var, base_ty, true.into())
    }

    pub(super) fn check<T: Check<'tcx>>(&self, term: &T, ty: &Ty) -> Constraint {
        term.check(self, ty)
    }

    pub(super) fn synth<T: Synth<'tcx>>(&self, term: &T) -> (Constraint, Ty) {
        term.synth(self)
    }

    pub(super) fn is_subtype(&self, ty1: &Ty, ty2: &Ty) -> Constraint {
        match (ty1, ty2) {
            (&Ty::RefBase(v1, b1, ref p1), &Ty::RefBase(v2, b2, ref p2)) => {
                if b1 == b2 {
                    let p1 = p1.clone();
                    let mut p2 = p2.clone();
                    p2.replace(v2, v1);
                    Constraint::forall(v1, b1, p1, p2)
                } else {
                    panic!("Base type mismatch")
                }
            }
            _ => todo!(),
        }
    }
}
