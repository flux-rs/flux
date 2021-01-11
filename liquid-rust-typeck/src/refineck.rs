use std::collections::HashMap;

use crate::{
    constraint::Constraint,
    subtyping::{infer_subst, subtyping},
};
use ast::{FnBody, StatementKind};
use liquid_rust_core::{
    ast::{self, ContDef, FnDef, Place, Statement},
    names::ContId,
    ty::{self, ContTy, TyCtxt},
};
use ty::pred;

use crate::{env::Env, synth::Synth};

pub struct RefineChecker<'a> {
    conts: &'a HashMap<ContId, ContTy>,
    tcx: &'a TyCtxt,
}

impl<'a> RefineChecker<'a> {
    pub fn new(tcx: &'a TyCtxt, conts: &'a HashMap<ContId, ContTy>) -> Self {
        Self { tcx, conts }
    }

    pub fn check_fn_def<I>(mut self, func: &FnDef<I>, fn_ty: &ty::FnTy) -> Constraint {
        let mut env = Env::new(self.tcx);
        env.insert_locals(fn_ty.locals(&func.params));
        env.extend_heap(&fn_ty.in_heap);

        Constraint::from_bindings(
            fn_ty.in_heap.bindings(),
            self.check_body(&mut env, &func.body),
        )
    }

    pub fn check_body<I>(&mut self, env: &mut Env, body: &FnBody<I>) -> Constraint {
        match body {
            FnBody::LetCont(defs, rest) => {
                let mut vec = Vec::new();
                for def in defs {
                    vec.push(self.check_cont_def(env, def));
                }
                vec.push(self.check_body(env, rest));
                Constraint::Conj(vec)
            }
            FnBody::Ite { discr, then, else_ } => {
                let snapshot = env.snapshot();
                let c1 = self.check_body(env, then);
                env.rollback_to(snapshot);
                let c2 = self.check_body(env, else_);

                let discr = self.tcx.mk_pred_place(env.resolve_place(discr));
                Constraint::Conj(vec![
                    Constraint::guard(&discr, c1),
                    Constraint::guard(&self.tcx.mk_un_op(ty::UnOp::Not, discr), c2),
                ])
            }
            FnBody::Call { .. } => todo!(),
            FnBody::Jump { target, args } => {
                let cont_ty = &self.conts[target];

                let heap1 = env.heap();
                let locals1 = env.locals();
                let heap2 = &cont_ty.heap;
                let locals2 = &cont_ty.locals(args);

                let subst = infer_subst(heap1, locals1, heap2, locals2);
                let heap2 = &subst.apply(self.tcx, heap2);
                let locals2 = subst.apply(self.tcx, locals2);

                Constraint::Conj(
                    locals2
                        .into_iter()
                        .map(|(x, l)| {
                            let ty1 = &self
                                .tcx
                                .selfify(&env.lookup(&Place::from(x)), pred::Place::from(l));
                            let ty2 = &heap2[&l];
                            subtyping(self.tcx, heap1, ty1, heap2, ty2)
                        })
                        .collect(),
                )
            }
            FnBody::Seq(stmnt, rest) => {
                let (c, bindings) = env.capture_bindings(|env| self.check_stmnt(env, stmnt));
                Constraint::Conj(vec![
                    Constraint::from_bindings(bindings, self.check_body(env, rest)),
                    c,
                ])
            }
            FnBody::Abort => Constraint::True,
        }
    }

    fn check_cont_def<I>(&mut self, env: &mut Env, def: &ContDef<I>) -> Constraint {
        let snapshot = env.snapshot_without_locals();

        let cont_ty = &self.conts[&def.name];
        let bindings = cont_ty.heap.bindings();
        env.insert_locals(cont_ty.locals(&def.params));
        env.extend_heap(&cont_ty.heap);
        let c = self.check_body(env, &def.body);

        env.rollback_to(snapshot);
        Constraint::from_bindings(bindings, c)
    }

    fn check_stmnt<I>(&mut self, env: &mut Env, stmnt: &Statement<I>) -> Constraint {
        match &stmnt.kind {
            StatementKind::Let(x, layout) => {
                env.alloc(*x, self.tcx.mk_ty_for_layout(layout));
                Constraint::True
            }
            StatementKind::Assign(place, rvalue) => {
                let ty = rvalue.synth(self.tcx, env);
                env.update(place, ty);
                Constraint::True
            }
            StatementKind::Drop(x) => env.drop(x),
            StatementKind::Nop => Constraint::True,
        }
    }
}
