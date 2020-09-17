use std::collections::HashMap;

use super::{ast::*, context::LiquidRustCtxt};

struct TyCtxt<'lr> {
    heap: HashMap<Location, Ty<'lr>>,
    env: HashMap<Local, OwnRef>,
    cx: &'lr LiquidRustCtxt<'lr>,
}

impl<'lr> TyCtxt<'lr> {
    pub fn new(cx: &'lr LiquidRustCtxt<'lr>, heap: &Heap<'lr>, env: &Env) -> Self {
        Self {
            heap: heap.iter().copied().collect(),
            env: env.iter().copied().collect(),
            cx,
        }
    }

    pub fn init_from_fn_def(cx: &'lr LiquidRustCtxt<'lr>, fn_def: &FnDef<'lr>) -> Self {
        TyCtxt::new(cx, &fn_def.heap, &fn_def.args)
    }

    pub fn lookup(&self, place: &Place) -> (Pred<'lr>, Ty<'lr>) {
        let OwnRef(l) = self.env[&place.local];
        let typ = self.heap[&l];
        let pred = self.cx.mk_place(l.into(), &place.projection);
        (pred, typ.project(&place.projection))
    }

    pub fn update(&mut self, place: &Place, typ: Ty<'lr>) {
        let OwnRef(l) = self.env[&place.local];
        let fresh_l = self.fresh_location();
        let t1 = self.heap[&l];
        let t2 = t1.update_at(self.cx, &place.projection, typ);
        self.heap.insert(fresh_l, t2);
        self.env.insert(place.local, OwnRef(fresh_l));
    }

    pub fn alloc(&mut self, x: Local, layout: &TypeLayout) {
        let l = self.fresh_location();
        self.env.insert(x, OwnRef(l));
        self.heap.insert(l, self.cx.mk_ty_for_layout(layout));
    }

    pub fn fresh_location(&self) -> Location {
        // TODO: actually return a fresh location
        Location(Symbol::intern("l"))
    }

    fn can_call(&self, env: &Env, args: &[Local]) -> Result<(), String> {
        for local in args {
            if !self.env.contains_key(local) {
                return Result::Err(format!("Missing local {:?}", local));
            }
            if env.iter().find(|x| x.0 == *local).is_some() {
                return Result::Err(format!("Argument already moved {:?}", local));
            }
        }
        for (local, _) in env {
            if !self.env.contains_key(local) {
                return Result::Err(format!("Missing local {:?}", local));
            }
        }
        return Ok(());
    }
}

pub struct TypeCk<'a, 'b, 'lr> {
    tcx: TyCtxt<'lr>,
    kenv: &'a mut HashMap<Symbol, Cont<'b, 'lr>>,
    cx: &'lr LiquidRustCtxt<'lr>,
    errors: Vec<String>,
}

impl<'b, 'lr> TypeCk<'_, 'b, 'lr> {
    pub fn check(cx: &'lr LiquidRustCtxt<'lr>, fn_def: &FnDef<'lr>) -> Result<(), String> {
        let mut kenv = HashMap::default();
        let env = vec![];
        kenv.insert(
            fn_def.ret,
            Cont {
                heap: &fn_def.out_heap,
                env: &env,
                params: vec![fn_def.out_ty],
            },
        );
        let mut checker = TypeCk {
            tcx: TyCtxt::init_from_fn_def(cx, fn_def),
            kenv: &mut kenv,
            errors: vec![],
            cx,
        };
        checker.wt_fn_body(&fn_def.body);
        if checker.errors.is_empty() {
            Ok(())
        } else {
            Err(format!("{:?}", checker.errors))
        }
    }

    fn wt_operand(&self, operand: &Operand) -> (Pred<'lr>, Ty<'lr>) {
        match operand {
            Operand::Deref(place) => self.tcx.lookup(place),
            Operand::Constant(c) => {
                let pred = self
                    .cx
                    .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_const(*c));
                (
                    self.cx.mk_const(*c),
                    self.cx.mk_refine(Var::nu(), c.ty(), pred),
                )
            }
        }
    }

    fn wt_binop(&mut self, op: BinOp, rhs: &Operand, lhs: &Operand) -> Ty<'lr> {
        let (p1, t1) = self.wt_operand(lhs);
        let (p2, t2) = self.wt_operand(rhs);
        if !t1.is_int() || !t2.is_int() {
            self.errors.push(format!(
                "Cannot use operator `{:?}` with non integer types",
                op
            ));
        }
        let pred = self
            .cx
            .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_binop(op, p1, p2));
        self.cx.mk_refine(Var::nu(), op.ty(), pred)
    }

    fn wt_rvalue(&mut self, val: &Rvalue) -> Ty<'lr> {
        match val {
            Rvalue::Use(operand) => {
                let (pred, typ) = self.wt_operand(operand);
                self.selfify(pred, &typ);
                if let Operand::Deref(place) = operand {
                    if !typ.is_copy() {
                        self.tcx.update(place, self.cx.mk_uninit(typ.size()));
                    }
                }
                typ
            }
            Rvalue::BinaryOp(op, lhs, rhs) => self.wt_binop(*op, rhs, lhs),
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let t1 = self.wt_binop(*op, lhs, rhs);
                let t2 = self
                    .cx
                    .mk_refine(Var::nu(), BasicType::Bool, self.cx.preds.tt);
                self.cx
                    .mk_tuple(&[(Var::field(0), t1), (Var::field(1), t2)])
            }
        }
    }

    fn wt_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::Let(x, layout) => {
                self.tcx.alloc(*x, layout);
            }
            Statement::Assign(place, rval) => {
                let (_, t1) = self.tcx.lookup(place);
                let t2 = self.wt_rvalue(rval);
                if t1.size() != t2.size() {
                    todo!();
                }
                self.tcx.update(place, t2);
            }
        }
    }

    fn wt_fn_body(&mut self, fn_body: &'b FnBody<'lr>) {
        match fn_body {
            FnBody::LetCont {
                name,
                heap,
                env,
                params,
                body,
                rest,
            } => {
                self.kenv.insert(
                    *name,
                    Cont {
                        heap,
                        env,
                        params: params.iter().map(|p| p.1).collect(),
                    },
                );
                let mut checker = TypeCk {
                    tcx: TyCtxt::new(self.cx, heap, env),
                    kenv: self.kenv,
                    cx: self.cx,
                    errors: vec![],
                };
                checker.wt_fn_body(body);
                self.errors.extend(checker.errors);
                self.wt_fn_body(rest);
            }
            FnBody::Ite {
                discr: _,
                then_branch,
                else_branch,
            } => {
                // TODO: use the discriminant
                self.wt_fn_body(then_branch);
                self.wt_fn_body(else_branch);
            }
            FnBody::Call { func, args, ret } => {
                let Cont { env, .. } = &self.kenv[ret];
                if let (_, TyS::Fn { .. }) = self.tcx.lookup(func) {
                    if let Err(err) = self.tcx.can_call(env, args) {
                        self.errors.push(err);
                    }
                } else {
                    self.errors.push("not a function type".into());
                }
            }
            FnBody::Jump { target, args } => {
                if let Some(Cont { env, .. }) = &self.kenv.get(target) {
                    if let Err(err) = self.tcx.can_call(env, args) {
                        self.errors.push(err);
                    }
                } else {
                    self.errors.push(format!(
                        "Cannot find continuation `{}` in this scope",
                        target
                    ));
                }
            }
            FnBody::Seq(statement, rest) => {
                self.wt_statement(statement);
                self.wt_fn_body(rest);
            }
            FnBody::Abort => {}
        }
    }

    fn selfify(&self, pred: Pred<'lr>, typ: Ty<'lr>) -> Ty<'lr> {
        match typ {
            TyS::Refine { bind, ty, .. } => {
                let r = self.cx.mk_binop(BinOp::Eq, self.cx.preds.nu, pred);
                self.cx.mk_refine(*bind, *ty, r)
            }
            _ => typ,
        }
    }
}

impl BinOp {
    pub fn ty(&self) -> BasicType {
        match self {
            BinOp::Add | BinOp::Sub => BasicType::Int,
            BinOp::Lt | BinOp::Le | BinOp::Eq | BinOp::Ge | BinOp::Gt => BasicType::Bool,
        }
    }
}
