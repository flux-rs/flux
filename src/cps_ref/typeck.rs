use std::collections::HashMap;

use super::{
    ast::*, constraint::Constraint, context::LiquidRustCtxt, subst::DeferredSubst, subst::Subst,
    utils::OrderedHashMap,
};

type LocalsMap = HashMap<Local, OwnRef>;
type LocationsMap<'lr> = OrderedHashMap<Location, Ty<'lr>>;
type Bindings<'lr> = Vec<(Location, Ty<'lr>)>;

struct TyCtxt<'lr> {
    cx: &'lr LiquidRustCtxt<'lr>,
    frames: Vec<CtxtFrame<'lr>>,
    curr_location: u32,
}

struct CtxtFrame<'lr> {
    locations: LocationsMap<'lr>,
    locals: LocalsMap,
}

impl<'lr> TyCtxt<'lr> {
    pub fn new(
        cx: &'lr LiquidRustCtxt<'lr>,
        locations: LocationsMap<'lr>,
        locals: LocalsMap,
    ) -> Self {
        let frame = CtxtFrame { locations, locals };
        Self {
            frames: vec![frame],
            cx,
            curr_location: 0,
        }
    }

    pub fn vars_in_scope(&self) -> Vec<Var> {
        self.frames
            .iter()
            .flat_map(|f| f.locations.keys())
            .map(|l| l.into())
            .collect()
    }

    pub fn enter_cont_def<T>(
        &mut self,
        cont_def: &ContDef<'lr>,
        mut act: impl for<'a> FnMut(&'a mut Self) -> T,
    ) -> T {
        let frame = CtxtFrame {
            locals: cont_def
                .env
                .iter()
                .chain(cont_def.params.iter())
                .copied()
                .collect(),
            locations: insert_kvars(self.cx, &cont_def.heap, self.vars_in_scope()),
        };
        self.frames.push(frame);
        let t = act(self);
        self.frames.pop();
        t
    }

    pub fn enter_branch<T>(&mut self, mut act: impl for<'a> FnMut(&'a mut Self) -> T) -> T {
        let frame = CtxtFrame {
            locals: self.frames.last().unwrap().locals.clone(),
            locations: LocationsMap::new(),
        };
        self.frames.push(frame);
        let r = act(self);
        self.frames.pop();
        r
    }

    pub fn lookup(&self, place: &Place) -> (Pred<'lr>, Ty<'lr>) {
        let OwnRef(l) = self.lookup_local(place.local).unwrap();
        let typ = self.lookup_location(l).unwrap();
        let pred = self.cx.mk_place(l.into(), &place.projection);
        (pred, typ.project(&place.projection))
    }

    fn lookup_local(&self, x: Local) -> Option<OwnRef> {
        self.frames.last().and_then(|f| f.locals.get(&x).copied())
    }

    fn lookup_location(&self, l: Location) -> Option<Ty<'lr>> {
        for frame in self.frames.iter().rev() {
            if let Some(typ) = frame.locations.get(&l) {
                return Some(typ);
            }
        }
        None
    }

    fn insert_location(&mut self, l: Location, typ: Ty<'lr>) {
        debug_assert!(self.lookup_location(l).is_none());
        let frame = self.frames.last_mut().unwrap();
        frame.locations.insert(l, typ);
    }

    fn insert_local(&mut self, x: Local, ownref: OwnRef) {
        let frame = self.frames.last_mut().unwrap();
        frame.locals.insert(x, ownref);
    }

    pub fn uninit(&mut self, place: &Place) {
        let (_, t) = self.lookup(place);
        self.update(place, self.cx.mk_uninit(t.size()));
    }

    pub fn update(&mut self, place: &Place, typ: Ty<'lr>) -> (Location, Ty<'lr>) {
        let OwnRef(l) = self.lookup_local(place.local).unwrap();
        let updated_typ =
            self.lookup_location(l)
                .unwrap()
                .update_at(self.cx, &place.projection, typ);
        let fresh_l = self.fresh_location();
        self.insert_location(fresh_l, updated_typ);
        self.insert_local(place.local, OwnRef(fresh_l));
        (fresh_l, updated_typ)
    }

    pub fn alloc(&mut self, x: Local, layout: &TypeLayout) {
        debug_assert!(self.lookup_local(x).is_none());
        let fresh_l = self.fresh_location();
        self.insert_location(fresh_l, self.cx.mk_ty_for_layout(layout));
        self.insert_local(x, OwnRef(fresh_l));
    }

    fn fresh_location(&mut self) -> Location {
        let l = self.curr_location;
        self.curr_location += 1;
        Location(Symbol::intern(&format!("{}", l)))
    }

    pub fn check_call(
        &mut self,
        in_heap: &Heap<'lr>,
        params: &[OwnRef],
        out_heap: &Heap<'lr>,
        out_ty: OwnRef,
        args: &[Local],
        cont: &Cont<'_, 'lr>,
    ) -> Result<Constraint, TypeError<'lr>> {
        if args.len() != params.len() {
            return Err(TypeError::ArgCount);
        }
        // Check against function arguments
        // TODO: pass vars in scope
        let locations_f = insert_kvars(self.cx, &in_heap, vec![]);
        let locals_f = args.iter().copied().zip(params.iter().copied()).collect();
        let c1 = self.env_incl(&locations_f, &locals_f)?;

        // Update context after function call
        let fresh_x = Local(Symbol::intern("$")); // FIXME
        for arg in args {
            self.uninit(&Place::from(*arg))
        }
        // FIXME: we are assuming all locations are fresh
        for (l, typ) in out_heap {
            self.insert_location(*l, typ);
        }
        self.insert_local(fresh_x, out_ty);

        let c2 =
            Constraint::from_bindings(out_heap.iter().copied(), self.check_jump(cont, &[fresh_x])?);
        Ok(Constraint::Conj(vec![c1, c2]))
    }

    pub fn check_jump(
        &mut self,
        cont: &Cont<'_, 'lr>,
        args: &[Local],
    ) -> Result<Constraint, TypeError<'lr>> {
        if args.len() != cont.params.len() {
            return Err(TypeError::ArgCount);
        }
        let locals = cont.locals_map(args)?;
        self.env_incl(&cont.heap, &locals)
    }

    fn env_incl(
        &mut self,
        locations: &LocationsMap<'lr>,
        locals: &LocalsMap,
    ) -> Result<Constraint, TypeError<'lr>> {
        let subst = self.infer_subst_ctxt(&locations, locals);
        let locations = DeferredSubst::new(subst, locations);
        let mut vec = vec![];
        for (x, OwnRef(l2)) in locals {
            let OwnRef(l1) = self.lookup_local(*x).unwrap();
            let p = self.cx.mk_place(l1.into(), &[]);
            let typ1 = selfify(self.cx, p, self.lookup_location(l1).unwrap()).into();
            let typ2 = locations.get(l2);
            vec.push(self.subtype(&locations, typ1, typ2)?);
        }
        Ok(Constraint::Conj(vec))
    }

    fn subtype(
        &mut self,
        locations: &DeferredSubst<&LocationsMap<'lr>>,
        typ1: DeferredSubst<Ty<'lr>>,
        typ2: DeferredSubst<Ty<'lr>>,
    ) -> Result<Constraint, TypeError<'lr>> {
        let (subst1, typ1) = typ1.split();
        let (subst2, typ2) = typ2.split();
        let c = match (typ1, typ2) {
            (TyS::Fn { .. }, TyS::Fn { .. }) => todo!("implement function subtyping"),
            (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
                let p = self.cx.mk_place((*l1).into(), &[]);
                let typ1 = selfify(self.cx, p, self.lookup_location(*l1).unwrap()).into();
                let typ2 = locations.get(l2);
                self.subtype(locations, typ1, typ2)?
            }
            (
                TyS::Refine {
                    ty: ty1,
                    pred: pred1,
                },
                TyS::Refine {
                    ty: ty2,
                    pred: pred2,
                },
            ) => {
                if ty1 != ty2 {
                    return Err(TypeError::SubtypingError(typ1, typ2));
                }
                Constraint::from_subtype(
                    *ty1,
                    DeferredSubst::new(subst1, pred1),
                    DeferredSubst::new(subst2, pred2),
                )
            }
            (TyS::Tuple(fields1), TyS::Tuple(fields2)) => {
                if fields1.len() != fields2.len() {
                    return Err(TypeError::SubtypingError(typ1, typ2));
                }
                let subst2 =
                    subst2.extend2(fields2.iter().map(|f| f.0), fields1.iter().map(|f| f.0));
                let mut iter = fields1.iter().zip(fields2).rev();
                if let Some(((_, t1), (_, t2))) = iter.next() {
                    let t1 = DeferredSubst::new(subst1.clone(), *t1);
                    let t2 = DeferredSubst::new(subst2.clone(), *t2);
                    let mut c = self.subtype(locations, t1, t2)?;
                    for ((x1, t1), (_, t2)) in iter {
                        let t1 = DeferredSubst::new(subst1.clone(), *t1);
                        let t2 = DeferredSubst::new(subst2.clone(), *t2);
                        c = Constraint::Conj(vec![
                            self.subtype(locations, t1.clone(), t2)?,
                            Constraint::from_binding(*x1, t1, c),
                        ]);
                    }
                    c
                } else {
                    Constraint::True
                }
            }
            (_, TyS::Uninit(_)) => Constraint::True,
            _ => return Err(TypeError::SubtypingError(typ1, typ2)),
        };
        Ok(c)
    }

    fn infer_subst_ctxt(&self, locations: &LocationsMap, locals: &LocalsMap) -> Subst {
        let mut v = Vec::new();
        for (x, OwnRef(l2)) in locals {
            let OwnRef(l1) = self.lookup_local(*x).unwrap();
            self.infer_subst_typ(
                locations,
                self.cx.mk_own_ref(l1),
                self.cx.mk_own_ref(*l2),
                &mut v,
            );
        }
        Subst::from(v)
    }

    fn infer_subst_typ(
        &self,
        locations: &LocationsMap,
        typ1: Ty,
        typ2: Ty,
        v: &mut Vec<(Var, Var)>,
    ) {
        match (typ1, typ2) {
            (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
                self.infer_subst_typ(
                    locations,
                    self.lookup_location(*l1).unwrap(),
                    locations[l2],
                    v,
                );
                v.push((Var::Location(*l2), Var::Location(*l1)));
            }
            _ => {}
        }
    }
}

pub struct TypeCk<'a, 'b, 'lr> {
    cx: &'lr LiquidRustCtxt<'lr>,
    kenv: &'a mut HashMap<Symbol, Cont<'b, 'lr>>,
    errors: Vec<TypeError<'lr>>,
}

impl<'b, 'lr> TypeCk<'_, 'b, 'lr> {
    pub fn cgen(
        cx: &'lr LiquidRustCtxt<'lr>,
        fn_def: &FnDef<'lr>,
    ) -> Result<Constraint, Vec<TypeError<'lr>>> {
        let mut kenv = HashMap::default();
        kenv.insert(fn_def.ret, Cont::from_fn_def(cx, fn_def));
        let mut checker = TypeCk {
            cx,
            kenv: &mut kenv,
            errors: vec![],
        };
        let locations = insert_kvars(cx, &fn_def.heap, vec![]);
        let locals = fn_def.args.iter().copied().collect();
        let c = Constraint::from_bindings(
            locations.clone().iter().map(|(&l, &t)| (l, t)),
            checker.wt_fn_body(&mut TyCtxt::new(cx, locations, locals), &fn_def.body),
        );
        if checker.errors.is_empty() {
            Ok(c)
        } else {
            Err(checker.errors)
        }
    }

    fn wt_operand(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        operand: &Operand,
    ) -> (Pred<'lr>, Ty<'lr>, Bindings<'lr>) {
        match operand {
            Operand::Deref(place) => {
                let mut bindings = vec![];
                let (pred, typ) = tcx.lookup(place);
                if !typ.is_copy() {
                    bindings.push(tcx.update(place, self.cx.mk_uninit(typ.size())));
                }
                (pred, typ, bindings)
            }
            Operand::Constant(c) => {
                let pred = self
                    .cx
                    .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_const(*c));
                (
                    self.cx.mk_const(*c),
                    self.cx.mk_refine(c.ty(), pred),
                    vec![],
                )
            }
        }
    }

    fn wt_binop(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        op: BinOp,
        rhs: &Operand,
        lhs: &Operand,
    ) -> Result<(Ty<'lr>, Bindings<'lr>), TypeError<'lr>> {
        let (p1, t1, mut bindings1) = self.wt_operand(tcx, lhs);
        let (p2, t2, bindings2) = self.wt_operand(tcx, rhs);
        bindings1.extend(bindings2);
        if !t1.is_int() || !t2.is_int() {
            return Err(TypeError::BinOpMismatch(op, t1, t2));
        }
        let (ty, pred) = match op {
            BinOp::Add | BinOp::Sub => (
                BasicType::Int,
                self.cx
                    .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_binop(op, p1, p2)),
            ),
            BinOp::Lt | BinOp::Le | BinOp::Eq | BinOp::Ge | BinOp::Gt => (
                BasicType::Bool,
                self.cx
                    .mk_iff(self.cx.preds.nu, self.cx.mk_binop(op, p1, p2)),
            ),
        };
        Ok((self.cx.mk_refine(ty, pred), bindings1))
    }

    fn wt_rvalue(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        val: &Rvalue,
    ) -> Result<(Ty<'lr>, Bindings<'lr>), TypeError<'lr>> {
        let r = match val {
            Rvalue::Use(operand) => {
                let (p, typ, bindings) = self.wt_operand(tcx, operand);
                (selfify(self.cx, p, &typ), bindings)
            }
            Rvalue::BinaryOp(op, lhs, rhs) => self.wt_binop(tcx, *op, rhs, lhs)?,
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let (t1, bindings) = self.wt_binop(tcx, *op, lhs, rhs)?;
                let t2 = self.cx.mk_refine(BasicType::Bool, self.cx.preds.tt);
                let tuple = self
                    .cx
                    .mk_tuple(&[(Field::nth(0), t1), (Field::nth(1), t2)]);
                (tuple, bindings)
            }
            Rvalue::UnaryOp(op, operand) => {
                let (pred, typ, bindings) = self.wt_operand(tcx, operand);
                match (op, typ) {
                    (
                        UnOp::Not,
                        TyS::Refine {
                            ty: BasicType::Bool,
                            ..
                        },
                    ) => {
                        let t = self
                            .cx
                            .mk_refine(BasicType::Bool, self.cx.mk_unop(UnOp::Not, pred));
                        (t, bindings)
                    }
                    _ => {
                        return Err(TypeError::UnOpMismatch(*op, typ));
                    }
                }
            }
        };
        Ok(r)
    }

    fn wt_statement(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        statement: &Statement,
    ) -> Result<Bindings<'lr>, TypeError<'lr>> {
        match statement {
            Statement::Let(x, layout) => {
                tcx.alloc(*x, layout);
                Ok(vec![])
            }
            Statement::Assign(place, rval) => {
                let (_, t1) = tcx.lookup(place);
                let (t2, mut bindings) = self.wt_rvalue(tcx, rval)?;
                if t1.size() != t2.size() {
                    return Err(TypeError::SizeMismatch(t1, t2));
                }
                bindings.push(tcx.update(place, t2));
                Ok(bindings)
            }
        }
    }

    fn wt_fn_body(&mut self, tcx: &mut TyCtxt<'lr>, fn_body: &'b FnBody<'lr>) -> Constraint {
        match fn_body {
            FnBody::LetCont { def, rest } => {
                let cont = Cont::from_cont_def(self.cx, def, tcx.vars_in_scope());
                self.kenv.insert(def.name, cont);
                let c1 = tcx.enter_cont_def(def, |tcx| self.wt_fn_body(tcx, &def.body));
                let c1 = Constraint::from_bindings(
                    self.kenv[&def.name].heap.iter().map(|(&l, &t)| (l, t)),
                    c1,
                );
                let c2 = self.wt_fn_body(tcx, rest);
                Constraint::Conj(vec![c1, c2])
            }
            FnBody::Ite { discr, then, else_ } => {
                let (p, typ) = tcx.lookup(discr);
                match typ {
                    TyS::Refine {
                        ty: BasicType::Bool,
                        ..
                    } => {
                        let c1 = tcx.enter_branch(|tcx| self.wt_fn_body(tcx, then));
                        let c2 = self.wt_fn_body(tcx, else_);
                        Constraint::Conj(vec![
                            Constraint::guard(p, c1),
                            Constraint::guard(self.cx.mk_unop(UnOp::Not, p), c2),
                        ])
                    }
                    _ => {
                        self.errors.push(TypeError::NotBool(typ));
                        Constraint::Err
                    }
                }
            }
            FnBody::Call { func, ret, args } => {
                let cont = &self.kenv[ret];
                let (_, typ) = tcx.lookup(func);
                match typ {
                    TyS::Fn {
                        in_heap,
                        params,
                        out_heap,
                        ret: out_ty,
                    } => match tcx.check_call(in_heap, params, out_heap, *out_ty, args, cont) {
                        Ok(c) => c,
                        Err(err) => {
                            self.errors.push(err);
                            Constraint::Err
                        }
                    },
                    _ => {
                        self.errors.push(TypeError::NotFun(typ));
                        Constraint::Err
                    }
                }
            }
            FnBody::Jump { target, args } => tcx.check_jump(&self.kenv[target], args).unwrap(),
            FnBody::Seq(statement, rest) => match self.wt_statement(tcx, statement) {
                Ok(bindings) => {
                    Constraint::from_bindings(bindings.iter().copied(), self.wt_fn_body(tcx, rest))
                }
                Err(err) => {
                    self.errors.push(err);
                    Constraint::Err
                }
            },
            FnBody::Abort => Constraint::True,
        }
    }
}
fn selfify<'lr>(cx: &'lr LiquidRustCtxt<'lr>, pred: Pred<'lr>, typ: Ty<'lr>) -> Ty<'lr> {
    match typ {
        TyS::Refine { ty, .. } => {
            let r = cx.mk_binop(BinOp::Eq, cx.preds.nu, pred);
            cx.mk_refine(*ty, r)
        }
        _ => typ,
    }
}

impl<'lr> Cont<'_, 'lr> {
    fn locals_map(&self, args: &[Local]) -> Result<LocalsMap, TypeError<'lr>> {
        debug_assert!(args.len() == self.params.len());
        let mut ctxt: LocalsMap = self.env.iter().copied().collect();
        for (local, ownref) in args.iter().zip(&self.params) {
            if ctxt.contains_key(local) {
                return Err(TypeError::DupLocal(*local));
            }
            ctxt.insert(*local, *ownref);
        }
        Ok(ctxt)
    }
}

fn insert_kvars<'lr, 'a>(
    cx: &'lr LiquidRustCtxt<'lr>,
    heap: &Heap<'lr>,
    mut vars_in_scope: Vec<Var>,
) -> LocationsMap<'lr> {
    heap.iter()
        .map(|&(l, t)| {
            let t = t.insert_kvars(cx, &mut vars_in_scope);
            vars_in_scope.push(l.into());
            (l, t)
        })
        .collect()
}

impl<'lr> TyS<'lr> {
    fn insert_kvars(
        &'lr self,
        cx: &'lr LiquidRustCtxt<'lr>,
        vars_in_scope: &mut Vec<Var>,
    ) -> Ty<'lr> {
        match self {
            TyS::Fn { .. } => todo!(),
            TyS::Tuple(fields) => {
                let fields: Vec<(Field, Ty)> = fields
                    .iter()
                    .map(|&(f, t)| {
                        let t = t.insert_kvars(cx, vars_in_scope);
                        vars_in_scope.push(Var::from(f));
                        (f, t)
                    })
                    .collect();
                vars_in_scope.truncate(vars_in_scope.len() - fields.len());
                cx.mk_tuple(&fields)
            }
            &TyS::RefineHole { ty, n } => {
                // Nu needs to be the first argument because of liquid-fixpoint restrictions
                let mut vars: Vec<Var> = vec![Var::Nu];
                vars.extend(vars_in_scope.iter().copied());
                cx.mk_refine(ty, cx.mk_pred(PredS::Kvar(n, vars)))
            }
            _ => self,
        }
    }
}
struct Cont<'a, 'lr> {
    pub heap: LocationsMap<'lr>,
    pub env: &'a Env,
    pub params: Vec<OwnRef>,
}

const EMPTY_ENV: &Env = &vec![];
impl<'a, 'lr> Cont<'a, 'lr> {
    fn from_cont_def(
        cx: &'lr LiquidRustCtxt<'lr>,
        def: &'a ContDef<'lr>,
        vars_in_scope: Vec<Var>,
    ) -> Self {
        Self {
            heap: insert_kvars(cx, &def.heap, vars_in_scope),
            env: &def.env,
            params: def.params.iter().map(|p| p.1).collect(),
        }
    }

    fn from_fn_def(cx: &'lr LiquidRustCtxt<'lr>, def: &'a FnDef<'lr>) -> Self {
        Self {
            heap: insert_kvars(cx, &def.out_heap, vec![]),
            env: EMPTY_ENV,
            params: vec![def.out_ty],
        }
    }
}

#[derive(Debug)]
pub enum TypeError<'lr> {
    SubtypingError(Ty<'lr>, Ty<'lr>),
    SizeMismatch(Ty<'lr>, Ty<'lr>),
    DupLocal(Local),
    BinOpMismatch(BinOp, Ty<'lr>, Ty<'lr>),
    UnOpMismatch(UnOp, Ty<'lr>),
    NotFun(Ty<'lr>),
    NotBool(Ty<'lr>),
    ArgCount,
}
