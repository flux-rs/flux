use std::collections::HashMap;

use crate::{
    ast::{
        pred::{Pred, Var},
        *,
    },
    names::{ContId, Field, FnId, Local, Location},
    ty::context::TyCtxt,
};
use quickscope::ScopeMap;

pub struct NameFreshener<'a, S> {
    conts: ScopeMap<ContId<S>, ContId>,
    locals: ScopeMap<Local<S>, Local>,
    locations: ScopeMap<Location<S>, Location>,
    fields: ScopeMap<Field<S>, Field>,
    regions: HashMap<UniversalRegion<S>, UniversalRegion>,
    fns: HashMap<FnId<S>, FnId>,
    tcx: &'a TyCtxt,
}

impl<'a, S> NameFreshener<'a, S>
where
    S: Eq + Copy + std::hash::Hash + std::fmt::Debug,
{
    pub fn new(tcx: &'a TyCtxt) -> Self {
        NameFreshener {
            conts: ScopeMap::new(),
            locals: ScopeMap::new(),
            locations: ScopeMap::new(),
            fields: ScopeMap::new(),
            regions: HashMap::new(),
            fns: HashMap::new(),
            tcx,
        }
    }

    pub fn freshen<I>(mut self, program: Program<I, S>) -> Program<I> {
        let mut defs = vec![];
        for (fn_id, def) in program {
            let fresh = self.tcx.fresh::<FnId>();
            self.fns.insert(fn_id, fresh);
            defs.push((fresh, def))
        }
        let mut program = Program::new();
        for (fn_id, def) in defs {
            program.add_fn(fn_id, self.freshen_fn_def(def));
        }
        program
    }

    fn freshen_fn_def<I>(&mut self, def: FnDef<I, S>) -> FnDef<I> {
        let tcx = self.tcx;
        self.conts.define(def.ret, tcx.fresh::<ContId>());
        for local in &def.params {
            self.locals.define(*local, tcx.fresh::<Local>())
        }
        for (location, _) in &def.ty.in_heap {
            self.locations.define(*location, tcx.fresh::<Location>());
        }
        for region in &def.ty.regions {
            self.regions.insert(*region, tcx.fresh::<UniversalRegion>());
        }

        FnDef {
            params: self.freshen_args(def.params),
            body: self.freshen_body(def.body),
            ty: self.freshen_fn_ty(def.ty),
            ret: self.freshen_cont_id(def.ret),
        }
    }

    fn freshen_body<I>(&mut self, body: FnBody<I, S>) -> FnBody<I> {
        use FnBody::*;
        let tcx = self.tcx;
        match body {
            LetCont(defs, box rest) => {
                self.conts.push_layer();
                for def in &defs {
                    self.conts.define(def.name, tcx.fresh::<ContId>());
                }
                let defs = defs
                    .into_iter()
                    .map(|def| self.freshen_cont_def(def))
                    .collect();
                let rest = box self.freshen_body(rest);

                self.conts.pop_layer();

                LetCont(defs, rest)
            }
            Ite {
                discr,
                box then,
                box else_,
            } => Ite {
                discr: self.freshen_place(discr),
                then: box self.freshen_body(then),
                else_: box self.freshen_body(else_),
            },
            Call {
                func,
                args,
                destination,
            } => Call {
                func: self.fns[&func],
                args: self.freshen_args(args),
                destination: destination
                    .map(|(place, ret)| (self.freshen_place(place), self.freshen_cont_id(ret))),
            },
            Jump { target, args } => Jump {
                target: self.freshen_cont_id(target),
                args: self.freshen_args(args),
            },
            Seq(statement, box rest) => {
                self.locals.push_layer();
                let k = Seq(
                    self.freshen_statement(statement),
                    box self.freshen_body(rest),
                );
                self.locals.pop_layer();
                k
            }
            Abort => Abort,
        }
    }

    fn freshen_cont_def<I>(&mut self, cont: ContDef<I, S>) -> ContDef<I> {
        let tcx = self.tcx;
        self.locals.push_layer();
        for local in &cont.params {
            self.locals.define(*local, tcx.fresh::<Local>());
        }
        self.locations.push_layer();
        for (location, _) in &cont.ty.heap {
            self.locations.define(*location, tcx.fresh::<Location>());
        }
        let name = self.freshen_cont_id(cont.name);
        let ty = self.freshen_cont_ty(cont.ty);
        let params = self.freshen_params(cont.params);
        let body = box self.freshen_body(*cont.body);
        self.locations.pop_layer();
        self.locals.pop_layer();
        ContDef {
            name,
            ty,
            params,
            body,
        }
    }

    fn freshen_cont_ty(&mut self, cont_ty: ContTy<S>) -> ContTy {
        let mut inputs = vec![];
        for l in cont_ty.inputs {
            inputs.push(self.freshen_location(l));
        }
        ContTy {
            heap: self.freshen_heap(cont_ty.heap),
            locals: self.freshen_locals(cont_ty.locals),
            inputs,
        }
    }

    fn freshen_params(&mut self, params: Vec<Local<S>>) -> Vec<Local> {
        params.into_iter().map(|l| self.freshen_local(l)).collect()
    }

    fn freshen_statement<I>(&mut self, statement: Statement<I, S>) -> Statement<I> {
        use StatementKind::*;
        let kind = match statement.kind {
            StatementKind::Let(local, layout) => {
                self.locals.define(local, self.tcx.fresh::<Local>());
                Let(self.freshen_local(local), layout)
            }
            StatementKind::Assign(place, value) => {
                Assign(self.freshen_place(place), self.freshen_rvalue(value))
            }
            Drop(place) => Drop(self.freshen_place(place)),
            Nop => Nop,
        };
        Statement {
            source_info: statement.source_info,
            kind,
        }
    }

    fn freshen_rvalue(&mut self, rvalue: Rvalue<S>) -> Rvalue {
        use Rvalue::*;
        match rvalue {
            Use(op) => Use(self.freshen_operand(op)),
            Ref(kind, place) => Ref(kind, self.freshen_place(place)),
            BinaryOp(op, lhs, rhs) => {
                BinaryOp(op, self.freshen_operand(lhs), self.freshen_operand(rhs))
            }
            CheckedBinaryOp(op, lhs, rhs) => {
                CheckedBinaryOp(op, self.freshen_operand(lhs), self.freshen_operand(rhs))
            }
            UnaryOp(op, operand) => UnaryOp(op, self.freshen_operand(operand)),
        }
    }

    fn freshen_operand(&mut self, operand: Operand<S>) -> Operand {
        use Operand::*;
        match operand {
            Copy(place) => Copy(self.freshen_place(place)),
            Move(place) => Move(self.freshen_place(place)),
            Constant(c) => Constant(c),
        }
    }

    fn freshen_region(&mut self, region: Region<S>) -> Region {
        match region {
            Region::Concrete(places) => Region::Concrete(
                places
                    .into_iter()
                    .map(|place| self.freshen_place(place))
                    .collect(),
            ),
            Region::Infer => Region::Infer,
            Region::Universal(region) => Region::Universal(self.regions[&region]),
        }
    }

    fn freshen_fn_ty(&mut self, ty: FnTy<S>) -> FnTy {
        let mut regions = vec![];
        for region in ty.regions {
            regions.push(self.regions[&region])
        }

        self.locals.push_layer();
        for (local, _) in &ty.inputs {
            self.locals.define(*local, self.tcx.fresh::<Local>())
        }

        let in_heap = self.freshen_heap(ty.in_heap);
        let inputs = self.freshen_locals(ty.inputs);
        self.locations.push_layer();
        for (location, _) in &ty.out_heap {
            self.locations
                .define(*location, self.tcx.fresh::<Location>());
        }
        let out_heap = self.freshen_heap(ty.out_heap);
        let output = self.freshen_location(ty.output);
        let outputs = self.freshen_locals(ty.outputs);
        self.locations.pop_layer();
        self.locals.pop_layer();
        FnTy {
            regions,
            in_heap,
            inputs,
            out_heap,
            outputs,
            output,
        }
    }

    fn freshen_ty(&mut self, ty: Ty<S>) -> Ty {
        use Ty::*;
        match ty {
            OwnRef(location) => OwnRef(self.freshen_location(location)),
            Ref(kind, region, location) => Ref(
                kind,
                self.freshen_region(region),
                self.freshen_location(location),
            ),
            Tuple(tup) => {
                self.fields.push_layer();
                for (fld, _) in &tup {
                    self.fields.define(*fld, self.tcx.fresh::<Field>());
                }
                let tup = tup
                    .into_iter()
                    .map(|(fld, ty)| (self.freshen_field(fld), self.freshen_ty(ty)))
                    .collect();
                self.fields.pop_layer();
                Tuple(tup)
            }
            Uninit(s) => Uninit(s),
            Refine(bty, refine) => Refine(bty, self.freshen_refine(refine)),
        }
    }

    fn freshen_refine(&mut self, refine: Refine<S>) -> Refine {
        match refine {
            Refine::Infer => Refine::Infer,
            Refine::Pred(pred) => Refine::Pred(self.freshen_pred(pred)),
        }
    }

    fn freshen_pred(&mut self, pred: Pred<S>) -> Pred {
        use Pred::*;
        match pred {
            Constant(c) => Constant(c),
            Place(pred::Place { base, projs }) => Place(pred::Place {
                base: self.freshen_var(base),
                projs,
            }),
            BinaryOp(op, box lhs, box rhs) => {
                BinaryOp(op, box self.freshen_pred(lhs), box self.freshen_pred(rhs))
            }
            UnaryOp(op, box operand) => UnaryOp(op, box self.freshen_pred(operand)),
        }
    }

    fn freshen_var(&mut self, var: Var<S>) -> Var {
        match var {
            Var::Nu => Var::Nu,
            Var::Location(location) => Var::Location(self.freshen_location(location)),
            Var::Field(field) => Var::Field(self.freshen_field(field)),
        }
    }

    fn freshen_place(&mut self, place: Place<S>) -> Place {
        Place {
            base: self.freshen_local(place.base),
            projs: place.projs,
        }
    }

    fn freshen_args(&mut self, args: Vec<Local<S>>) -> Vec<Local> {
        args.into_iter()
            .map(|local| self.freshen_local(local))
            .collect()
    }

    fn freshen_locals(&mut self, locals: Vec<(Local<S>, Location<S>)>) -> Vec<(Local, Location)> {
        locals
            .into_iter()
            .map(|(x, l)| (self.freshen_local(x), self.freshen_location(l)))
            .collect()
    }

    fn freshen_heap(&mut self, heap: Heap<S>) -> Heap {
        heap.into_iter()
            .map(|(l, ty)| (self.freshen_location(l), self.freshen_ty(ty)))
            .collect()
    }

    fn freshen_cont_id(&mut self, cont_id: ContId<S>) -> ContId {
        self.conts
            .get(&cont_id)
            .copied()
            .expect("NameFreshener: ContId not found")
    }

    fn freshen_local(&mut self, x: Local<S>) -> Local {
        self.locals
            .get(&x)
            .copied()
            .expect("NameFreshener: Local not found")
    }

    fn freshen_location(&mut self, l: Location<S>) -> Location {
        self.locations
            .get(&l)
            .copied()
            .expect("NameFreshener: Location not found")
    }

    fn freshen_field(&mut self, f: Field<S>) -> Field {
        self.fields
            .get(&f)
            .copied()
            .expect("NameFreshener: Field not found")
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Name<S> {
    Location(Location<S>),
    Local(Local<S>),
    Field(Field<S>),
    ContId(ContId<S>),
}
