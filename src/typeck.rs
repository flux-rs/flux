extern crate rustc_mir;

use super::context::LiquidRustCtxt;
use super::refinements::{Binder, Place, Pred, ReftType, Scalar, Value, Var};
use super::smtlib2::{SmtRes, Solver};
use super::syntax::ast::{BinOpKind, UnOpKind};
use rustc::mir::interpret::ConstValue;
use rustc::mir::{self, Constant, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc::ty::{self, Ty};
use rustc_hir::{def_id::DefId, BodyId};
use rustc_index::vec::IndexVec;
use rustc_index::{bit_set::BitSet, vec::Idx};
use rustc_mir::dataflow::{
    do_dataflow, BitDenotation, BottomValue, DataflowResultsCursor, DebugFormatted, GenKillSet,
};
use std::collections::{HashMap, HashSet};

pub fn check_body(cx: &LiquidRustCtxt<'_, '_>, body_id: BodyId) {
    ReftChecker::new(cx, body_id).check_body();
}

struct ReftChecker<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustCtxt<'lr, 'tcx>,
    mir: &'a mir::Body<'tcx>,
    reft_types: HashMap<mir::Local, Binder<&'lr ReftType<'lr, 'tcx>>>,
    cursor: DataflowResultsCursor<'a, 'tcx, DefinitelyInitializedLocal<'a, 'tcx>>,
}

impl<'a, 'lr, 'tcx> ReftChecker<'a, 'lr, 'tcx> {
    pub fn new(cx: &'a LiquidRustCtxt<'lr, 'tcx>, body_id: BodyId) -> Self {
        let reft_types = cx.local_decls(body_id).clone();
        let mir = cx.optimized_mir(body_id);
        let cursor = initialized_locals(cx, cx.hir().body_owner_def_id(body_id));
        ReftChecker {
            cx,
            mir,
            reft_types,
            cursor,
        }
    }

    fn env_at(&mut self, block: mir::BasicBlock, index: usize) -> Vec<&'lr Pred<'lr, 'tcx>> {
        let loc = mir::Location {
            block,
            statement_index: index,
        };
        self.cursor.seek(loc);
        let mut env = Vec::new();
        for local in self.cursor.get().iter() {
            if let Some(pred) = self.reft_types.get(&local).and_then(|rt| rt.pred()) {
                env.push(self.cx.open_pred(pred, Value::Local(local)));
            }
        }
        env
    }

    pub fn check_body(&mut self) {
        for (bb, bbd) in self.mir.basic_blocks().iter_enumerated() {
            print!("\nbb{}:", bb.index());
            for (i, statement) in bbd.statements.iter().enumerate() {
                println!("\n  {:?}", statement);
                match &statement.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        let ty = place.ty(self, self.cx.tcx()).ty;
                        let lhs = self.rvalue_reft_type(ty, rvalue);
                        let env = self.env_at(bb, i);
                        self.check_assign(*place, &env, lhs);
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop => {}
                    _ => todo!("{:?}", statement),
                }
            }
            let env = self.env_at(bb, bbd.statements.len());
            if let Some(terminator) = &bbd.terminator {
                println!("\n  {:?}", terminator.kind);
                match &terminator.kind {
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        if let Some((place, _)) = destination {
                            let fun_type = self.operand_reft_type(func);
                            if place.projection.len() > 0 {
                                todo!();
                            }
                            let values = args
                                .iter()
                                .map(|arg| self.operand_to_arg(arg))
                                .collect::<Vec<_>>();
                            let (formals, ret) = self.cx.open_fun_type(fun_type, &values);

                            for (arg, formal) in args.iter().zip(formals) {
                                let actual = self.operand_reft_type(arg);
                                self.check_subtyping(&env, actual, formal);
                            }
                            println!("");
                            self.check_assign(*place, &env, ret);
                        } else {
                            todo!("implement checks for non converging calls")
                        }
                    }
                    TerminatorKind::Resume
                    | TerminatorKind::Assert { .. }
                    | TerminatorKind::Abort
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable => {}
                    _ => todo!(),
                };
            }
        }
        println!("---------------------------");
    }

    fn check_assign(
        &mut self,
        place: mir::Place,
        env: &[&'lr Pred<'lr, 'tcx>],
        lhs: Binder<&'lr ReftType<'lr, 'tcx>>,
    ) {
        if place.projection.len() > 0 {
            todo!();
        }
        let local = place.local;
        if let Some(rhs) = self.reft_types.get(&local) {
            self.check_subtyping(&env, lhs, *rhs);
        } else if !self.mir.local_decls[local].is_user_variable() {
            println!("    infer {:?}:{:?}", local, lhs);
            self.reft_types.insert(local, lhs);
        }
    }

    fn operand_to_arg(&self, operand: &Operand<'tcx>) -> Value<'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.len() > 0 {
                    bug!("values in argument position must by constants or locals")
                }
                Value::Local(place.local)
            }
            Operand::Constant(box Constant { literal, .. }) => {
                if_chain! {
                    if let ty::ConstKind::Value(val) = literal.val;
                    if let ConstValue::Scalar(scalar) = val;
                    if let mir::interpret::Scalar::Raw {data, size} = scalar;
                    then {
                        Value::Constant(literal.ty, Scalar { data, size })
                    }
                    else {
                        todo!("{:?}", operand);
                    }
                }
            }
        }
    }

    fn check_subtyping(
        &self,
        env: &[&'lr Pred<'lr, 'tcx>],
        lhs: Binder<&'lr ReftType<'lr, 'tcx>>,
        rhs: Binder<&'lr ReftType<'lr, 'tcx>>,
    ) {
        let lhs = self.cx.open_with_fresh_vars(lhs);
        let rhs = self.cx.open_with_fresh_vars(rhs);
        match (lhs, rhs) {
            (ReftType::Fun { .. }, ReftType::Fun { .. }) => todo!(),
            (ReftType::Reft(lhs), ReftType::Reft(rhs)) => {
                let r = self.check(&env, lhs, rhs);
                if let Err(e) = r {
                    println!("    {:?}", e);
                }
            }
            _ => bug!("refinement types must have the same shape"),
        }
    }

    fn operand_reft_type(&self, operand: &Operand<'tcx>) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let reft_ty = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                match place.ty(self, self.cx.tcx()).ty.kind {
                    ty::FnDef(def_id, _) => return self.cx.reft_type_for(def_id),
                    ty::FnPtr(..) => todo!(),
                    _ => {
                        let place = Place {
                            var: Var::Local(place.local),
                            projection: place.projection,
                        };
                        let place = self.cx.mk_pred_place(place);
                        self.cx
                            .mk_reft(self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, place))
                    }
                }
            }
            Operand::Constant(box Constant { literal, .. }) => match literal.ty.kind {
                ty::FnDef(def_id, _) => return self.cx.reft_type_for(def_id),
                ty::FnPtr(..) => todo!(),
                _ => {
                    let scalar = if_chain! {
                        if let ty::ConstKind::Value(val) = literal.val;
                        if let ConstValue::Scalar(scalar) = val;
                        if let mir::interpret::Scalar::Raw {data, size} = scalar;
                        then {
                            Scalar { data, size }
                        }
                        else {
                            todo!("{:?}", operand);
                        }
                    };
                    let constant = self.cx.mk_constant(literal.ty, scalar);
                    self.cx
                        .mk_reft(self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, constant))
                }
            },
        };
        Binder::bind(reft_ty)
    }

    fn operand_to_value(&self, operand: &Operand<'tcx>) -> &'lr Pred<'lr, 'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.cx.mk_pred_place(Place {
                var: Var::Local(place.local),
                projection: place.projection,
            }),
            Operand::Constant(box Constant { literal, .. }) => if_chain! {
                if let ty::ConstKind::Value(val) = literal.val;
                if let ConstValue::Scalar(scalar) = val;
                if let mir::interpret::Scalar::Raw {data, size} = scalar;
                then {
                    self.cx.mk_constant(literal.ty, Scalar { data, size })
                }
                else {
                    todo!("{:?}", operand);
                }
            },
        }
    }

    pub fn rvalue_reft_type(
        &self,
        ty: Ty<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let reft_ty = match rvalue {
            // v:{v == operand}
            Rvalue::Use(operand) => return self.operand_reft_type(operand),
            // v:{v.0 == lhs + rhs}
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let op = mir_op_to_refine_op(*op);
                let bin =
                    self.cx
                        .mk_binary(self.operand_to_value(lhs), op, self.operand_to_value(rhs));
                let ty = ty.tuple_fields().next().unwrap();
                let bin = self.cx.mk_binary(
                    self.cx.mk_pred_place(self.cx.mk_place_field(
                        Place::nu(),
                        mir::Field::new(0),
                        ty,
                    )),
                    BinOpKind::Eq,
                    bin,
                );
                self.cx.mk_reft(bin)
            }
            // v:{v == lhs + rhs}
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let op = mir_op_to_refine_op(*op);
                let bin =
                    self.cx
                        .mk_binary(self.operand_to_value(lhs), op, self.operand_to_value(rhs));
                let bin = self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, bin);
                self.cx.mk_reft(bin)
            }
            _ => todo!("{:?}", rvalue),
        };
        Binder::bind(reft_ty)
    }

    fn check(
        &self,
        env: &[&'lr Pred<'lr, 'tcx>],
        lhs: &'lr Pred<'lr, 'tcx>,
        rhs: &'lr Pred<'lr, 'tcx>,
    ) -> SmtRes<()> {
        let mut solver = Solver::default(())?;
        let mut places = HashSet::new();
        for pred in env.iter().chain(&[lhs, rhs]) {
            pred.iter_places(|place| {
                places.insert(place);
            })
        }

        for place in places {
            solver.declare_const(&place, "Int")?;
        }

        for pred in env {
            println!("    {}", pred.to_smt_str());
            solver.assert(pred)?;
        }
        let not_rhs = Pred::Unary(UnOpKind::Not, rhs);
        solver.assert(lhs)?;
        solver.assert(&not_rhs)?;
        println!("    {}", lhs.to_smt_str());
        println!("    {}", not_rhs.to_smt_str());

        let b = solver.check_sat()?;
        println!("    unsat {}", !b);
        Ok(())
    }
}

impl<'tcx> mir::HasLocalDecls<'tcx> for ReftChecker<'_, '_, 'tcx> {
    fn local_decls(&self) -> &IndexVec<mir::Local, mir::LocalDecl<'tcx>> {
        &self.mir.local_decls
    }
}

pub fn mir_op_to_refine_op(op: mir::BinOp) -> BinOpKind {
    match op {
        mir::BinOp::Add => BinOpKind::Add,
        mir::BinOp::Sub => BinOpKind::Sub,
        mir::BinOp::Mul => BinOpKind::Mul,
        mir::BinOp::Div => BinOpKind::Div,
        mir::BinOp::Eq => BinOpKind::Eq,
        mir::BinOp::Lt => BinOpKind::Lt,
        mir::BinOp::Ge => BinOpKind::Ge,
        mir::BinOp::Gt => BinOpKind::Gt,
        mir::BinOp::Le
        | mir::BinOp::Ne
        | mir::BinOp::Rem
        | mir::BinOp::BitXor
        | mir::BinOp::BitAnd
        | mir::BinOp::BitOr
        | mir::BinOp::Shl
        | mir::BinOp::Shr
        | mir::BinOp::Offset => unimplemented!("{:?}", op),
    }
}

fn initialized_locals<'a, 'tcx>(
    cx: &LiquidRustCtxt<'_, 'tcx>,
    def_id: DefId,
) -> DataflowResultsCursor<'a, 'tcx, DefinitelyInitializedLocal<'a, 'tcx>> {
    let mir = cx.tcx().optimized_mir(def_id);
    let dead_unwinds = BitSet::new_empty(mir.basic_blocks().len());
    let initialized_result = do_dataflow(
        cx.tcx(),
        mir,
        def_id,
        &[],
        &dead_unwinds,
        DefinitelyInitializedLocal::new(mir),
        |bd, p| DebugFormatted::new(&bd.body().local_decls[p]),
    );

    DataflowResultsCursor::new(initialized_result, mir)
}

struct DefinitelyInitializedLocal<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
}

impl<'a, 'tcx> DefinitelyInitializedLocal<'a, 'tcx> {
    pub fn new(body: &'a mir::Body<'tcx>) -> Self {
        DefinitelyInitializedLocal { body }
    }

    pub fn body(&self) -> &mir::Body<'tcx> {
        self.body
    }
}

impl<'tcx> BitDenotation<'tcx> for DefinitelyInitializedLocal<'_, 'tcx> {
    type Idx = mir::Local;
    fn name() -> &'static str {
        "definitely_initialized_local"
    }

    fn bits_per_block(&self) -> usize {
        self.body.local_decls.len()
    }

    fn start_block_effect(&self, on_entry: &mut BitSet<mir::Local>) {
        on_entry.clear();
        for arg in self.body.args_iter() {
            on_entry.insert(arg);
        }
    }

    fn statement_effect(&self, trans: &mut GenKillSet<mir::Local>, loc: mir::Location) {
        let stmt = &self.body[loc.block].statements[loc.statement_index];

        if let StatementKind::Assign(box (place, _)) = stmt.kind {
            if place.projection.len() == 0 {
                trans.gen(place.local);
            } else {
                todo!("{:?}", stmt)
            }
        }
    }

    fn terminator_effect(&self, _trans: &mut GenKillSet<mir::Local>, _loc: mir::Location) {
        // TODO: at least function calls should have effect here
    }

    fn propagate_call_return(
        &self,
        _in_out: &mut BitSet<mir::Local>,
        _call_bb: mir::BasicBlock,
        _dest_bb: mir::BasicBlock,
        _dest_place: &mir::Place<'tcx>,
    ) {
        // Nothing to do when a call returns successfully
    }
}

impl BottomValue for DefinitelyInitializedLocal<'_, '_> {
    const BOTTOM_VALUE: bool = true;
}
