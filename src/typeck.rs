extern crate rustc_mir;

use super::context::LiquidRustCtxt;
use super::refinements::{Place, Pred, ReftType, Value, Var};
use super::smtlib2::{SmtRes, Solver};
use super::syntax::ast::{BinOpKind, UnOpKind};
use rustc::mir::{self, Constant, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc::ty::{self, Ty};
use rustc_hir::BodyId;
use rustc_index::vec::IndexVec;
use rustc_index::{bit_set::BitSet, vec::Idx};
use rustc_mir::dataflow::{
    do_dataflow, BitDenotation, BottomValue, DataflowResultsCursor, DebugFormatted, GenKillSet,
};
use std::collections::{HashMap, HashSet};

pub fn check_body(cx: &LiquidRustCtxt<'_, '_>, body_id: BodyId) {
    ReftChecker::new(cx, body_id).check_body();
}

struct ReftChecker<'a, 'b, 'tcx> {
    cx: &'b LiquidRustCtxt<'a, 'tcx>,
    body_id: BodyId,
    mir: &'b mir::Body<'tcx>,
    reft_types: HashMap<mir::Local, &'a ReftType<'a, 'tcx>>,
}

impl<'a, 'b, 'tcx> ReftChecker<'a, 'b, 'tcx> {
    pub fn new(cx: &'b LiquidRustCtxt<'a, 'tcx>, body_id: BodyId) -> Self {
        let reft_types = cx.local_decls(body_id).clone();
        let mir = cx.optimized_mir(body_id);
        ReftChecker {
            cx,
            mir,
            body_id,
            reft_types,
        }
    }

    pub fn check_body(&mut self) {
        let mut cursor = self.initialized_locals();

        for (bb, bbd) in self.mir.basic_blocks().iter_enumerated() {
            print!("\nbb{}:", bb.index());
            for (i, statement) in bbd.statements.iter().enumerate() {
                let loc = mir::Location {
                    block: bb,
                    statement_index: i,
                };
                cursor.seek(loc);
                let mut env = HashMap::new();
                for local in cursor.get().iter() {
                    if let Some(pred) = self.reft_types.get(&local).and_then(|rt| rt.pred()) {
                        env.insert(local, pred);
                    }
                }
                println!("\n  {:?}", statement);
                match &statement.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        let ty = place.ty(self, self.cx.tcx()).ty;
                        let local = place.local;
                        let lhs = self.rvalue_reft_type(ty, rvalue);
                        if let Some(rhs) = self.reft_types.get(&local) {
                            self.check_subtyping(&env, lhs, rhs, Some(local));
                        } else if !self.mir.local_decls[local].is_user_variable() {
                            println!("    infer {:?} for {:?}", lhs, local);
                            self.reft_types.insert(local, lhs);
                        }
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop => {}
                    _ => todo!("{:?}", statement),
                }
            }
            let loc = mir::Location {
                block: bb,
                statement_index: bbd.statements.len(),
            };
            cursor.seek(loc);
            let mut env = HashMap::new();
            for local in cursor.get().iter() {
                if let Some(ReftType::Reft(pred)) = self.reft_types.get(&local) {
                    env.insert(local, *pred);
                }
            }
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
                            let mut values = args
                                .iter()
                                .map(|arg| self.operand_to_arg_value(arg))
                                .collect::<Vec<_>>();
                            values.push(Value::Local(place.local));
                            let opened = self.cx.open_reft_type(fun_type, &values);
                            let (ret, formals) = opened.split_last().unwrap();

                            for formal in formals {
                                self.check_subtyping(&env, self.cx.reft_true, formal, None);
                            }
                            println!("");
                            if let Some(rhs) = self.reft_types.get(&place.local) {
                                self.check_subtyping(&env, ret, *rhs, Some(place.local));
                            } else if !self.mir.local_decls[place.local].is_user_variable() {
                                println!("    infer {:?} for {:?}", ret, place.local);
                                self.reft_types.insert(place.local, ret);
                            }
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

    fn operand_to_arg_value(&self, operand: &Operand<'tcx>) -> Value<'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.len() > 0 {
                    bug!("values in argument position must by constants or locals")
                }
                Value::Local(place.local)
            }
            Operand::Constant(box Constant { literal, .. }) => match literal.val {
                ty::ConstKind::Value(val) => Value::Constant(literal.ty, val),
                _ => unimplemented!("{:?}", operand),
            },
        }
    }

    fn check_subtyping(
        &self,
        env: &HashMap<mir::Local, &'a Pred<'a, 'tcx>>,
        lhs: &'a ReftType<'a, 'tcx>,
        rhs: &'a ReftType<'a, 'tcx>,
        local: Option<mir::Local>,
    ) {
        match (lhs, rhs) {
            (ReftType::Fun { .. }, ReftType::Fun { .. }) => todo!(),
            (ReftType::Reft(lhs), ReftType::Reft(rhs)) => {
                let r = self.check(&env, lhs, rhs, local);
                if let Err(e) = r {
                    println!("    {:?}", e);
                }
            }
            _ => bug!("refinement types must have the same shape"),
        }
    }

    fn initialized_locals(
        &self,
    ) -> DataflowResultsCursor<'b, 'tcx, DefinitelyInitializedLocal<'b, 'tcx>> {
        let dead_unwinds = BitSet::new_empty(self.mir.basic_blocks().len());
        let def_id = self.cx.hir().body_owner_def_id(self.body_id);
        let initialized_result = do_dataflow(
            self.cx.tcx(),
            self.mir,
            def_id,
            &[],
            &dead_unwinds,
            DefinitelyInitializedLocal::new(self.mir),
            |bd, p| DebugFormatted::new(&bd.body().local_decls[p]),
        );

        DataflowResultsCursor::new(initialized_result, self.mir)
    }

    fn operand_reft_type(&self, operand: &Operand<'tcx>) -> &'a ReftType<'a, 'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                match place.ty(self, self.cx.tcx()).ty.kind {
                    ty::FnDef(def_id, _) => self.cx.reft_type_for(def_id),
                    ty::FnPtr(..) => todo!(),
                    _ => {
                        let place = Place {
                            var: Var::Free(place.local),
                            projection: place.projection,
                        };
                        let place = self.cx.mk_pred_place(place);
                        self.cx
                            .mk_reft(self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, place))
                    }
                }
            }
            Operand::Constant(box Constant { literal, .. }) => match literal.ty.kind {
                ty::FnDef(def_id, _) => self.cx.reft_type_for(def_id),
                ty::FnPtr(..) => todo!(),
                _ => match literal.val {
                    ty::ConstKind::Value(val) => {
                        let constant = self.cx.mk_constant(literal.ty, val);
                        self.cx
                            .mk_reft(self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, constant))
                    }
                    _ => unimplemented!("{:?}", operand),
                },
            },
        }
    }

    fn operand_to_value(&self, operand: &Operand<'tcx>) -> &'a Pred<'a, 'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.cx.mk_pred_place(Place {
                var: Var::Free(place.local),
                projection: place.projection,
            }),
            Operand::Constant(box Constant { literal, .. }) => match literal.val {
                ty::ConstKind::Value(val) => self.cx.mk_constant(literal.ty, val),
                _ => unimplemented!("{:?}", operand),
            },
        }
    }

    pub fn rvalue_reft_type(&self, ty: Ty<'tcx>, rvalue: &Rvalue<'tcx>) -> &'a ReftType<'a, 'tcx> {
        match rvalue {
            // v:{v == operand}
            Rvalue::Use(operand) => self.operand_reft_type(operand),
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
        }
    }

    fn check(
        &self,
        env: &HashMap<mir::Local, &'a Pred<'a, 'tcx>>,
        mut lhs: &'a Pred<'a, 'tcx>,
        mut rhs: &'a Pred<'a, 'tcx>,
        local: Option<mir::Local>,
    ) -> SmtRes<()> {
        let mut solver = Solver::default(())?;
        let mut places = HashSet::new();
        let preds = env
            .iter()
            .map(|(local, pred)| self.cx.open_pred_with_locals(pred, &[*local]))
            .collect::<Vec<_>>();

        for pred in &preds {
            pred.iter_places(|place| {
                places.insert(place);
            })
        }

        if let Some(local) = local {
            lhs = self.cx.open_pred_with_locals(lhs, &[local]);
            rhs = self.cx.open_pred_with_locals(rhs, &[local]);
        }

        lhs.iter_places(|place| {
            places.insert(place);
        });

        lhs.iter_places(|place| {
            places.insert(place);
        });

        for place in places {
            solver.declare_const(&place, "Int")?;
        }

        for pred in preds {
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

impl<'a, 'tcx> BitDenotation<'tcx> for DefinitelyInitializedLocal<'a, 'tcx> {
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

impl<'a, 'tcx> BottomValue for DefinitelyInitializedLocal<'a, 'tcx> {
    const BOTTOM_VALUE: bool = true;
}
