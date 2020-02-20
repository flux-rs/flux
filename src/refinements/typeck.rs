extern crate rustc_mir;

use super::{Binder, Operand, Place, Pred, ReftType, Scalar, Var};
use crate::context::LiquidRustCtxt;
use crate::smtlib2::{SmtRes, Solver};
use crate::syntax::ast::{BinOpKind, UnOpKind};
use rustc::mir::{self, Constant, Rvalue, StatementKind, TerminatorKind};
use rustc::ty::{self, Ty};
use rustc_data_structures::work_queue::WorkQueue;
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
    conditionals: IndexVec<mir::BasicBlock, Vec<&'lr Pred<'lr, 'tcx>>>,
}

impl<'a, 'lr, 'tcx> ReftChecker<'a, 'lr, 'tcx> {
    pub fn new(cx: &'a LiquidRustCtxt<'lr, 'tcx>, body_id: BodyId) -> Self {
        let reft_types = cx.local_decls(body_id).clone();
        let mir = cx.optimized_mir(body_id);
        let cursor = initialized_locals(cx, cx.hir().body_owner_def_id(body_id));
        let conditionals = conditionals(cx, mir);
        ReftChecker {
            cx,
            mir,
            reft_types,
            cursor,
            conditionals,
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
                env.push(self.cx.open_pred(pred, Operand::from_local(local)));
            }
        }
        for conditional in &self.conditionals[block] {
            env.push(conditional);
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
                        println!("    {:?}", env);
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
                            let values: Vec<_> = args.iter().map(Operand::from_mir).collect();
                            let (formals, ret) = self.cx.split_fun_type(fun_type, &values);

                            println!("    {:?}", env);
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
                    | TerminatorKind::Goto { .. }
                    | TerminatorKind::SwitchInt { .. }
                    | TerminatorKind::Assert { .. }
                    | TerminatorKind::Abort
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable => {}
                    _ => todo!("{:?}", terminator.kind),
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

    fn operand_reft_type(&self, operand: &mir::Operand<'tcx>) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let reft_ty = match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                match place.ty(self, self.cx.tcx()).ty.kind {
                    ty::FnDef(def_id, _) => return self.cx.reft_type_for(def_id),
                    ty::FnPtr(..) => todo!(),
                    _ => {
                        let place = Place {
                            var: Var::Local(place.local),
                            projection: place.projection,
                        };
                        let place = self.cx.mk_operand(Operand::Place(place));
                        self.cx
                            .mk_reft(self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, place))
                    }
                }
            }
            mir::Operand::Constant(box Constant { literal, .. }) => match literal.ty.kind {
                ty::FnDef(def_id, _) => return self.cx.reft_type_for(def_id),
                ty::FnPtr(..) => todo!(),
                _ => {
                    let scalar = match Scalar::from_const(literal) {
                        Some(scalar) => scalar,
                        None => todo!("{:?}", literal),
                    };
                    let constant = self.cx.mk_operand(Operand::Constant(literal.ty, scalar));
                    self.cx
                        .mk_reft(self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, constant))
                }
            },
        };
        Binder::bind(reft_ty)
    }

    pub fn rvalue_reft_type(
        &self,
        ty: Ty<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let reft_ty = match rvalue {
            Rvalue::Use(operand) => return self.operand_reft_type(operand),
            // v:{v.0 == lhs + rhs}
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let op = mir_op_to_refine_op(*op);
                let lhs = self.cx.mk_operand(Operand::from_mir(lhs));
                let rhs = self.cx.mk_operand(Operand::from_mir(rhs));
                let bin = self.cx.mk_binary(lhs, op, rhs);
                let ty = ty.tuple_fields().next().unwrap();
                let bin = self.cx.mk_binary(
                    self.cx.mk_operand(Operand::Place(self.cx.mk_place_field(
                        Place::nu(),
                        mir::Field::new(0),
                        ty,
                    ))),
                    BinOpKind::Eq,
                    bin,
                );
                self.cx.mk_reft(bin)
            }
            // v:{v == lhs + rhs}
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let op = mir_op_to_refine_op(*op);
                let lhs = self.cx.mk_operand(Operand::from_mir(lhs));
                let rhs = self.cx.mk_operand(Operand::from_mir(rhs));
                let bin = self.cx.mk_binary(lhs, op, rhs);
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
            let sort = match &place.ty(self, self.cx.tcx()).kind {
                ty::Int(..) => "Int",
                ty::Bool => "Bool",
                ty @ _ => todo!("{:?}", ty),
            };
            solver.declare_const(&place, sort)?;
        }

        for pred in env {
            solver.assert(pred)?;
        }

        let not_rhs = Pred::Unary(UnOpKind::Not, rhs);
        solver.assert(lhs)?;
        solver.assert(&not_rhs)?;

        let b = solver.check_sat()?;
        println!("      {:?} => {:?}  {}", lhs, rhs, !b);
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

fn conditionals<'lr, 'tcx>(
    cx: &LiquidRustCtxt<'lr, 'tcx>,
    body: &mir::Body<'tcx>,
) -> IndexVec<mir::BasicBlock, Vec<&'lr Pred<'lr, 'tcx>>> {
    let mut dirty_queue: WorkQueue<mir::BasicBlock> =
        WorkQueue::with_none(body.basic_blocks().len());

    let cond_data: CondData = gather_conds(cx, body);
    let bits_per_block = cond_data.conds.len();
    let bottom = BitSet::new_filled(bits_per_block);

    let mut entry_sets = IndexVec::from_elem(bottom, body.basic_blocks());
    entry_sets[mir::START_BLOCK].clear();

    for (bb, _) in mir::traversal::reverse_postorder(body) {
        dirty_queue.insert(bb);
    }

    while let Some(bb) = dirty_queue.pop() {
        if let Some(terminator) = &body[bb].terminator {
            match &terminator.kind {
                mir::TerminatorKind::SwitchInt { targets, .. } => {
                    for (target, ci) in targets.iter().zip(&cond_data.lookup[bb]) {
                        let mut temp = entry_sets[bb].clone();
                        temp.insert(*ci);
                        if entry_sets[*target].intersect(&temp) {
                            dirty_queue.insert(*target);
                        }
                    }
                }
                mir::TerminatorKind::Assert { target, .. } => {
                    let mut temp = entry_sets[bb].clone();
                    temp.insert(cond_data.lookup[bb][0]);
                    if entry_sets[*target].intersect(&temp) {
                        dirty_queue.insert(*target);
                    }
                }
                mir::TerminatorKind::Call {
                    destination,
                    cleanup,
                    ..
                } => {
                    if let Some(_) = cleanup {
                        todo!();
                    }
                    if let Some((_, target)) = destination {
                        let temp = &entry_sets[bb].clone();
                        if entry_sets[*target].intersect(&temp) {
                            dirty_queue.insert(*target);
                        }
                    }
                }
                mir::TerminatorKind::Goto { target } => {
                    let temp = &entry_sets[bb].clone();
                    if entry_sets[*target].intersect(&temp) {
                        dirty_queue.insert(*target);
                    }
                }
                mir::TerminatorKind::Return
                | mir::TerminatorKind::Resume
                | mir::TerminatorKind::Abort
                | mir::TerminatorKind::GeneratorDrop
                | mir::TerminatorKind::Unreachable => {}
                _ => todo!("{:?}", terminator.kind),
            }
        }
    }
    let mut results = IndexVec::new();
    for entry_set in entry_sets {
        let mut preds = Vec::new();
        for ci in entry_set.iter() {
            preds.push(cond_data.conds[ci]);
        }
        results.push(preds);
    }
    results
}

newtype_index! {
    pub struct CondIndex {
        DEBUG_FORMAT = "ci{}"
    }
}

#[derive(Debug)]
struct CondData<'lr, 'tcx> {
    conds: IndexVec<CondIndex, &'lr Pred<'lr, 'tcx>>,
    lookup: IndexVec<mir::BasicBlock, Vec<CondIndex>>,
}

fn gather_conds<'lr, 'tcx>(
    cx: &LiquidRustCtxt<'lr, 'tcx>,
    body: &mir::Body<'tcx>,
) -> CondData<'lr, 'tcx> {
    let mut cond_data = CondData {
        conds: IndexVec::new(),
        lookup: IndexVec::new(),
    };
    for bb_data in body.basic_blocks().iter() {
        if let Some(terminator) = &bb_data.terminator {
            let mut lookup = Vec::new();
            match &terminator.kind {
                mir::TerminatorKind::SwitchInt {
                    discr,
                    values,
                    switch_ty,
                    ..
                } => {
                    let discr = cx.mk_operand(Operand::from_mir(discr));
                    let mut disj = cx.pred_false;
                    for value in values.iter() {
                        let value = cx.mk_operand(Operand::from_bits(cx.tcx(), *value, switch_ty));
                        let cond = cx.mk_binary(discr, BinOpKind::Eq, value);
                        disj = cx.mk_binary(disj, BinOpKind::Or, cond);
                        lookup.push(cond_data.conds.next_index());
                        cond_data.conds.push(cond);
                    }
                    let neg = cx.mk_unary(UnOpKind::Not, disj);
                    lookup.push(cond_data.conds.next_index());
                    cond_data.conds.push(neg);
                }
                mir::TerminatorKind::Assert { cond, expected, .. } => {
                    let mut cond = cx.mk_operand(Operand::from_mir(cond));
                    if !expected {
                        cond = cx.mk_unary(UnOpKind::Not, cond);
                    }
                    lookup.push(cond_data.conds.next_index());
                    cond_data.conds.push(cond);
                }
                _ => {}
            }
            cond_data.lookup.push(lookup);
        }
    }
    cond_data
}
