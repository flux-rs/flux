extern crate rustc_mir;

use super::dataflow;
use super::{Binder, Operand, Place, Pred, ReftType, Scalar, Var};
use crate::context::LiquidRustCtxt;
use crate::smtlib2::{SmtRes, Solver};
use crate::syntax::ast::{BinOpKind, UnOpKind};
use rustc_hir::BodyId;
use rustc_index::vec::IndexVec;
use rustc_index::{bit_set::BitSet, vec::Idx};
use rustc_middle::mir::{self, Constant, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Ty};
use rustc_mir::dataflow::{
    Analysis, AnalysisDomain, BottomValue, GenKill, GenKillAnalysis, ResultsCursor,
};
use std::collections::{HashMap, HashSet};

pub fn check_body(cx: &LiquidRustCtxt<'_, '_>, body_id: BodyId) {
    ReftChecker::new(cx, body_id).check_body();
}

struct ReftChecker<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustCtxt<'lr, 'tcx>,
    mir: &'a mir::Body<'tcx>,
    reft_types: HashMap<mir::Local, Binder<&'lr ReftType<'lr, 'tcx>>>,
    cursor: ResultsCursor<'a, 'tcx, DefinitelyInitializedLocal<'a, 'tcx>>,
    conditionals: IndexVec<mir::BasicBlock, Vec<&'lr Pred<'lr, 'tcx>>>,
}

impl<'a, 'lr, 'tcx> ReftChecker<'a, 'lr, 'tcx> {
    pub fn new(cx: &'a LiquidRustCtxt<'lr, 'tcx>, body_id: BodyId) -> Self {
        let reft_types = cx.local_decls(body_id).clone();
        let mir = cx.optimized_mir(body_id);
        let def_id = cx.hir().body_owner_def_id(body_id);
        let cursor = DefinitelyInitializedLocal::new(mir)
            .into_engine(cx.tcx(), mir, def_id.to_def_id())
            .iterate_to_fixpoint()
            .into_results_cursor(mir);
        let conditionals = dataflow::do_conditionals_analysis(cx, mir);
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
        self.cursor.seek_before(loc);
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
            (ReftType::Reft(_, lhs), ReftType::Reft(_, rhs)) => {
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
                let ty = place.ty(self, self.cx.tcx()).ty;
                match ty.kind {
                    ty::FnDef(def_id, _) => return self.cx.reft_type_for(def_id),
                    ty::FnPtr(..) => todo!(),
                    _ => {
                        let place = Place {
                            var: Var::Local(place.local),
                            projection: place.projection,
                        };
                        let place = self.cx.mk_operand(Operand::Place(place));
                        self.cx
                            .mk_reft(ty, self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, place))
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
                    let ty = literal.ty;
                    let constant = self.cx.mk_operand(Operand::Constant(literal.ty, scalar));
                    self.cx
                        .mk_reft(ty, self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, constant))
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
                let op = mir_binop_to_refine_op(*op);
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
                self.cx.mk_reft(ty, bin)
            }
            // v:{v == lhs + rhs}
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let op = mir_binop_to_refine_op(*op);
                let lhs = self.cx.mk_operand(Operand::from_mir(lhs));
                let rhs = self.cx.mk_operand(Operand::from_mir(rhs));
                let bin = self.cx.mk_binary(lhs, op, rhs);
                let bin = self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, bin);
                self.cx.mk_reft(ty, bin)
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
        println!("      {{{:?}}} <: {{{:?}}}  {}", lhs, rhs, !b);
        Ok(())
    }
}

impl<'tcx> mir::HasLocalDecls<'tcx> for ReftChecker<'_, '_, 'tcx> {
    fn local_decls(&self) -> &IndexVec<mir::Local, mir::LocalDecl<'tcx>> {
        &self.mir.local_decls
    }
}

pub fn mir_binop_to_refine_op(op: mir::BinOp) -> BinOpKind {
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
        | mir::BinOp::Offset => todo!("{:?}", op),
    }
}

struct DefinitelyInitializedLocal<'a, 'tcx> {
    body: &'a mir::Body<'tcx>,
}

impl<'a, 'tcx> DefinitelyInitializedLocal<'a, 'tcx> {
    pub fn new(body: &'a mir::Body<'tcx>) -> Self {
        DefinitelyInitializedLocal { body }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for DefinitelyInitializedLocal<'_, 'tcx> {
    type Idx = mir::Local;

    const NAME: &'static str = "definitely_init_local";

    fn bits_per_block(&self, _: &mir::Body<'tcx>) -> usize {
        self.body.local_decls.len()
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, on_entry: &mut BitSet<Self::Idx>) {
        on_entry.clear();
        for arg in self.body.args_iter() {
            on_entry.insert(arg);
        }
    }

    fn pretty_print_idx(&self, w: &mut impl std::io::Write, mpi: Self::Idx) -> std::io::Result<()> {
        write!(w, "{:?}", self.body.local_decls[mpi])
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for DefinitelyInitializedLocal<'_, 'tcx> {
    fn statement_effect(
        &self,
        trans: &mut impl GenKill<mir::Local>,
        stmt: &mir::Statement<'tcx>,
        _loc: mir::Location,
    ) {
        if let StatementKind::Assign(box (place, _)) = stmt.kind {
            if place.projection.len() == 0 {
                trans.gen(place.local);
            } else {
                todo!("{:?}", stmt)
            }
        }
    }

    fn terminator_effect(
        &self,
        trans: &mut impl GenKill<mir::Local>,
        terminator: &mir::Terminator<'tcx>,
        _loc: mir::Location,
    ) {
        // TODO: at least function calls should have effect here
        if_chain! {
            if let TerminatorKind::Call {destination, ..} = &terminator.kind;
            if let Some((place, _)) = destination;
            then {
                if place.projection.len() == 0 {
                    trans.gen(place.local);
                } else {
                    todo!("{:?}", terminator)
                }
            }
        }
    }

    fn call_return_effect(
        &self,
        _trans: &mut impl GenKill<Self::Idx>,
        _block: mir::BasicBlock,
        _func: &mir::Operand<'tcx>,
        _args: &[mir::Operand<'tcx>],
        _dest_place: mir::Place<'tcx>,
    ) {
        // TODO We should initialize the dest_place here
    }
}

impl BottomValue for DefinitelyInitializedLocal<'_, '_> {
    const BOTTOM_VALUE: bool = true;
}
