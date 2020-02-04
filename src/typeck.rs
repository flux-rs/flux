extern crate rustc_mir;

use super::context::LiquidRustCtxt;
use super::refinements::{FnRefines, Refine, RefineCtxt};
use super::smtlib2::{Expr2Smt, SmtInfo, SmtRes, Solver};
use super::syntax::ast::{BinOpKind, UnOpKind};
use rustc::mir::{self, Constant, Operand, Rvalue, StatementKind};
use rustc::ty::ConstKind;
use rustc_index::bit_set::BitSet;
use rustc_mir::dataflow::{
    do_dataflow, BitDenotation, BottomValue, DataflowResultsCursor, DebugFormatted, GenKillSet,
};
use std::collections::HashMap;

pub fn checks<'a, 'rcx, 'tcx>(
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    fn_refines: &FnRefines<'rcx, 'tcx>,
    mir: &mir::Body<'tcx>,
) {
    let mut refines = fn_refines.local_decls.clone();

    let dead_unwinds = BitSet::new_empty(mir.basic_blocks().len());
    let def_id = cx.hir().body_owner_def_id(fn_refines.body_id);
    let initialized_result = do_dataflow(
        *cx.tcx(),
        mir,
        def_id,
        &[],
        &dead_unwinds,
        DefinitelyInitializedLocal::new(mir),
        |bd, p| DebugFormatted::new(&bd.body().local_decls[p]),
    );

    let mut cursor = DataflowResultsCursor::new(initialized_result, mir);

    for (bb, bbd) in mir.basic_blocks().iter_enumerated() {
        for (i, statement) in bbd.statements.iter().enumerate() {
            let loc = mir::Location {
                block: bb,
                statement_index: i,
            };
            cursor.seek(loc);
            let mut env = HashMap::new();
            for local in cursor.get().iter() {
                if let Some(refine) = refines.get(&local) {
                    env.insert(local, *refine);
                }
            }
            match &statement.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    if place.projection.len() == 0 {
                        let local = place.local;
                        let lhs = b(rcx, rvalue);
                        if let Some(rhs) = fn_refines.local_decls.get(&local) {
                            let r = check(rcx, &env, lhs, rhs, local);
                            println!("{:?}", r);
                        } else if !mir.local_decls[local].is_user_variable() {
                            refines.insert(local, lhs);
                        }
                    }
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop => {}
                _ => unimplemented!(),
            }
        }
    }
}

fn check<'rcx, 'tcx>(
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    env: &HashMap<mir::Local, &'rcx Refine<'rcx, 'tcx>>,
    lhs: &'rcx Refine<'rcx, 'tcx>,
    rhs: &'rcx Refine<'rcx, 'tcx>,
    local: mir::Local,
) -> SmtRes<()> {
    let mut solver = Solver::default(())?;
    let info = SmtInfo { nu: local };
    if !env.contains_key(&local) {
        solver.declare_const(&format!("{:?}", local), "Int")?;
    }
    for local in env.keys() {
        solver.declare_const(&format!("{:?}", local), "Int")?;
    }
    for refine in env.values() {
        let mut v = Vec::new();
        refine.expr_to_smt2(&mut v, info)?;
        println!("{:?}", String::from_utf8(v));
        solver.assert_with(refine, info)?;
    }
    let mut v = Vec::new();
    lhs.expr_to_smt2(&mut v, info)?;
    println!("{:?}", String::from_utf8(v));
    solver.assert_with(lhs, info)?;
    solver.assert_with(rcx.mk_not(rhs), info)?;
    let b = solver.check_sat()?;
    println!("unsat {}\n", !b);
    Ok(())
}

pub fn b<'rcx, 'tcx>(
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> &'rcx Refine<'rcx, 'tcx> {
    let value = match rvalue {
        Rvalue::Use(operand) => mk_operand(rcx, operand),
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let op = mir_op_to_refine_op(op);
            rcx.mk_binary(mk_operand(rcx, lhs), op, mk_operand(rcx, rhs))
        }
        Rvalue::UnaryOp(op, operand) => mk_unary(rcx, op, operand),
        _ => unimplemented!("{:?}", rvalue),
    };
    rcx.mk_binary(rcx.nu, BinOpKind::Eq, value)
}

pub fn mk_unary<'rcx, 'tcx>(
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    op: &mir::UnOp,
    operand: &Operand<'tcx>,
) -> &'rcx Refine<'rcx, 'tcx> {
    let op = match op {
        mir::UnOp::Not => UnOpKind::Not,
        mir::UnOp::Neg => unimplemented!(),
    };
    rcx.mk_unary(op, mk_operand(rcx, operand))
}

pub fn mir_op_to_refine_op<'rcx, 'tcx>(op: &mir::BinOp) -> BinOpKind {
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

pub fn mk_operand<'rcx, 'tcx>(
    rcx: &'rcx RefineCtxt<'rcx, 'tcx>,
    operand: &Operand<'tcx>,
) -> &'rcx Refine<'rcx, 'tcx> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => rcx.mk_place(*place),
        Operand::Constant(box Constant { literal, .. }) => match literal.val {
            ConstKind::Value(val) => rcx.mk_constant(literal.ty, val),
            _ => unimplemented!("{:?}", operand),
        },
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

        match stmt.kind {
            StatementKind::Assign(box (place, _)) => {
                if place.projection.len() == 0 {
                    trans.gen(place.local);
                } else {
                    unimplemented!("{:?}", stmt)
                }
            }
            _ => (),
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
