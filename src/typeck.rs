extern crate rustc_mir;

use super::context::LiquidRustCtxt;
use super::refinements::{Place, Pred, Var};
use super::smtlib2::{SmtRes, Solver};
use super::syntax::ast::{BinOpKind, UnOpKind};
use rustc::mir::{self, Constant, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc::ty::{self, Ty};
use rustc_hir::BodyId;
use rustc_index::{bit_set::BitSet, vec::Idx};
use rustc_mir::dataflow::{
    do_dataflow, BitDenotation, BottomValue, DataflowResultsCursor, DebugFormatted, GenKillSet,
};
use std::collections::{HashMap, HashSet};

pub fn check_body<'a, 'tcx>(cx: &'a LiquidRustCtxt<'a, 'tcx>, body_id: BodyId) {
    let mir = cx.optimized_mir(body_id);
    let local_decls = cx.local_decls(body_id);
    let mut refines = local_decls.clone();

    let dead_unwinds = BitSet::new_empty(mir.basic_blocks().len());
    let def_id = cx.hir().body_owner_def_id(body_id);
    let initialized_result = do_dataflow(
        cx.tcx(),
        mir,
        def_id,
        &[],
        &dead_unwinds,
        DefinitelyInitializedLocal::new(mir),
        |bd, p| DebugFormatted::new(&bd.body().local_decls[p]),
    );

    let mut cursor = DataflowResultsCursor::new(initialized_result, mir);

    for (bb, bbd) in mir.basic_blocks().iter_enumerated() {
        println!("bb{}:", bb.index());
        for (i, statement) in bbd.statements.iter().enumerate() {
            let loc = mir::Location {
                block: bb,
                statement_index: i,
            };
            cursor.seek(loc);
            let mut env = HashMap::new();
            for local in cursor.get().iter() {
                if let Some(refine) = refines.get(&local) {
                    env.insert(local, refine);
                }
            }
            println!("  {:?}\n", statement);
            match &statement.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    let ty = place.ty(mir, cx.tcx()).ty;
                    let local = place.local;
                    let lhs = *b(cx, ty, rvalue).open(&[local]);
                    if let Some(rhs) = local_decls.get(&local) {
                        let r = check(&env, &lhs, rhs);
                        if let Err(e) = r {
                            println!("{:?}", e);
                        }
                    } else if !mir.local_decls[local].is_user_variable() {
                        refines.insert(local, lhs);
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
        if let Some(terminator) = &bbd.terminator {
            println!("  {:?}\n", terminator.kind);
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {}
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

fn check<'tcx>(
    env: &HashMap<mir::Local, &Pred<'tcx>>,
    lhs: &Pred<'tcx>,
    rhs: &Pred<'tcx>,
) -> SmtRes<()> {
    let mut solver = Solver::default(())?;
    let mut places = HashSet::new();
    for refine in env.values().chain(&[lhs, rhs]) {
        refine.iter_places(|place| {
            places.insert(place);
        })
    }

    for place in places {
        solver.declare_const(&place, "Int")?;
    }

    for refine in env.values() {
        println!("    {}", refine.to_smt_str());
        solver.assert(refine)?;
    }
    let not_rhs = Pred::Unary(UnOpKind::Not, box rhs.clone());
    solver.assert(lhs)?;
    solver.assert(&not_rhs)?;
    println!("    {}", lhs.to_smt_str());
    println!("    {}", not_rhs.to_smt_str());

    let b = solver.check_sat()?;
    println!("    unsat {}\n", !b);
    Ok(())
}

pub fn b<'tcx>(cx: &LiquidRustCtxt<'_, 'tcx>, ty: Ty<'tcx>, rvalue: &Rvalue<'tcx>) -> Pred<'tcx> {
    match rvalue {
        // v:{v == operand}
        Rvalue::Use(operand) => match ty.kind {
            ty::FnDef(_, _) | ty::FnPtr(_) => todo!(),
            _ => {
                let operand = mk_operand(operand);
                Pred::Binary(Pred::nu(), BinOpKind::Eq, operand)
            }
        },
        // v:{v.0 == lhs + rhs}
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let op = mir_op_to_refine_op(*op);
            let bin = box Pred::Binary(mk_operand(lhs), op, mk_operand(rhs));
            let ty = ty.tuple_fields().next().unwrap();
            Pred::Binary(
                cx.mk_place_field(Place::nu(), mir::Field::new(0), ty),
                BinOpKind::Eq,
                bin,
            )
        }
        // v:{v == lhs + rhs}
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let op = mir_op_to_refine_op(*op);
            let bin = box Pred::Binary(mk_operand(lhs), op, mk_operand(rhs));
            Pred::Binary(Pred::nu(), BinOpKind::Eq, bin)
        }
        _ => todo!("{:?}", rvalue),
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

fn mk_operand<'tcx>(operand: &Operand<'tcx>) -> Box<Pred<'tcx>> {
    box match operand {
        Operand::Copy(place) | Operand::Move(place) => Pred::Place(Place {
            var: Var::Free(place.local),
            projection: place.projection,
        }),
        Operand::Constant(box Constant { literal, .. }) => match literal.val {
            ty::ConstKind::Value(val) => Pred::Constant(literal.ty, val),
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
