extern crate rustc_mir;

use super::context::LiquidRustCtxt;
use super::refinements::{FnRefines, Place, Refine, Var};
use super::smtlib2::{SmtRes, Solver};
use super::syntax::ast::{BinOpKind, UnOpKind};
use rustc::mir::{self, Constant, Operand, Rvalue, StatementKind};
use rustc::ty::{self, Ty};
use rustc_index::{bit_set::BitSet, vec::Idx};
use rustc_mir::dataflow::{
    do_dataflow, BitDenotation, BottomValue, DataflowResultsCursor, DebugFormatted, GenKillSet,
};
use std::collections::{HashMap, HashSet};

pub fn checks<'a, 'tcx>(
    cx: &'a LiquidRustCtxt<'a, 'tcx>,
    fn_refines: &FnRefines<'tcx>,
    mir: &mir::Body<'tcx>,
) {
    let mut refines = fn_refines.local_decls.clone();

    let dead_unwinds = BitSet::new_empty(mir.basic_blocks().len());
    let def_id = cx.hir().body_owner_def_id(fn_refines.body_id);
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
            match &statement.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    let ty = place.ty(mir, cx.tcx()).ty;
                    let local = place.local;
                    let lhs = *b(cx, ty, rvalue).open(&[local]);
                    if let Some(rhs) = fn_refines.local_decls.get(&local) {
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
                _ => unimplemented!(),
            }
        }
    }
}

fn check<'tcx>(
    env: &HashMap<mir::Local, &Refine<'tcx>>,
    lhs: &Refine<'tcx>,
    rhs: &Refine<'tcx>,
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

    for (_, refine) in env {
        println!("{}", refine.to_smt_str());
        solver.assert(refine)?;
    }
    let not_rhs = Refine::Unary(UnOpKind::Not, box rhs.clone());
    solver.assert(lhs)?;
    solver.assert(&not_rhs)?;
    println!("{}", lhs.to_smt_str());
    println!("{}", not_rhs.to_smt_str());

    let b = solver.check_sat()?;
    println!("unsat {}\n", !b);
    Ok(())
}

pub fn b<'tcx>(cx: &LiquidRustCtxt<'_, 'tcx>, ty: Ty<'tcx>, rvalue: &Rvalue<'tcx>) -> Refine<'tcx> {
    match rvalue {
        // v:{v == operand}
        Rvalue::Use(operand) => {
            let operand = mk_operand(operand);
            Refine::Binary(Refine::nu(), BinOpKind::Eq, operand)
        }
        // v:{v.0 == lhs + rhs}
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let op = mir_op_to_refine_op(op);
            let bin = box Refine::Binary(mk_operand(lhs), op, mk_operand(rhs));
            let ty = ty.tuple_fields().next().unwrap();
            Refine::Binary(
                cx.mk_place_field(Place::nu(), mir::Field::new(0), ty),
                BinOpKind::Eq,
                bin,
            )
        }
        // v:{v == lhs + rhs}
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let op = mir_op_to_refine_op(op);
            let bin = box Refine::Binary(mk_operand(lhs), op, mk_operand(rhs));
            Refine::Binary(Refine::nu(), BinOpKind::Eq, bin)
        }
        _ => unimplemented!("{:?}", rvalue),
    }
}

pub fn mir_op_to_refine_op<'tcx>(op: &mir::BinOp) -> BinOpKind {
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

fn mk_operand<'tcx>(operand: &Operand<'tcx>) -> Box<Refine<'tcx>> {
    box match operand {
        Operand::Copy(place) | Operand::Move(place) => Refine::Place(Place {
            var: Var::Free(place.local),
            projection: place.projection,
        }),
        Operand::Constant(box Constant { literal, .. }) => match literal.val {
            ty::ConstKind::Value(val) => Refine::Constant(literal.ty, val),
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
