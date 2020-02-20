use crate::context::LiquidRustCtxt;
use crate::refinements::{Operand, Pred};
use crate::syntax::ast::{BinOpKind, UnOpKind};
use rustc::mir;
use rustc_data_structures::work_queue::WorkQueue;
use rustc_index::bit_set::BitSet;
use rustc_index::vec::IndexVec;

pub fn do_conditionals_analysis<'lr, 'tcx>(
    cx: &LiquidRustCtxt<'lr, 'tcx>,
    body: &mir::Body<'tcx>,
) -> IndexVec<mir::BasicBlock, Vec<&'lr Pred<'lr, 'tcx>>> {
    let cond_data = gather_conds(cx, body);
    let mut analysis = ConditionalsAnalysis::new(body, &cond_data);
    analysis.iterate_to_fixpoint();

    let mut results = IndexVec::new();
    for entry_set in analysis.entry_sets {
        let mut preds = Vec::new();
        for ci in entry_set.iter() {
            preds.push(cond_data.conds[ci]);
        }
        results.push(preds);
    }
    results
}

struct ConditionalsAnalysis<'a, 'lr, 'tcx> {
    body: &'a mir::Body<'tcx>,
    entry_sets: IndexVec<mir::BasicBlock, BitSet<CondIndex>>,
    cond_data: &'a CondData<'lr, 'tcx>,
}

impl<'a, 'lr, 'tcx> ConditionalsAnalysis<'a, 'lr, 'tcx> {
    pub fn new(body: &'a mir::Body<'tcx>, cond_data: &'a CondData<'lr, 'tcx>) -> Self {
        let bits_per_block = cond_data.conds.len();
        let bottom = BitSet::new_filled(bits_per_block);
        let mut entry_sets = IndexVec::from_elem(bottom, body.basic_blocks());

        // Apply initial block effect
        entry_sets[mir::START_BLOCK].clear();

        ConditionalsAnalysis {
            body,
            entry_sets,
            cond_data,
        }
    }

    pub fn iterate_to_fixpoint(&mut self) {
        let mut queue: WorkQueue<mir::BasicBlock> =
            WorkQueue::with_none(self.body.basic_blocks().len());

        for (bb, _) in mir::traversal::reverse_postorder(self.body) {
            queue.insert(bb);
        }

        while let Some(bb) = queue.pop() {
            if let Some(terminator) = &self.body[bb].terminator {
                match &terminator.kind {
                    mir::TerminatorKind::SwitchInt { targets, .. } => {
                        for (target, ci) in targets.iter().zip(&self.cond_data.lookup[bb]) {
                            let mut out = self.entry_sets[bb].clone();
                            out.insert(*ci);
                            self.propagate_bits_into_entry_set_for(out, *target, &mut queue);
                        }
                    }
                    mir::TerminatorKind::Assert { target, .. } => {
                        let mut out = self.entry_sets[bb].clone();
                        out.insert(self.cond_data.lookup[bb][0]);
                        self.propagate_bits_into_entry_set_for(out, *target, &mut queue);
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
                            let out = self.entry_sets[bb].clone();
                            self.propagate_bits_into_entry_set_for(out, *target, &mut queue);
                        }
                    }
                    mir::TerminatorKind::Goto { target } => {
                        let out = self.entry_sets[bb].clone();
                        self.propagate_bits_into_entry_set_for(out, *target, &mut queue);
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
    }

    fn propagate_bits_into_entry_set_for(
        &mut self,
        out: BitSet<CondIndex>,
        bb: mir::BasicBlock,
        queue: &mut WorkQueue<mir::BasicBlock>,
    ) {
        let entry_set = &mut self.entry_sets[bb];
        let set_changed = entry_set.intersect(&out);
        if set_changed {
            queue.insert(bb);
        }
    }
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
