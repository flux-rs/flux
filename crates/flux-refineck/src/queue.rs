use std::collections::BinaryHeap;

use rustc_data_structures::graph::dominators::Dominators;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::BasicBlock;

struct Item<'a> {
    bb: BasicBlock,
    dominators: &'a Dominators<BasicBlock>,
}

pub(crate) struct WorkQueue<'a> {
    heap: BinaryHeap<Item<'a>>,
    set: BitSet<BasicBlock>,
    dominators: &'a Dominators<BasicBlock>,
}

impl<'a> WorkQueue<'a> {
    pub(crate) fn empty(len: usize, dominators: &'a Dominators<BasicBlock>) -> Self {
        Self { heap: BinaryHeap::with_capacity(len), set: BitSet::new_empty(len), dominators }
    }

    pub(crate) fn insert(&mut self, bb: BasicBlock) -> bool {
        if self.set.insert(bb) {
            self.heap.push(Item { bb, dominators: self.dominators });
            true
        } else {
            false
        }
    }

    pub(crate) fn pop(&mut self) -> Option<BasicBlock> {
        if let Some(Item { bb, .. }) = self.heap.pop() {
            self.set.remove(bb);
            Some(bb)
        } else {
            None
        }
    }
}

impl PartialEq for Item<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.bb == other.bb
    }
}

impl PartialOrd for Item<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for Item<'_> {}

impl Ord for Item<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.dominators.cmp_in_dominator_order(other.bb, self.bb)
    }
}
