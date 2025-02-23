use std::collections::BinaryHeap;

use rustc_index::{bit_set::DenseBitSet, IndexVec};
use rustc_middle::mir::BasicBlock;

struct Item<'a> {
    bb: BasicBlock,
    dominator_order_rank: &'a IndexVec<BasicBlock, u32>,
}

pub(crate) struct WorkQueue<'a> {
    heap: BinaryHeap<Item<'a>>,
    set: DenseBitSet<BasicBlock>,
    dominator_order_rank: &'a IndexVec<BasicBlock, u32>,
}

impl<'a> WorkQueue<'a> {
    pub(crate) fn empty(len: usize, dominator_order_rank: &'a IndexVec<BasicBlock, u32>) -> Self {
        Self {
            heap: BinaryHeap::with_capacity(len),
            set: DenseBitSet::new_empty(len),
            dominator_order_rank,
        }
    }

    pub(crate) fn insert(&mut self, bb: BasicBlock) -> bool {
        if self.set.insert(bb) {
            self.heap
                .push(Item { bb, dominator_order_rank: self.dominator_order_rank });
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
        self.dominator_order_rank[other.bb].cmp(&self.dominator_order_rank[self.bb])
    }
}
