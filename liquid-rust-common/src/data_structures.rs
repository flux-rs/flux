use std::collections::{HashSet, VecDeque};

use crate::index::Idx;

pub struct WorkQueue<T: Idx> {
    deque: VecDeque<T>,
    set: HashSet<T>,
}

impl<T: Idx> WorkQueue<T> {
    #[inline]
    pub fn with_capacity(len: usize) -> Self {
        WorkQueue {
            deque: VecDeque::with_capacity(len),
            set: HashSet::with_capacity(len),
        }
    }

    #[inline]
    pub fn insert(&mut self, element: T) -> bool {
        if self.set.insert(element) {
            self.deque.push_back(element);
            true
        } else {
            false
        }
    }

    /// Attempt to pop an element from the work queue.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.deque.pop_front().map(|element| {
            self.set.remove(&element);
            element
        })
    }

    /// Returns `true` if nothing is enqueued.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.deque.is_empty()
    }
}
