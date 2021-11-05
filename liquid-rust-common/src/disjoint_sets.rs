use std::{cell::Cell, cmp::Ordering};

use rustc_hash::FxHashMap;

pub use crate::index::{Idx, IndexVec};

pub struct DisjointSets<I: Idx, T> {
    map: FxHashMap<I, T>,
    parent: IndexVec<I, Cell<I>>,
    rank: IndexVec<I, usize>,
    next: IndexVec<I, I>,
}

pub struct Set<'a, I: Idx, T> {
    disjoint_sets: &'a DisjointSets<I, T>,
    current: Option<I>,
    root: I,
}

impl<I: Idx, T> DisjointSets<I, T> {
    pub fn new(n: usize) -> Self {
        let parent = IndexVec::from_fn_n(|idx| Cell::new(idx), n);
        let rank = IndexVec::from_elem_n(0, n);
        let next = IndexVec::from_fn_n(|idx| idx, n);
        Self {
            map: FxHashMap::default(),
            parent,
            rank,
            next,
        }
    }

    pub fn len(&self) -> usize {
        self.parent.len()
    }

    pub fn push(&mut self, idx: I) {
        self.parent.push(Cell::new(idx));
        self.rank.push(0);
        self.next.push(idx);
    }
    pub fn union(&mut self, idx1: I, idx2: I, merge: impl FnOnce(&mut Self, T, T) -> T) {
        let root1 = self.find(idx1);
        let root2 = self.find(idx2);

        if root1 == root2 {
            return;
        }

        self.next.swap(root1, root2);

        let root = match Ord::cmp(&self.rank[root1], &self.rank[root2]) {
            Ordering::Less => {
                self.parent[root1].set(root2);
                root2
            }
            Ordering::Equal => {
                *self.parent[root1].get_mut() = root2;
                self.rank[root2] += 1;
                root2
            }
            Ordering::Greater => {
                self.parent[root2].set(root1);
                root1
            }
        };
        match (self.map.remove(&root1), self.map.remove(&root2)) {
            (None, None) => {}
            (None, Some(elem)) | (Some(elem), None) => {
                self.map.insert(root, elem);
            }
            (Some(elem1), Some(elem2)) => {
                let elem = merge(self, elem1, elem2);
                self.map.insert(root, elem);
            }
        }
    }

    pub fn remove(&mut self, idx: I) -> Option<T> {
        self.map.remove(&self.find(idx))
    }

    pub fn get(&self, idx: I) -> Option<&T> {
        self.map.get(&self.find(idx))
    }

    pub fn insert(&mut self, idx: I, elem: T) -> Option<T> {
        self.map.insert(self.find(idx), elem)
    }

    fn find(&self, elem: I) -> I {
        let p = self.parent[elem].get();
        if p != elem {
            self.parent[elem].set(self.find(p));
        }
        self.parent[elem].get()
    }
}

impl<I: Idx, T: Clone> DisjointSets<I, T> {
    pub fn merge_with(&mut self, other: &Self, mut merge: impl FnMut(&mut Self, T, T) -> T) {
        self.merge_with_inner(other, &mut merge);
    }

    fn merge_with_inner(&mut self, other: &Self, merge: &mut impl FnMut(&mut Self, T, T) -> T) {
        for idx in self.parent.indices() {
            let root = other.find(idx);
            if root == idx {
                match (self.remove(idx), other.get(idx)) {
                    (None, None) => {}
                    (None, Some(elem)) => {
                        self.insert(idx, elem.clone());
                    }
                    (Some(elem), None) => {
                        self.map.insert(idx, elem);
                    }
                    (Some(elem1), Some(elem2)) => {
                        let elem = merge(self, elem1, elem2.clone());
                        self.insert(idx, elem);
                    }
                }
            } else {
                self.union(idx, root, &mut *merge);
            }
        }
    }
}

impl<'a, I: Idx, T> Iterator for Set<'a, I, T> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;

        let next = self.disjoint_sets.next[current];

        self.current = if next == self.root { None } else { Some(next) };

        Some(current)
    }
}
