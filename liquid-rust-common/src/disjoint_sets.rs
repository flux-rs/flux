use std::{cell::Cell, cmp::Ordering, fmt};

use itertools::Itertools;
use rustc_hash::FxHashMap;

pub use crate::index::{Idx, IndexVec};

#[derive(Clone)]
pub struct DisjointSetsMap<I: Idx, T> {
    map: FxHashMap<I, T>,
    parent: IndexVec<I, Cell<I>>,
    rank: IndexVec<I, usize>,
    next: IndexVec<I, I>,
}

pub struct SetIter<'a, I: Idx, T> {
    disjoint_sets: &'a DisjointSetsMap<I, T>,
    current: Option<I>,
    root: I,
}

impl<I: Idx, T> DisjointSetsMap<I, T> {
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

    pub fn same_set(&self, idx1: I, idx2: I) -> bool {
        self.find(idx1) == self.find(idx2)
    }

    pub fn union(&mut self, idx1: I, idx2: I, merge: impl FnOnce(T, T) -> T) {
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
                let elem = merge(elem1, elem2);
                self.map.insert(root, elem);
            }
        }
    }

    pub fn multi_union(
        &mut self,
        indices: impl IntoIterator<Item = I>,
        merge: impl Fn(T, T) -> T + Copy,
    ) {
        let mut indices = indices.into_iter();
        match indices.next() {
            None => return,
            Some(first) => {
                for idx in indices {
                    self.union(first, idx, merge)
                }
            }
        }
    }

    pub fn iter_set(&self, idx: I) -> SetIter<I, T> {
        let root = self.find(idx);
        SetIter {
            disjoint_sets: self,
            current: Some(root),
            root,
        }
    }

    pub fn iter_sets(&self) -> impl Iterator<Item = Vec<I>> {
        self.parent
            .indices()
            .into_group_map_by(|idx| self.find(*idx))
            .into_iter()
            .sorted()
            .map(|(_, set)| set)
    }

    pub fn remove(&mut self, idx: I) -> Option<T> {
        self.map.remove(&self.find(idx))
    }

    pub fn get(&self, idx: I) -> Option<&T> {
        self.map.get(&self.find(idx))
    }

    pub fn get_mut(&mut self, idx: I) -> Option<&mut T> {
        self.map.get_mut(&self.find(idx))
    }

    pub fn insert(&mut self, idx: I, elem: T) -> Option<T> {
        self.map.insert(self.find(idx), elem)
    }

    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.map.values()
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.map.values_mut()
    }

    fn find(&self, elem: I) -> I {
        let p = self.parent[elem].get();
        if p != elem {
            self.parent[elem].set(self.find(p));
        }
        self.parent[elem].get()
    }
}

impl<I: Idx, T: Clone> DisjointSetsMap<I, T> {
    pub fn merge_with(&mut self, other: &Self, merge: impl Fn(T, T) -> T + Copy) {
        for idx in self.parent.indices() {
            let root = other.find(idx);
            if root == idx {
                if let Some(elem1) = other.get(idx) {
                    match self.remove(idx) {
                        Some(elem2) => {
                            self.insert(idx, merge(elem1.clone(), elem2));
                        }
                        None => {
                            self.insert(idx, elem1.clone());
                        }
                    }
                }
            } else {
                self.union(idx, root, merge);
            }
        }
    }
}

impl<'a, I: Idx, T> Iterator for SetIter<'a, I, T> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;

        let next = self.disjoint_sets.next[current];

        self.current = if next == self.root { None } else { Some(next) };

        Some(current)
    }
}

impl<I: Idx, T> std::ops::Index<I> for DisjointSetsMap<I, T> {
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<I: Idx, T> std::ops::IndexMut<I> for DisjointSetsMap<I, T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

impl<I, T> fmt::Debug for DisjointSetsMap<I, T>
where
    T: fmt::Debug,
    I: Idx,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (root, set) in self
            .parent
            .indices()
            .into_group_map_by(|idx| self.find(*idx))
            .into_iter()
            .sorted()
        {
            if set.len() == 1 {
                write!(f, "{:?}: ", set[0])?;
            } else {
                write!(f, "{{{:?}}}: ", set.iter().sorted().format(", "),)?;
            }
            match self.map.get(&root) {
                Some(ty) => {
                    write!(f, "{:?}, ", ty)?;
                }
                None => {
                    write!(f, "unknown, ")?;
                }
            }
        }
        write!(f, "}}")
    }
}
