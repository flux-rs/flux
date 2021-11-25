use std::{cell::Cell, fmt, iter::FusedIterator};

use itertools::Itertools;
use rustc_hash::FxHashMap;

pub use crate::index::{Idx, IndexVec};

#[derive(Clone, Default)]
pub struct DisjointSetsMap<I: Idx, T> {
    map: FxHashMap<I, T>,
    parent: IndexVec<I, Cell<I>>,
    size: IndexVec<I, usize>,
    next: IndexVec<I, I>,
}

pub struct Set<'a, I: Idx> {
    next: &'a IndexVec<I, I>,
    remaining: usize,
    current: I,
}

impl<I: Idx, T> DisjointSetsMap<I, T> {
    pub fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            parent: IndexVec::new(),
            size: IndexVec::new(),
            next: IndexVec::new(),
        }
    }

    pub fn from_iter<Iter>(iter: Iter) -> Self
    where
        Iter: IntoIterator<Item = T>,
        Iter::IntoIter: ExactSizeIterator,
    {
        let iter = iter.into_iter();
        let n = iter.len();
        Self {
            map: iter
                .enumerate()
                .map(|(idx, elem)| (I::new(idx), elem))
                .collect(),
            parent: IndexVec::from_fn_n(|idx| Cell::new(idx), n),
            size: IndexVec::from_elem_n(1, n),
            next: IndexVec::from_fn_n(|idx| idx, n),
        }
    }

    pub fn size(&self) -> usize {
        self.parent.len()
    }

    pub fn push(&mut self, elem: T) -> I {
        let idx = self.parent.next_index();
        self.map.insert(idx, elem);
        self.parent.push(Cell::new(idx));
        self.size.push(1);
        self.next.push(idx);
        idx
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

        let root = if self.size[root1] <= self.size[root2] {
            self.parent[root1].set(root2);
            self.size[root2] += self.size[root1];
            root2
        } else {
            self.parent[root2].set(root1);
            self.size[root1] += self.size[root2];
            root1
        };

        let elem1 = self.map.remove(&root1).unwrap();
        let elem2 = self.map.remove(&root2).unwrap();
        self.map.insert(root, merge(elem1, elem2));
    }

    pub fn multi_union(
        &mut self,
        indices: impl IntoIterator<Item = I>,
        merge: impl Fn(T, T) -> T + Copy,
    ) {
        let mut indices = indices.into_iter();
        match indices.next() {
            None => {}
            Some(first) => {
                for idx in indices {
                    self.union(first, idx, merge)
                }
            }
        }
    }

    pub fn set(&self, idx: I) -> Set<I> {
        let root = self.find(idx);
        Set::new(&self.next, root, self.size[root])
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

    pub fn map_values<R, F>(self, mut f: F) -> DisjointSetsMap<I, R>
    where
        F: FnMut(Set<I>, T) -> R,
    {
        let DisjointSetsMap {
            map,
            parent,
            size,
            next,
        } = self;
        let f = &mut f;
        let map = map
            .into_iter()
            .map(|(root, elem)| (root, f(Set::new(&next, root, size[root]), elem)))
            .collect();
        DisjointSetsMap {
            map,
            parent,
            size,
            next,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (Set<I>, &T)> {
        self.map
            .iter()
            .map(|(root, elem)| (Set::new(&self.next, *root, self.size[*root]), elem))
    }
}

impl<I: Idx, T: Clone> DisjointSetsMap<I, T> {
    pub fn merge_with(&mut self, other: &Self, merge: impl Fn(T, T) -> T + Copy) {
        for idx in self.parent.indices() {
            let root = other.find(idx);
            if root == idx {
                let elem1 = self[idx].clone();
                let elem2 = other[idx].clone();
                self[idx] = merge(elem1, elem2);
            } else {
                self.union(idx, root, merge);
            }
        }
    }
}

impl<'a, I: Idx> Set<'a, I> {
    fn new(next: &'a IndexVec<I, I>, root: I, size: usize) -> Self {
        Self {
            next,
            remaining: size,
            current: root,
        }
    }
}

impl<'a, I: Idx> Iterator for Set<'a, I> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }

        let current = self.current;
        self.current = self.next[current];
        self.remaining -= 1;

        Some(current)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<I: Idx> FusedIterator for Set<'_, I> {}

impl<'a, I: Idx> ExactSizeIterator for Set<'a, I> {
    fn len(&self) -> usize {
        self.remaining
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
    I: Idx,
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for (mut set, elem) in self.iter() {
            if set.len() == 1 {
                write!(f, "{:?}: ", set.next().unwrap())?;
            } else {
                write!(f, "{{{:?}}}: ", set.sorted().format(", "))?;
            }
            write!(f, "{:?}, ", elem)?;
        }
        write!(f, "}}")
    }
}
