use std::collections::hash_map::Entry;

use liquid_rust_common::index::{Idx, IndexVec};
use liquid_rust_core::ir::Field;
use rustc_hash::FxHashMap;

use crate::{
    subst::Subst,
    ty::{Loc, Path},
};

#[derive(Clone)]
pub struct PathMap<T> {
    map: FxHashMap<Loc, Node<T>>,
}

#[derive(Clone, Copy)]
pub struct PathRef<'a> {
    pub loc: Loc,
    pub projection: &'a [Field],
}

enum PathsIter<'a, T> {
    Internal {
        stack: Vec<std::iter::Enumerate<std::slice::Iter<'a, Node<T>>>>,
        loc: Loc,
        projection: Vec<Field>,
    },
    Leaf(Option<Loc>),
}

impl<'a, T> PathsIter<'a, T> {
    fn new(loc: Loc, root: &'a Node<T>) -> Self {
        match root {
            Node::Leaf(_) => PathsIter::Leaf(Some(loc)),
            Node::Internal(fields) => {
                PathsIter::Internal {
                    loc,
                    projection: vec![],
                    stack: vec![fields.iter().enumerate()],
                }
            }
        }
    }
}

impl<'a, T> Iterator for PathsIter<'a, T> {
    type Item = Path;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            PathsIter::Internal { stack, loc, projection } => {
                while let Some(top) = stack.last_mut() {
                    if let Some((i, node)) = top.next() {
                        if let Node::Internal(fields) = node {
                            projection.push(Field::new(i));
                            stack.push(fields.iter().enumerate());
                        } else {
                            projection.push(Field::new(i));
                            let path = Path::new(*loc, &projection);
                            projection.pop();
                            return Some(path);
                        }
                    } else {
                        projection.pop();
                        stack.pop();
                    }
                }
                None
            }
            PathsIter::Leaf(loc) => loc.take().map(|loc| Path::new(loc, &[])),
        }
    }
}

#[derive(Clone)]
enum Node<T> {
    Leaf(T),
    Internal(IndexVec<Field, Node<T>>),
}

impl<T> PathMap<T> {
    pub fn new() -> Self {
        Self { map: FxHashMap::default() }
    }

    pub fn locs(&self) -> impl Iterator<Item = Loc> + '_ {
        self.map.keys().copied()
    }

    pub fn paths(&self) -> impl Iterator<Item = Path> + '_ {
        self.map
            .iter()
            .flat_map(|(loc, root)| PathsIter::new(*loc, root))
    }

    pub fn iter_mut(&mut self, mut f: impl FnMut(PathRef, &mut T)) {
        fn go<T>(
            node: &mut Node<T>,
            loc: Loc,
            projection: &mut Vec<Field>,
            f: &mut impl FnMut(PathRef, &mut T),
        ) {
            match node {
                Node::Leaf(value) => {
                    f(PathRef::new(loc, projection), value);
                }
                Node::Internal(fields) => {
                    for (field, child) in fields.iter_enumerated_mut() {
                        projection.push(field);
                        go(child, loc, projection, f);
                        projection.pop();
                    }
                }
            }
        }

        for (loc, node) in &mut self.map {
            go(node, *loc, &mut vec![], &mut f);
        }
    }

    pub fn iter<'a>(&'a self, mut f: impl FnMut(PathRef, &'a T)) {
        fn go<'a, T>(
            node: &'a Node<T>,
            loc: Loc,
            projection: &mut Vec<Field>,
            f: &mut impl FnMut(PathRef, &'a T),
        ) {
            match node {
                Node::Leaf(value) => {
                    f(PathRef::new(loc, projection), value);
                }
                Node::Internal(fields) => {
                    for (field, child) in fields.iter_enumerated() {
                        projection.push(field);
                        go(child, loc, projection, f);
                        projection.pop();
                    }
                }
            }
        }

        for (loc, node) in &self.map {
            go(node, *loc, &mut vec![], &mut f);
        }
    }

    pub fn merge_with(&mut self, other: PathMap<T>, f: impl Fn(&mut T, T) + Copy) {
        for (loc, node) in other.map {
            match self.map.entry(loc) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().merge_with(node, f);
                }
                Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }
    }

    pub fn get<'a>(&self, path: impl Into<PathRef<'a>>) -> Option<&T> {
        let path = path.into();
        let mut node = self.map.get(&path.loc)?;
        for field in path.projection {
            match node {
                Node::Leaf(_) => return None,
                Node::Internal(fields) => node = &fields[*field],
            }
        }
        match node {
            Node::Leaf(value) => Some(value),
            Node::Internal(_) => None,
        }
    }

    pub fn get_mut<'a>(&mut self, path: impl Into<PathRef<'a>>) -> Option<&mut T> {
        let path = path.into();
        let mut node = self.map.get_mut(&path.loc)?;
        for field in path.projection {
            match node {
                Node::Leaf(_) => return None,
                Node::Internal(fields) => node = &mut fields[*field],
            }
        }
        match node {
            Node::Leaf(value) => Some(value),
            Node::Internal(_) => None,
        }
    }

    pub fn contains_path<'a>(&self, path: impl Into<PathRef<'a>>) -> bool {
        self.get(path.into()).is_some()
    }

    pub fn contains_loc(&self, loc: Loc) -> bool {
        self.map.contains_key(&loc)
    }

    pub fn insert(&mut self, loc: Loc, value: T) {
        self.map.insert(loc, Node::Leaf(value));
    }

    pub fn remove(&mut self, loc: Loc) {
        self.map.remove(&loc);
    }

    #[track_caller]
    pub fn update<'a>(&mut self, path: impl Into<PathRef<'a>>, value: T) {
        let path = path.into();
        if let Some(slot) = self.get_mut(path) {
            *slot = value;
        } else {
            panic!("no entry found for path: `{:?}", path)
        }
    }
}

impl<T> Node<T> {
    fn merge_with(&mut self, other: Node<T>, f: impl Fn(&mut T, T) + Copy) {
        match (self, other) {
            (Node::Leaf(val1), Node::Leaf(val2)) => {
                f(val1, val2);
            }
            (Node::Internal(fields1), Node::Internal(fields2)) => {
                assert!(fields1.len() == fields2.len());
                for (child1, child2) in fields1.iter_mut().zip(fields2.into_iter()) {
                    child1.merge_with(child2, f);
                }
            }
            _ => panic!("merge of incompatible nodes"),
        }
    }
}

// HACK(nilehmann) we have to create a Subst trait
impl PathMap<crate::ty::Ty> {
    pub fn subst(self, subst: &Subst) -> Self {
        let map = self
            .map
            .into_iter()
            .map(|(loc, mut node)| {
                node.subst_mut(subst);
                (subst.subst_loc(loc), node)
            })
            .collect();
        PathMap { map }
    }
}

impl PathMap<Vec<crate::ty::Ty>> {
    pub fn subst(self, subst: &Subst) -> Self {
        let map = self
            .map
            .into_iter()
            .map(|(loc, mut node)| {
                node.subst_mut(subst);
                (subst.subst_loc(loc), node)
            })
            .collect();
        PathMap { map }
    }
}

impl Node<crate::ty::Ty> {
    pub fn subst_mut(&mut self, subst: &Subst) {
        match self {
            Node::Leaf(ty) => *ty = subst.subst_ty(ty),
            Node::Internal(fields) => {
                for field in fields.iter_mut() {
                    field.subst_mut(subst);
                }
            }
        }
    }
}

impl Node<Vec<crate::ty::Ty>> {
    pub fn subst_mut(&mut self, subst: &Subst) {
        match self {
            Node::Leaf(tys) => {
                for ty in tys {
                    *ty = subst.subst_ty(ty)
                }
            }
            Node::Internal(fields) => {
                for field in fields.iter_mut() {
                    field.subst_mut(subst);
                }
            }
        }
    }
}

impl<T> Default for PathMap<T> {
    fn default() -> Self {
        Self { map: Default::default() }
    }
}

impl<'a> PathRef<'a> {
    pub fn new(loc: Loc, projection: &'a [Field]) -> Self {
        Self { loc, projection }
    }

    pub fn to_path(&self) -> Path {
        Path::new(self.loc, self.projection)
    }
}

impl From<Loc> for PathRef<'_> {
    fn from(loc: Loc) -> Self {
        PathRef::new(loc, &[])
    }
}

impl<'a> From<&'a Path> for PathRef<'a> {
    fn from(path: &'a Path) -> Self {
        path.as_ref()
    }
}

mod pretty {
    use super::*;
    use crate::pretty::*;
    use std::fmt;

    impl Pretty for PathRef<'_> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", self.loc)?;
            for field in self.projection {
                w!(".{:?}", ^field)?;
            }
            Ok(())
        }
    }

    impl_debug_with_default_cx!(PathRef<'_>);
}
