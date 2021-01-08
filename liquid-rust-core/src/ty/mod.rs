pub mod context;
pub mod pred;

use std::fmt;

pub use crate::ast::{BaseType, BorrowKind, LocalsMap};
pub use crate::names::{ContId, Field, Location};
use crate::{ast::Place, names::Local};
pub use context::TyCtxt;
use hashconsing::HConsed;
use indexmap::IndexMap;
pub use pred::{Pred, PredS};

pub type Ty = HConsed<TyS>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyS {
    kind: TyKind,
}

impl TyS {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }

    pub fn is_int(&self) -> bool {
        matches!(
            self.kind(),
            TyKind::Refine {
                bty: BaseType::Int,
                ..
            }
        )
    }

    pub fn is_bool(&self) -> bool {
        matches!(
            self.kind(),
            TyKind::Refine {
                bty: BaseType::Bool,
                ..
            }
        )
    }

    pub fn size(&self) -> usize {
        match self.kind() {
            TyKind::Fn(_) => 1,
            TyKind::OwnRef(_) => 1,
            TyKind::Ref(_, _, _) => 1,
            TyKind::Tuple(tup) => tup.types().map(|ty| ty.size()).sum(),
            TyKind::Uninit(n) => *n,
            TyKind::Refine { .. } => 1,
        }
    }

    pub fn shape_eq(&self, ty: &Ty) -> bool {
        match (self.kind(), ty.kind()) {
            (TyKind::Fn(ty1), TyKind::Fn(ty2)) => ty1.shape_eq(&ty2),
            (TyKind::OwnRef(_), TyKind::OwnRef(_)) => true,
            (TyKind::Ref(bk1, _, _), TyKind::Ref(bk2, _, _)) => bk1 == bk2,
            (TyKind::Tuple(tuple1), TyKind::Tuple(tuple2)) => tuple1.shape_eq(tuple2),
            (TyKind::Uninit(n1), TyKind::Uninit(n2)) => n1 == n2,
            (TyKind::Refine { bty: bty1, .. }, TyKind::Refine { bty: bty2, .. }) => bty1 == bty2,
            _ => false,
        }
    }
}

impl fmt::Display for TyS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Fn(_) => todo!(),
            TyKind::OwnRef(l) => write!(f, "Own(l${})", l.0),
            TyKind::Ref(BorrowKind::Shared, r, l) => write!(f, "&({}, $l{})", r, l.0),
            TyKind::Ref(BorrowKind::Mut, r, l) => write!(f, "&mut ({}, $l{})", r, l.0),
            TyKind::Tuple(tup) => {
                let tup = tup
                    .iter()
                    .map(|(f, ty)| format!("$f{}: {}", f.0, ty))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", tup)
            }
            TyKind::Uninit(size) => write!(f, "Uninit({})", size),
            TyKind::Refine {
                bty,
                refine: Refine::Infer(k),
            } => write!(f, "{{ {} | $k{} }}", bty, k.0),
            TyKind::Refine {
                bty,
                refine: Refine::Pred(pred),
            } => write!(f, "{{ {} | {} }}", bty, pred),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TyKind {
    Fn(FnTy),
    OwnRef(Location),
    Ref(BorrowKind, Region, Location),
    Tuple(Tuple),
    Uninit(usize),
    Refine { bty: BaseType, refine: Refine },
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FnTy {
    pub in_heap: Heap,
    pub inputs: Vec<Location>,
    pub out_heap: Heap,
    pub output: Location,
}

impl FnTy {
    pub fn shape_eq(&self, _ty: &FnTy) -> bool {
        todo!()
    }

    pub fn locals(&self, args: &[Local]) -> LocalsMap {
        assert!(self.inputs.len() == args.len());
        let mut vec = Vec::new();
        for (&x, &l) in args.iter().zip(&self.inputs) {
            vec.push((x, l));
        }
        LocalsMap::from(vec)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Tuple(Vec<(Field, Ty)>);

impl Tuple {
    pub fn shape_eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }

        self.iter().zip(other).all(|(x1, x2)| x1.1.shape_eq(&x2.1))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn map_ty_at(&self, n: usize, f: impl FnOnce(&Ty) -> Ty) -> Tuple {
        let mut v = self.0.clone();
        v[n].1 = f(&v[n].1);
        Tuple(v)
    }

    pub fn ty_at(&self, n: usize) -> &Ty {
        &self.0[n].1
    }

    pub fn types(&self) -> impl Iterator<Item = &Ty> {
        self.0.iter().map(|x| &x.1)
    }

    pub fn iter(&self) -> impl Iterator<Item = &(Field, Ty)> {
        self.0.iter()
    }
}

#[macro_export]
macro_rules! tup {
    ($($f:expr => $ty:expr),*) => {{
        let mut _vec = ::std::vec::Vec::new();
        $(
            _vec.push(($f, $ty));
        )*
        $crate::ty::Tuple::from(vec![])
    }};
}

impl<I> From<I> for Tuple
where
    I: IntoIterator<Item = (Field, Ty)>,
{
    fn from(iter: I) -> Self {
        Tuple(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a Tuple {
    type Item = &'a (Field, Ty);

    type IntoIter = std::slice::Iter<'a, (Field, Ty)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

#[derive(Debug)]
pub struct ContTy {
    pub heap: Heap,
    locals: LocalsMap,
    inputs: Vec<Location>,
}

impl ContTy {
    pub fn new(heap: Heap, locals: LocalsMap, inputs: Vec<Location>) -> Self {
        ContTy {
            heap,
            locals,
            inputs,
        }
    }

    pub fn locals(&self, args: &[Local]) -> LocalsMap {
        assert!(self.inputs.len() == args.len());
        let mut vec = Vec::new();
        for &(x, l) in &self.locals {
            vec.push((x, l));
        }
        for (&x, &l) in args.iter().zip(&self.inputs) {
            vec.push((x, l));
        }
        LocalsMap::from(vec)
    }
}

#[derive(Eq, PartialEq, Clone, Debug, Hash)]
pub enum Region {
    Concrete(Vec<Place>),
    Infer(RegionVid),
}

impl fmt::Display for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Region::Concrete(places) => {
                let places = places
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{{ {} }}", places)
            }
            Region::Infer(rvid) => write!(f, "$r{}", rvid.0),
        }
    }
}

impl From<Place> for Region {
    fn from(place: Place) -> Self {
        Region::Concrete(vec![place])
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Refine {
    Pred(Pred),
    Infer(KVid),
}

#[derive(Clone, Debug)]
pub struct Heap(IndexMap<Location, Ty>);

impl std::fmt::Display for Heap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, (l, ty)) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "$l{}: {}", l.0, ty)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

impl Heap {
    pub fn new() -> Self {
        Heap(IndexMap::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn split_off(&mut self, at: usize) -> Heap {
        Heap(self.0.split_off(at))
    }

    pub fn get(&self, l: &Location) -> Option<&Ty> {
        self.0.get(l)
    }

    pub fn insert(&mut self, l: Location, ty: Ty) -> Option<Ty> {
        self.0.insert(l, ty)
    }

    pub fn iter(&self) -> indexmap::map::Iter<Location, Ty> {
        self.0.iter()
    }
}

impl std::ops::Index<&Location> for Heap {
    type Output = Ty;

    fn index(&self, l: &Location) -> &Self::Output {
        self.get(l).expect("Heap: location not found")
    }
}

impl PartialEq for Heap {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }

        self.0.iter().zip(other).all(|(x1, x2)| x1 == x2)
    }
}

impl Eq for Heap {}

impl std::hash::Hash for Heap {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for (l, ty) in self {
            l.hash(state);
            ty.hash(state);
        }
    }
}

impl<'a> IntoIterator for &'a Heap {
    type Item = (&'a Location, &'a Ty);

    type IntoIter = indexmap::map::Iter<'a, Location, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<I> From<I> for Heap
where
    I: IntoIterator<Item = (Location, Ty)>,
{
    fn from(it: I) -> Self {
        Heap(it.into_iter().collect())
    }
}

/// A **K** **v**ariable **ID**
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct KVid(pub usize);

/// A **Region** **v**ariable **ID**
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct RegionVid(pub usize);
