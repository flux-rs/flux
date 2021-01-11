pub mod context;
pub mod subst;
use std::fmt;

use crate::{ast::Place, names::Local};
pub use crate::{
    ast::{
        pred::{BinOp, UnOp, Var},
        BaseTy, BorrowKind,
    },
    names::{ContId, Field, Location},
};
pub use context::TyCtxt;
use hashconsing::HConsed;
use indexmap::IndexMap;

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
        matches!(self.kind(), TyKind::Refine(BaseTy::Int, ..))
    }

    pub fn is_bool(&self) -> bool {
        matches!(self.kind(), TyKind::Refine(BaseTy::Bool, ..))
    }

    pub fn size(&self) -> usize {
        match self.kind() {
            TyKind::Fn(..) => 1,
            TyKind::OwnRef(..) => 1,
            TyKind::Ref(..) => 1,
            TyKind::Tuple(tup) => tup.types().map(|ty| ty.size()).sum(),
            TyKind::Uninit(n) => *n,
            TyKind::Refine(..) => 1,
        }
    }

    pub fn shape_eq(&self, ty: &Ty) -> bool {
        match (self.kind(), ty.kind()) {
            (TyKind::Fn(ty1), TyKind::Fn(ty2)) => ty1.shape_eq(&ty2),
            (TyKind::OwnRef(..), TyKind::OwnRef(..)) => true,
            (TyKind::Ref(bk1, ..), TyKind::Ref(bk2, ..)) => bk1 == bk2,
            (TyKind::Tuple(tuple1), TyKind::Tuple(tuple2)) => tuple1.shape_eq(tuple2),
            (TyKind::Uninit(n1), TyKind::Uninit(n2)) => n1 == n2,
            (TyKind::Refine(bty1, ..), TyKind::Refine(bty2, ..)) => bty1 == bty2,
            _ => false,
        }
    }

    pub fn walk(&self, f: &mut impl FnMut(&TyS)) {
        f(self);
        match self.kind() {
            TyKind::Tuple(tup) => {
                for ty in tup.types() {
                    ty.walk(f);
                }
            }
            TyKind::OwnRef(_)
            | TyKind::Ref(_, _, _)
            | TyKind::Fn(_)
            | TyKind::Uninit(_)
            | TyKind::Refine(_, _) => {}
        }
    }
}

impl fmt::Display for TyS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Fn(..) => todo!(),
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
            TyKind::Refine(bty, Refine::Infer(k)) => write!(f, "{{ {} | {} }}", bty, k),
            TyKind::Refine(bty, Refine::Pred(pred)) => write!(f, "{{ {} | {} }}", bty, pred),
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
    Refine(BaseTy, Refine),
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
        args.iter()
            .zip(&self.inputs)
            .map(|(x, l)| (*x, *l))
            .collect()
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

    pub fn map(&self, mut f: impl FnMut(usize, &Field, &Ty) -> (Field, Ty)) -> Tuple {
        self.0
            .iter()
            .enumerate()
            .map(|(i, (fld, ty))| f(i, fld, ty))
            .collect()
    }

    pub fn ty_at(&self, n: usize) -> &Ty {
        &self.0[n].1
    }

    pub fn types(&self) -> impl DoubleEndedIterator<Item = &Ty> + ExactSizeIterator {
        self.0.iter().map(|x| &x.1)
    }

    pub fn fields(&self) -> impl DoubleEndedIterator<Item = &Field> + ExactSizeIterator {
        self.0.iter().map(|x| &x.0)
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &(Field, Ty)> + ExactSizeIterator {
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

impl std::iter::FromIterator<(Field, Ty)> for Tuple {
    fn from_iter<T: IntoIterator<Item = (Field, Ty)>>(iter: T) -> Self {
        Tuple(iter.into_iter().collect())
    }
}

#[derive(Debug)]
pub struct ContTy {
    pub heap: Heap,
    pub locals: LocalsMap,
    pub inputs: Vec<Location>,
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
        self.locals
            .iter()
            .chain(args.iter().zip(&self.inputs))
            .map(|(x, l)| (*x, *l))
            .collect()
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
    Infer(Kvar),
}

impl From<Kvar> for Refine {
    fn from(v: Kvar) -> Self {
        Refine::Infer(v)
    }
}

impl From<Pred> for Refine {
    fn from(v: Pred) -> Self {
        Refine::Pred(v)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Kvar(pub KVid, pub Vec<Var>);

impl fmt::Display for Kvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars = (self.1)
            .iter()
            .map(|v| format!("{}", v))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "$k{}[{}]", (self.0).0, vars)
    }
}

#[derive(Clone, Debug)]
pub struct Heap(IndexMap<Location, Ty>);

impl Heap {
    pub fn new() -> Self {
        Heap(IndexMap::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
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

    pub fn keys(&self) -> impl Iterator<Item = &Location> {
        self.0.keys()
    }

    pub fn bindings(&self) -> Vec<(Location, Ty)> {
        self.0.iter().map(|(l, ty)| (*l, ty.clone())).collect()
    }

    pub fn map_ty(&self, mut f: impl FnMut(&Ty) -> Ty) -> Heap {
        self.iter().map(|(l, ty)| (*l, f(ty))).collect()
    }
}

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

impl IntoIterator for Heap {
    type Item = (Location, Ty);

    type IntoIter = indexmap::map::IntoIter<Location, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Heap {
    type Item = (&'a Location, &'a Ty);

    type IntoIter = indexmap::map::Iter<'a, Location, Ty>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl std::iter::FromIterator<(Location, Ty)> for Heap {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Location, Ty)>,
    {
        Heap(iter.into_iter().collect())
    }
}

#[derive(Debug, Clone)]
pub struct LocalsMap(IndexMap<Local, Location>);

impl LocalsMap {
    pub fn empty() -> Self {
        LocalsMap(IndexMap::new())
    }

    pub fn locals(&self) -> impl Iterator<Item = &Local> {
        self.iter().map(|(x, _)| x)
    }

    pub fn iter(&self) -> indexmap::map::Iter<Local, Location> {
        self.0.iter()
    }

    pub fn get(&self, x: &Local) -> Option<&Location> {
        self.0.get(x)
    }

    pub fn insert(&mut self, x: Local, l: Location) -> Option<Location> {
        self.0.insert(x, l)
    }
}

impl<'a> std::ops::Index<&'a Local> for LocalsMap {
    type Output = Location;

    fn index(&self, x: &'a Local) -> &Self::Output {
        self.get(x).expect("LocalsMap: local not found")
    }
}

impl std::iter::FromIterator<(Local, Location)> for LocalsMap {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Local, Location)>,
    {
        LocalsMap(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a LocalsMap {
    type Item = (&'a Local, &'a Location);

    type IntoIter = indexmap::map::Iter<'a, Local, Location>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl IntoIterator for LocalsMap {
    type Item = (Local, Location);

    type IntoIter = indexmap::map::IntoIter<Local, Location>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Extend<(Local, Location)> for LocalsMap {
    fn extend<T: IntoIterator<Item = (Local, Location)>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

/// A **K** **v**ariable **ID**
#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub struct KVid(pub usize);

/// A **Region** **v**ariable **ID**
#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub struct RegionVid(pub usize);

// Predicates

pub type Pred = HConsed<PredS>;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct PredS {
    kind: PredKind,
}

impl PredS {
    pub fn kind(&self) -> &PredKind {
        &self.kind
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PredKind {
    Constant(pred::Constant),
    Place(pred::Place),
    BinaryOp(BinOp, Pred, Pred),
    UnaryOp(UnOp, Pred),
}

impl std::fmt::Display for PredS {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            PredKind::Constant(c) => write!(f, "{}", c)?,
            PredKind::Place(place) => write!(f, "{}", place)?,
            PredKind::BinaryOp(op, lhs, rhs) => {
                write!(f, "({} {} {})", lhs, op, rhs)?;
            }
            PredKind::UnaryOp(op, operand) => {
                write!(f, "{}({})", op, operand)?;
            }
        }
        Ok(())
    }
}

pub mod pred {
    pub use crate::ast::pred::{Constant, Place};
}
