pub mod context;
pub mod subst;
use std::{collections::HashMap, fmt};

use crate::{
    ast::{self, Place},
    names::Local,
};
pub use crate::{
    ast::{
        pred::{BinOp, UnOp, Var},
        BaseTy, BorrowKind, UniversalRegion,
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

    pub fn is_copy(&self) -> bool {
        match self.kind() {
            TyKind::Tuple(tup) => tup.types().all(|ty| ty.is_copy()),
            TyKind::Refine { .. } | TyKind::Ref(BorrowKind::Shared, ..) => true,
            _ => false,
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(self.kind(), TyKind::Refine(BaseTy::Int, ..))
    }

    pub fn is_bool(&self) -> bool {
        matches!(self.kind(), TyKind::Refine(BaseTy::Bool, ..))
    }

    pub fn size(&self) -> usize {
        match self.kind() {
            TyKind::Tuple(tup) => tup.types().map(|ty| ty.size()).sum(),
            TyKind::Uninit(n) => *n,
            TyKind::Fn(..) | TyKind::OwnRef(..) | TyKind::Ref(..) | TyKind::Refine(..) => 1,
        }
    }

    pub fn walk<T>(&self, mut f: impl FnMut(&TyS, &[ast::Proj]) -> Walk<T>) -> Walk<T> {
        self.walk_internal(&mut f, &mut vec![])
    }

    fn walk_internal<T>(
        &self,
        f: &mut impl FnMut(&TyS, &[ast::Proj]) -> Walk<T>,
        projs: &mut Vec<ast::Proj>,
    ) -> Walk<T> {
        f(self, projs)?;
        if let TyKind::Tuple(tup) = self.kind() {
            for (i, ty) in tup.types().enumerate() {
                projs.push(ast::Proj::Field(i));
                ty.walk_internal(f, projs)?;
                projs.pop();
            }
        }
        Walk::Continue
    }
}

pub enum Walk<T = ()> {
    Stop(T),
    Continue,
}

impl<T> std::ops::Try for Walk<T> {
    type Ok = ();
    type Error = T;

    fn into_result(self) -> Result<Self::Ok, Self::Error> {
        match self {
            Walk::Stop(v) => Err(v),
            Walk::Continue => Ok(()),
        }
    }

    fn from_error(v: Self::Error) -> Self {
        Walk::Stop(v)
    }

    fn from_ok((): Self::Ok) -> Self {
        Walk::Continue
    }
}

impl fmt::Display for TyS {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Fn(..) => todo!(),
            TyKind::OwnRef(l) => write!(f, "own(l{})", l.inner()),
            TyKind::Ref(BorrowKind::Shared, r, l) => write!(f, "&{} l{}", r, l.inner()),
            TyKind::Ref(BorrowKind::Mut, r, l) => write!(f, "&{} mut l{}", r, l.inner()),
            TyKind::Tuple(tup) => {
                let tup = tup
                    .iter()
                    .map(|(f, ty)| format!("f{}: {}", f.inner(), ty))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", tup)
            }
            TyKind::Uninit(size) => write!(f, "uninit({})", size),
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
    pub regions: Vec<UniversalRegion>,
    pub in_heap: Heap,
    pub inputs: LocalsMap,
    pub out_heap: Heap,
    pub outputs: LocalsMap,
    pub output: Location,
}

impl FnTy {
    pub fn inputs(&self, args: &[Local]) -> LocalsMap {
        assert!(self.inputs.len() == args.len());
        args.iter()
            .zip(&self.inputs)
            .map(|(x, (_, l))| (*x, *l))
            .collect()
    }

    pub fn outputs(&self, args: &[Local]) -> LocalsMap {
        assert!(self.inputs.len() == args.len());
        let map: HashMap<Local, Local> = self
            .inputs
            .iter()
            .zip(args)
            .map(|((x, _), y)| (*x, *y))
            .collect();

        self.outputs.iter().map(|(x, l)| (map[x], *l)).collect()
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Tuple(Vec<(Field, Ty)>);

impl Tuple {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
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
}

#[macro_export]
macro_rules! tup {
    ($($f:expr => $ty:expr),*) => {{
        let mut _vec = ::std::vec::Vec::new();
        $(
            _vec.push(($f, $ty));
        )*
        _vec.into_iter().collect::<$crate::ty::Tuple>()
    }};
}

wrap_iterable! {
    Tuple: Vec<(Field, Ty)>
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
    Universal(UniversalRegion),
}

impl From<Vec<Place>> for Region {
    fn from(v: Vec<Place>) -> Self {
        Region::Concrete(v)
    }
}

impl From<RegionVid> for Region {
    fn from(v: RegionVid) -> Self {
        Region::Infer(v)
    }
}

impl Region {
    pub fn places(&self) -> &[Place] {
        match self {
            Region::Concrete(places) => places,
            Region::Infer(_) | Region::Universal(_) => &[],
        }
    }
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
            Region::Infer(rvid) => write!(f, "r{}", rvid.as_usize()),
            Region::Universal(param) => write!(f, "'{}", param.as_usize()),
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

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Kvar(pub KVid, pub Vec<Var>);

impl fmt::Display for Kvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let vars = (self.1)
            .iter()
            .map(|v| format!("{}", v))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "$k{}[{}]", (self.0).as_usize(), vars)
    }
}

impl fmt::Debug for Kvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[derive(Clone, Debug, Default)]
pub struct Heap(IndexMap<Location, Ty>);

wrap_iterable! {
    Heap: IndexMap<Location, Ty>
}

wrap_dict_like! {
    Heap: IndexMap<Location, Ty> {
        type Index = Location;
        type Output = Ty;
    }
}

impl Heap {
    pub fn new() -> Self {
        Heap(IndexMap::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
    }

    pub fn vars_in_scope(&self) -> impl Iterator<Item = Var> + '_ {
        self.iter().map(|(l, _)| Var::Location(*l))
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
            write!(f, "l{}: {}", l.inner(), ty)?;
        }
        write!(f, "]")?;
        Ok(())
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

#[derive(Debug, Clone)]
pub struct LocalsMap(IndexMap<Local, Location>);

impl LocalsMap {
    pub fn empty() -> Self {
        LocalsMap(IndexMap::new())
    }

    pub fn locals(&self) -> impl Iterator<Item = &Local> {
        self.iter().map(|(x, _)| x)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl PartialEq for LocalsMap {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }

        self.0.iter().zip(other).all(|(x1, x2)| x1 == x2)
    }
}

impl Eq for LocalsMap {}

impl std::hash::Hash for LocalsMap {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for (x, l) in self {
            x.hash(state);
            l.hash(state);
        }
    }
}

impl fmt::Display for LocalsMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, (x, l)) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "_{} -> l{}", x.as_usize(), l.as_usize())?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

wrap_iterable! {
    LocalsMap: IndexMap<Local, Location>
}

wrap_dict_like! {
    LocalsMap: IndexMap<Local, Location> {
        type Index = Local;
        type Output = Location;
    }
}

impl Extend<(Local, Location)> for LocalsMap {
    fn extend<T: IntoIterator<Item = (Local, Location)>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

newtype_index! {
    /// A **K** **v**ariable **ID**
    struct KVid
}

newtype_index! {
    /// A **Region** **v**ariable **ID**
    struct RegionVid
}

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
