extern crate arena;
extern crate rustc_index;

use super::syntax::ast;
use rustc::mir;
pub use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{self, Ty};
use rustc_hir::BodyId;
use std::collections::HashMap;
// use std::fmt;

#[derive(Debug)]
pub struct BodyRefts<'a, 'tcx> {
    pub body_id: BodyId,
    pub fun_type: Option<FunType<'a, 'tcx>>,
    pub local_decls: HashMap<mir::Local, &'a Pred<'a, 'tcx>>,
}

#[derive(Debug)]
pub enum ReftType<'a, 'tcx> {
    Fun(&'a FunType<'a, 'tcx>),
    Reft(&'a Pred<'a, 'tcx>),
}

#[derive(Debug, Copy, Clone)]
pub struct FunType<'a, 'tcx> {
    pub inputs: &'a [Pred<'a, 'tcx>],
    pub output: &'a Pred<'a, 'tcx>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Pred<'a, 'tcx> {
    Unary(ast::UnOpKind, &'a Pred<'a, 'tcx>),
    Binary(&'a Pred<'a, 'tcx>, ast::BinOpKind, &'a Pred<'a, 'tcx>),
    Constant(Ty<'tcx>, ConstValue<'tcx>),
    Place(Place<'tcx>),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Place<'tcx> {
    pub var: Var,
    pub projection: &'tcx ty::List<mir::PlaceElem<'tcx>>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum Var {
    Bound(usize),
    Free(mir::Local),
}

impl<'a, 'tcx> Pred<'a, 'tcx> {
    pub fn iter_places(&self, mut f: impl FnMut(Place<'tcx>) -> ()) {
        self._iter_places(&mut f)
    }

    pub fn _iter_places(&self, f: &mut impl FnMut(Place<'tcx>) -> ()) {
        match self {
            Self::Unary(_, expr) => expr._iter_places(f),
            Self::Binary(lhs, _, rhs) => {
                lhs._iter_places(f);
                rhs._iter_places(f);
            }
            Self::Place(place) => {
                f(*place);
            }
            Self::Constant(_, _) => {}
        }
    }

    pub fn nu() -> Self {
        Self::Place(Place::nu())
    }
}

impl<'tcx> Place<'tcx> {
    pub fn from_var(var: Var) -> Self {
        Place {
            var,
            projection: ty::List::empty(),
        }
    }

    pub fn nu() -> Self {
        Place::from_var(Var::nu())
    }
}

impl Var {
    pub fn nu() -> Self {
        Var::Bound(0)
    }
}

// impl fmt::Debug for Pred {
//     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             Self::Unary(op, expr) => write!(fmt, "{:?}{:?}", op, expr),
//             Self::Binary(lhs, op, rhs) => write!(fmt, "{:?} {:?} {:?}", lhs, op, rhs),
//             Self::Place(place) => write!(fmt, "{:?}", place),
//             Self::Constant(ty, value) => write!(fmt, "{:?}{}", value, ty),
//         }
//     }
// }

// impl fmt::Debug for Place<'_> {
//     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
//         for elem in self.projection.iter().rev() {
//             match elem {
//                 mir::ProjectionElem::Downcast(_, _) | mir::ProjectionElem::Field(_, _) => {
//                     write!(fmt, "(").unwrap();
//                 }
//                 mir::ProjectionElem::Deref => {
//                     write!(fmt, "(*").unwrap();
//                 }
//                 mir::ProjectionElem::Index(_)
//                 | mir::ProjectionElem::ConstantIndex { .. }
//                 | mir::ProjectionElem::Subslice { .. } => {}
//             }
//         }

//         write!(fmt, "{:?}", self.var)?;

//         for elem in self.projection.iter() {
//             match elem {
//                 mir::ProjectionElem::Downcast(Some(name), _index) => {
//                     write!(fmt, " as {})", name)?;
//                 }
//                 mir::ProjectionElem::Downcast(None, index) => {
//                     write!(fmt, " as variant#{:?})", index)?;
//                 }
//                 mir::ProjectionElem::Deref => {
//                     write!(fmt, ")")?;
//                 }
//                 mir::ProjectionElem::Field(field, ty) => {
//                     write!(fmt, ".{:?}: {:?})", field.index(), ty)?;
//                 }
//                 mir::ProjectionElem::Index(ref index) => {
//                     write!(fmt, "[{:?}]", index)?;
//                 }
//                 mir::ProjectionElem::ConstantIndex {
//                     offset,
//                     min_length,
//                     from_end: false,
//                 } => {
//                     write!(fmt, "[{:?} of {:?}]", offset, min_length)?;
//                 }
//                 mir::ProjectionElem::ConstantIndex {
//                     offset,
//                     min_length,
//                     from_end: true,
//                 } => {
//                     write!(fmt, "[-{:?} of {:?}]", offset, min_length)?;
//                 }
//                 mir::ProjectionElem::Subslice {
//                     from,
//                     to,
//                     from_end: true,
//                 } if *to == 0 => {
//                     write!(fmt, "[{:?}:]", from)?;
//                 }
//                 mir::ProjectionElem::Subslice {
//                     from,
//                     to,
//                     from_end: true,
//                 } if *from == 0 => {
//                     write!(fmt, "[:-{:?}]", to)?;
//                 }
//                 mir::ProjectionElem::Subslice {
//                     from,
//                     to,
//                     from_end: true,
//                 } => {
//                     write!(fmt, "[{:?}:-{:?}]", from, to)?;
//                 }
//                 mir::ProjectionElem::Subslice {
//                     from,
//                     to,
//                     from_end: false,
//                 } => {
//                     write!(fmt, "[{:?}..{:?}]", from, to)?;
//                 }
//             }
//         }

//         Ok(())
//     }
// }

// impl fmt::Debug for Var {
//     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             Self::Bound(idx) => write!(fmt, "${}", idx),
//             Self::Free(local) => write!(fmt, "{:?}", local),
//         }
//     }
// }
