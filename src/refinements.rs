extern crate arena;
extern crate rustc_index;

use super::syntax::ast;
use rustc::mir;
pub use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{self, Ty};
use rustc_hir::BodyId;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub struct BodyRefts<'tcx> {
    pub body_id: BodyId,
    pub fun_type: Option<FunType<'tcx>>,
    pub local_decls: HashMap<mir::Local, Pred<'tcx>>,
}

#[derive(Debug)]
pub enum RType<'tcx> {
    Fun(FunType<'tcx>),
    Reft(Pred<'tcx>),
}

#[derive(Debug, Clone)]
pub struct FunType<'tcx> {
    pub inputs: Vec<Pred<'tcx>>,
    pub output: Pred<'tcx>,
}

impl<'tcx> FunType<'tcx> {
    pub fn open(&self, locals: &[mir::Local]) -> Vec<Pred<'tcx>> {
        assert_eq!(locals.len(), self.inputs.len() + 1);
        let mut refines = self
            .inputs
            .iter()
            .enumerate()
            .map(|(i, refine)| *refine.open(&locals[0..i + 1]))
            .collect::<Vec<_>>();
        refines.push(*self.output.open(locals));
        refines
    }
}

#[derive(Clone)]
pub enum Pred<'tcx> {
    Unary(ast::UnOpKind, Box<Pred<'tcx>>),
    Binary(Box<Pred<'tcx>>, ast::BinOpKind, Box<Pred<'tcx>>),
    Constant(Ty<'tcx>, ConstValue<'tcx>),
    Place(Place<'tcx>),
}

impl<'tcx> Pred<'tcx> {
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
    pub fn open(&self, locals: &[mir::Local]) -> Box<Self> {
        match self {
            Self::Unary(op, expr) => box Self::Unary(*op, expr.open(locals)),
            Self::Binary(lhs, op, rhs) => box Self::Binary(lhs.open(locals), *op, rhs.open(locals)),
            Self::Place(place) => {
                let place = match place.var {
                    Var::Free(_) => *place,
                    Var::Bound(idx) => Place {
                        var: Var::Free(locals[locals.len() - idx - 1]),
                        projection: place.projection,
                    },
                };
                box Self::Place(place)
            }
            Self::Constant(ty, val) => box Self::Constant(ty, *val),
        }
    }

    pub fn nu() -> Box<Self> {
        box Self::Place(Place::nu())
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Place<'tcx> {
    pub var: Var,
    pub projection: &'tcx ty::List<mir::PlaceElem<'tcx>>,
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

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum Var {
    Bound(usize),
    Free(mir::Local),
}

impl Var {
    pub fn nu() -> Self {
        Var::Bound(0)
    }
}

impl<'tcx> fmt::Debug for Pred<'tcx> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unary(op, expr) => write!(fmt, "{:?}{:?}", op, expr),
            Self::Binary(lhs, op, rhs) => write!(fmt, "{:?} {:?} {:?}", lhs, op, rhs),
            Self::Place(place) => write!(fmt, "{:?}", place),
            Self::Constant(ty, value) => write!(fmt, "{:?}{}", value, ty),
        }
    }
}

impl fmt::Debug for Place<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        for elem in self.projection.iter().rev() {
            match elem {
                mir::ProjectionElem::Downcast(_, _) | mir::ProjectionElem::Field(_, _) => {
                    write!(fmt, "(").unwrap();
                }
                mir::ProjectionElem::Deref => {
                    write!(fmt, "(*").unwrap();
                }
                mir::ProjectionElem::Index(_)
                | mir::ProjectionElem::ConstantIndex { .. }
                | mir::ProjectionElem::Subslice { .. } => {}
            }
        }

        write!(fmt, "{:?}", self.var)?;

        for elem in self.projection.iter() {
            match elem {
                mir::ProjectionElem::Downcast(Some(name), _index) => {
                    write!(fmt, " as {})", name)?;
                }
                mir::ProjectionElem::Downcast(None, index) => {
                    write!(fmt, " as variant#{:?})", index)?;
                }
                mir::ProjectionElem::Deref => {
                    write!(fmt, ")")?;
                }
                mir::ProjectionElem::Field(field, ty) => {
                    write!(fmt, ".{:?}: {:?})", field.index(), ty)?;
                }
                mir::ProjectionElem::Index(ref index) => {
                    write!(fmt, "[{:?}]", index)?;
                }
                mir::ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: false,
                } => {
                    write!(fmt, "[{:?} of {:?}]", offset, min_length)?;
                }
                mir::ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: true,
                } => {
                    write!(fmt, "[-{:?} of {:?}]", offset, min_length)?;
                }
                mir::ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: true,
                } if *to == 0 => {
                    write!(fmt, "[{:?}:]", from)?;
                }
                mir::ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: true,
                } if *from == 0 => {
                    write!(fmt, "[:-{:?}]", to)?;
                }
                mir::ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: true,
                } => {
                    write!(fmt, "[{:?}:-{:?}]", from, to)?;
                }
                mir::ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                } => {
                    write!(fmt, "[{:?}..{:?}]", from, to)?;
                }
            }
        }

        Ok(())
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bound(idx) => write!(fmt, "${}", idx),
            Self::Free(local) => write!(fmt, "{:?}", local),
        }
    }
}
