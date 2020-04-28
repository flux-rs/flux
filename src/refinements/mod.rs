pub mod dataflow;
pub mod typeck;

extern crate arena;
extern crate rustc_index;

use super::syntax::ast;
use rustc_apfloat::{
    ieee::{Double, Single},
    Float,
};
use rustc_ast::ast::FloatTy;
use rustc_hir::BodyId;
use rustc_middle::mir;
use rustc_middle::mir::interpret::sign_extend;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_target::abi::Size;
use std::collections::HashMap;
use std::fmt;

#[derive(Copy, Clone)]
pub struct Binder<T>(T);

#[derive(Debug)]
pub struct BodyRefts<'a, 'tcx> {
    pub body_id: BodyId,
    pub fun_type: Option<Binder<&'a ReftType<'a, 'tcx>>>,
    pub local_decls: HashMap<mir::Local, Binder<&'a ReftType<'a, 'tcx>>>,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReftType<'a, 'tcx> {
    Fun {
        inputs: &'a [ReftType<'a, 'tcx>],
        output: &'a ReftType<'a, 'tcx>,
    },
    Reft(Ty<'tcx>, &'a Pred<'a, 'tcx>),
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum Pred<'a, 'tcx> {
    Unary(ast::UnOpKind, &'a Pred<'a, 'tcx>),
    Binary(&'a Pred<'a, 'tcx>, ast::BinOpKind, &'a Pred<'a, 'tcx>),
    Operand(Operand<'tcx>),
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum Operand<'tcx> {
    Constant(Ty<'tcx>, Scalar),
    Place(Place<'tcx>),
}

impl<'tcx> Operand<'tcx> {
    pub fn from_locals(locals: &[mir::Local]) -> Vec<Self> {
        locals.iter().map(|l| Self::from_local(*l)).collect()
    }

    pub fn from_local(local: mir::Local) -> Self {
        Operand::Place(Place {
            var: Var::Local(local),
            projection: ty::List::empty(),
        })
    }

    pub fn from_mir(operand: &mir::Operand<'tcx>) -> Self {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => Self::Place(Place {
                var: Var::Local(place.local),
                projection: place.projection,
            }),
            mir::Operand::Constant(box mir::Constant { literal, .. }) => {
                match Scalar::from_const(literal) {
                    Some(scalar) => Operand::Constant(literal.ty, scalar),
                    None => todo!("{:?}", operand),
                }
            }
        }
    }

    pub fn from_bits(tcx: TyCtxt<'tcx>, bits: u128, ty: Ty<'tcx>) -> Self {
        let param_ty = ty::ParamEnv::reveal_all().and(ty);
        let size = tcx
            .layout_of(param_ty)
            .unwrap_or_else(|e| panic!("could not compute layout for {:?}: {:?}", ty, e))
            .size;
        Self::from_scalar(ty, Scalar::from_uint(bits, size))
    }

    pub fn from_scalar(ty: Ty<'tcx>, scalar: Scalar) -> Self {
        Self::Constant(ty, scalar)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Scalar {
    pub data: u128,
    pub size: u8,
}

impl Scalar {
    pub fn from_bool(b: bool) -> Self {
        Scalar {
            data: b as u128,
            size: 1,
        }
    }

    pub fn from_uint(i: impl Into<u128>, size: Size) -> Self {
        let i = i.into();
        Scalar {
            data: i,
            size: size.bytes() as u8,
        }
    }

    pub fn from_f32(f: Single) -> Self {
        // We trust apfloat to give us properly truncated data.
        Scalar {
            data: f.to_bits(),
            size: 4,
        }
    }

    pub fn from_f64(f: Double) -> Self {
        // We trust apfloat to give us properly truncated data.
        Scalar {
            data: f.to_bits(),
            size: 8,
        }
    }

    pub fn from_const(lit: &ty::Const) -> Option<Self> {
        if_chain! {
            if let ty::ConstKind::Value(val) = lit.val;
            if let mir::interpret::ConstValue::Scalar(scalar) = val;
            if let mir::interpret::Scalar::Raw {data, size} = scalar;
            then {
                Some(Scalar { data, size })
            }
            else {
                None
            }
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Place<'tcx> {
    pub var: Var,
    pub projection: &'tcx ty::List<mir::PlaceElem<'tcx>>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum Var {
    Bound(usize),
    Local(mir::Local),
    Free(usize),
}

impl<T> Binder<T> {
    pub fn bind(val: T) -> Self {
        Binder(val)
    }

    pub fn skip_binder(&self) -> &T {
        &self.0
    }
}

impl<'a, 'tcx> Binder<&'a ReftType<'a, 'tcx>> {
    pub fn pred(&self) -> Option<Binder<&'a Pred<'a, 'tcx>>> {
        if let ReftType::Reft(_, pred) = self.skip_binder() {
            Some(Binder::bind(pred))
        } else {
            None
        }
    }
}

impl<'a, 'tcx> ReftType<'a, 'tcx> {
    pub fn pred(&self) -> Option<&'a Pred<'a, 'tcx>> {
        if let Self::Reft(_, pred) = self {
            Some(pred)
        } else {
            None
        }
    }
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
            Self::Operand(Operand::Place(place)) => f(*place),
            Self::Operand(Operand::Constant(..)) => {}
        }
    }

    pub fn nu() -> Self {
        Self::Operand(Operand::Place(Place::nu()))
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

    pub fn ty<D>(&self, local_decls: &D, tcx: TyCtxt<'tcx>) -> Ty<'tcx>
    where
        D: mir::HasLocalDecls<'tcx>,
    {
        match self.var {
            Var::Local(local) => {
                self.projection
                    .iter()
                    .fold(
                        mir::tcx::PlaceTy::from_ty(local_decls.local_decls()[local].ty),
                        |place_ty, elem| place_ty.projection_ty(tcx, elem),
                    )
                    .ty
            }
            // TODO: Fix this
            _ => tcx.mk_mach_int(ast::IntTy::I32),
        }
    }
}

impl Var {
    pub fn nu() -> Self {
        Var::Bound(0)
    }
}

impl<T: fmt::Debug> fmt::Debug for Binder<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.skip_binder(), fmt)
    }
}

impl fmt::Debug for ReftType<'_, '_> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Fun { inputs, output } => {
                write!(fmt, "(")?;
                for (i, pred) in inputs.iter().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{:?}", pred)?;
                }
                write!(fmt, ") -> {:?}", output)
            }
            Self::Reft(_, pred) => write!(fmt, "{{{:?}}}", pred),
        }
    }
}

impl fmt::Debug for Pred<'_, '_> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unary(op, expr) => write!(fmt, "{:?}({:?})", op, expr),
            Self::Binary(lhs, op, rhs) => write!(fmt, "{:?} {:?} {:?}", lhs, op, rhs),
            Self::Operand(operand) => write!(fmt, "{:?}", operand),
        }
    }
}

impl fmt::Debug for Operand<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Place(place) => write!(fmt, "{:?}", place),
            Self::Constant(ty, scalar) => {
                match &ty.kind {
                    ty::Bool => write!(fmt, "{}", if scalar.data == 0 { "false" } else { "true" }),
                    ty::Float(FloatTy::F32) => write!(fmt, "{}", Single::from_bits(scalar.data)),
                    ty::Float(FloatTy::F64) => write!(fmt, "{}", Double::from_bits(scalar.data)),
                    ty::Uint(_) => write!(fmt, "{}", scalar.data),
                    ty::Int(i) => {
                        // TODO: assuming 64 bits for isize. we can probably make this configurable
                        let bit_width = i.bit_width().unwrap_or(64) as u64;
                        let size = Size::from_bits(bit_width);
                        write!(fmt, "{}", sign_extend(scalar.data, size) as i128)
                    }
                    _ => write!(fmt, "`?:{:?}`", ty.kind),
                }
            }
        }
    }
}

impl fmt::Debug for Place<'_> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        for elem in self.projection.iter().rev() {
            match elem {
                mir::ProjectionElem::Downcast(_, _) => {
                    write!(fmt, "(").unwrap();
                }
                mir::ProjectionElem::Deref => {
                    write!(fmt, "(*").unwrap();
                }
                mir::ProjectionElem::Index(_)
                | mir::ProjectionElem::Field(..)
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
                mir::ProjectionElem::Field(field, _) => {
                    write!(fmt, ".{:?}", field.index())?;
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
                    from_end: false, ..
                } => {}
            }
        }

        Ok(())
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bound(idx) => write!(fmt, "^{}", idx),
            Self::Local(local) => write!(fmt, "_{}", local.index()),
            Self::Free(idx) => write!(fmt, "${}", idx),
        }
    }
}
