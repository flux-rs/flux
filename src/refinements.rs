extern crate arena;
extern crate rustc_index;

use super::syntax::ast;
use arena::TypedArena;
use rustc::mir;
pub use rustc::mir::interpret::{ConstValue, Scalar};
use rustc::ty::{self, Ty, TyCtxt};
use rustc_hir::BodyId;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub struct FnRefines<'rcx, 'tcx> {
    pub body_id: BodyId,
    pub fn_decl: FnDecl<'rcx, 'tcx>,
    pub local_decls: HashMap<mir::Local, &'rcx Refine<'rcx, 'tcx>>,
}

#[derive(Debug)]
pub struct FnDecl<'rcx, 'tcx> {
    pub inputs: Vec<&'rcx Refine<'rcx, 'tcx>>,
    pub output: &'rcx Refine<'rcx, 'tcx>,
}

#[derive(Debug)]
pub enum Refine<'rcx, 'tcx> {
    Unary(ast::UnOpKind, &'rcx Refine<'rcx, 'tcx>),
    Binary(
        &'rcx Refine<'rcx, 'tcx>,
        ast::BinOpKind,
        &'rcx Refine<'rcx, 'tcx>,
    ),
    Constant(Ty<'tcx>, ConstValue<'tcx>),
    Place(Place<'tcx>),
}

impl<'rcx, 'tcx> Refine<'rcx, 'tcx> {
    pub fn iter_places(&self, mut f: impl FnMut(Place<'tcx>) -> ()) -> () {
        self._iter_places(&mut f)
    }

    pub fn _iter_places(&self, f: &mut impl FnMut(Place<'tcx>) -> ()) -> () {
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
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Place<'tcx> {
    pub var: Var,
    pub projection: &'tcx ty::List<mir::PlaceElem<'tcx>>,
}

impl<'tcx> fmt::Debug for Place<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.var.0)?;
        for elem in self.projection.iter() {
            match elem {
                mir::ProjectionElem::Field(field, _) => {
                    write!(f, ".{}", field.index())?;
                }
                _ => unimplemented!("{:?}", elem),
            }
        }
        Ok(())
    }
}

pub struct VarSubst {
    map: HashMap<Var, mir::Local>,
}

impl VarSubst {
    pub fn empty() -> Self {
        VarSubst {
            map: HashMap::new(),
        }
    }

    pub fn subst<'tcx>(&self, place: Place<'tcx>) -> Option<mir::Place<'tcx>> {
        self.lookup(place.var).map(|local| mir::Place {
            local,
            projection: place.projection,
        })
    }

    pub fn lookup(&self, var: Var) -> Option<mir::Local> {
        self.map.get(&var).copied()
    }

    pub fn extend_with_fresh(&mut self, local: mir::Local) -> Var {
        // 0 is reserved for nu
        let var = Var(local.as_u32() + 1);
        self.map.insert(var, local);
        var
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Var(pub u32);

impl Var {
    pub fn nu() -> Self {
        Var(0)
    }
}

pub struct RefineCtxt<'rcx, 'tcx> {
    tcx: TyCtxt<'tcx>,
    arena: &'rcx TypedArena<Refine<'rcx, 'tcx>>,
    pub refine_true: &'rcx Refine<'rcx, 'tcx>,
    pub nu: &'rcx Refine<'rcx, 'tcx>,
}

impl<'rcx, 'tcx> RefineCtxt<'rcx, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, arena: &'rcx TypedArena<Refine<'rcx, 'tcx>>) -> Self {
        let refine_true = arena.alloc(Refine::Constant(
            tcx.types.bool,
            ConstValue::Scalar(Scalar::from_bool(true)),
        ));
        let nu = arena.alloc(Refine::Place(Place::from_var(Var::nu())));
        RefineCtxt {
            tcx,
            arena,
            refine_true,
            nu,
        }
    }

    pub fn mk_binary(
        &'rcx self,
        lhs: &'rcx Refine<'rcx, 'tcx>,
        op: ast::BinOpKind,
        rhs: &'rcx Refine<'rcx, 'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Binary(lhs, op, rhs))
    }

    pub fn mk_unary(
        &'rcx self,
        op: ast::UnOpKind,
        expr: &'rcx Refine<'rcx, 'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Unary(op, expr))
    }

    pub fn mk_place(&'rcx self, place: Place<'tcx>) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Place(place))
    }

    pub fn mk_constant(
        &'rcx self,
        ty: Ty<'tcx>,
        val: ConstValue<'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        self.arena.alloc(Refine::Constant(ty, val))
    }

    pub fn mk_not(&'rcx self, refine: &'rcx Refine<'rcx, 'tcx>) -> &'rcx Refine<'rcx, 'tcx> {
        self.mk_unary(ast::UnOpKind::Not, refine)
    }

    pub fn mk_place_field(
        &'rcx self,
        place: Place<'tcx>,
        field: mir::Field,
        ty: Ty<'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        self.mk_place_elem(place, mir::PlaceElem::Field(field, ty))
    }

    pub fn mk_place_elem(
        &'rcx self,
        place: Place<'tcx>,
        elem: mir::PlaceElem<'tcx>,
    ) -> &'rcx Refine<'rcx, 'tcx> {
        let mut projection = place.projection.to_vec();
        projection.push(elem);
        self.arena.alloc(Refine::Place(Place {
            var: place.var,
            projection: self.tcx.intern_place_elems(&projection),
        }))
    }
}
