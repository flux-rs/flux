use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        box_args,
        fold::{FallibleTypeFolder, TypeFoldable},
        BaseTy, GenericArg, Ref, Ty, TyKind, VariantIdx, FIRST_VARIANT,
    },
    rustc::mir::{FieldIdx, PlaceElem},
};
use itertools::Itertools;

use super::places_tree::downcast;
use crate::{
    checker::errors::CheckerErrKind,
    refine_tree::{RefineCtxt, UnpackFlags},
    type_env::places_tree::downcast_struct,
    CheckerConfig,
};

type Result<T = ()> = std::result::Result<T, CheckerErrKind>;

pub(crate) fn unfold(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    cursor: &mut impl Iterator<Item = PlaceElem>,
    ty: &Ty,
    checker_conf: CheckerConfig,
) -> Result<(Ty, Ty)> {
    let mut unfolder = Unfolder { genv, rcx, cursor, result: None, checker_conf };
    let updated = ty.try_fold_with(&mut unfolder)?;
    Ok((updated, unfolder.result.unwrap_or(ty.clone())))
}

pub(crate) fn lookup(cursor: &mut impl Iterator<Item = PlaceElem>, ty: &Ty) -> Result<(Ty, Ty)> {
    let mut lookup = Lookup { cursor, result: None, update: |ty| Ok(ty.clone()) };
    let updated = ty.try_fold_with(&mut lookup)?;
    Ok((updated, lookup.result.unwrap_or(ty.clone())))
}

struct Unfolder<'a, 'rcx, 'tcx, I> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    rcx: &'a mut RefineCtxt<'rcx>,
    result: Option<Ty>,
    cursor: &'a mut I,
    checker_conf: CheckerConfig,
}

impl<I> FallibleTypeFolder for Unfolder<'_, '_, '_, I>
where
    I: Iterator<Item = PlaceElem>,
{
    type Error = CheckerErrKind;

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty> {
        let Some(elem) = self.cursor.next() else {
            let ty = self.unfold(ty)?;
            self.result = Some(ty.clone());
            return Ok(ty)
        };
        let ty = self.rcx.unpack_with(ty, UnpackFlags::SHALLOW);
        match elem {
            PlaceElem::Deref => self.deref(&ty),
            PlaceElem::Field(f) => self.field(&ty, f),
            PlaceElem::Index(_) => todo!(),
            PlaceElem::Downcast(_, variant) => self.downcast(&ty, variant),
        }
    }
}

impl<I> Unfolder<'_, '_, '_, I>
where
    I: Iterator<Item = PlaceElem>,
{
    fn unfold(&mut self, ty: &Ty) -> Result<Ty> {
        if ty.is_box() {
            // TODO(nilehmann) implement unfolding of boxes
            Ok(ty.clone())
        } else if ty.is_struct() {
            self.downcast(ty, FIRST_VARIANT)
        } else {
            Ok(ty.clone())
        }
    }

    fn deref(&mut self, ty: &Ty) -> Result<Ty> {
        let ty = match ty.kind() {
            Ref!(re, ty, mutbl) => Ty::mk_ref(*re, ty.try_fold_with(self)?, *mutbl),
            _ => todo!(),
        };
        Ok(ty)
    }

    fn field(&mut self, ty: &Ty, f: FieldIdx) -> Result<Ty> {
        let ty = match ty.kind() {
            TyKind::Indexed(BaseTy::Tuple(fields), idx) => {
                let mut fields = fields.to_vec();
                fields[f.as_usize()] = fields[f.as_usize()].try_fold_with(self)?;
                Ty::indexed(BaseTy::Tuple(fields.into()), idx.clone())
            }
            TyKind::Indexed(BaseTy::Closure(def_id, fields), idx) => {
                let mut fields = fields.to_vec();
                fields[f.as_usize()] = fields[f.as_usize()].try_fold_with(self)?;
                Ty::indexed(BaseTy::Closure(*def_id, fields.into()), idx.clone())
            }
            TyKind::Indexed(BaseTy::Adt(adt, substs), idx) => {
                debug_assert!(adt.is_struct());
                let mut fields = downcast_struct(self.genv, adt, substs, idx)?
                    .into_iter()
                    .map(|ty| {
                        let ty = self.rcx.unpack(&ty);
                        self.assume_invariants(&ty);
                        ty
                    })
                    .collect_vec();
                fields[f.as_usize()] = fields[f.as_usize()].try_fold_with(self)?;
                Ty::downcast(adt.clone(), substs.clone(), FIRST_VARIANT, fields.into())
            }
            TyKind::Downcast(adt, substs, variant, fields) => {
                let mut fields = fields.to_vec();
                fields[f.as_usize()] = fields[f.as_usize()].try_fold_with(self)?;
                Ty::downcast(adt.clone(), substs.clone(), *variant, fields.into())
            }
            _ => todo!(),
        };
        Ok(ty)
    }

    fn downcast(&mut self, ty: &Ty, variant: VariantIdx) -> Result<Ty> {
        let ty = match ty.kind() {
            TyKind::Indexed(BaseTy::Adt(adt, substs), idx) => {
                let fields = downcast(self.genv, self.rcx, adt, substs, variant, idx)?
                    .into_iter()
                    .map(|ty| {
                        let ty = self.rcx.unpack(&ty);
                        self.assume_invariants(&ty);
                        ty
                    })
                    .collect_vec();
                Ty::downcast(adt.clone(), substs.clone(), FIRST_VARIANT, fields.into())
            }
            TyKind::Downcast(_, _, variant2, _) => {
                debug_assert_eq!(variant, *variant2);
                ty.clone()
            }
            _ => todo!(),
        };
        Ok(ty)
    }

    fn assume_invariants(&mut self, ty: &Ty) {
        self.rcx
            .assume_invariants(ty, self.checker_conf.check_overflow);
    }
}

struct Lookup<I, F>
where
    F: FnMut(&Ty) -> Result<Ty>,
{
    result: Option<Ty>,
    update: F,
    cursor: I,
}

impl<I, F> FallibleTypeFolder for Lookup<I, F>
where
    I: Iterator<Item = PlaceElem>,
    F: FnMut(&Ty) -> Result<Ty>,
{
    type Error = CheckerErrKind;

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty> {
        let Some(elem) = self.cursor.next() else {
            self.result = Some(ty.clone());
            return (self.update)(ty);
        };
        match elem {
            PlaceElem::Deref => self.deref(ty),
            PlaceElem::Field(f) => self.field(ty, f),
            PlaceElem::Downcast(_, _) => ty.try_fold_with(self),
            PlaceElem::Index(_) => todo!(),
        }
    }
}

impl<I, F> Lookup<I, F>
where
    I: Iterator<Item = PlaceElem>,
    F: FnMut(&Ty) -> Result<Ty>,
{
    fn deref(&mut self, ty: &Ty) -> Result<Ty> {
        let ty = match ty.kind() {
            TyKind::Indexed(BaseTy::Adt(adt, substs), idx) if adt.is_box() => {
                let (deref_ty, alloc) = box_args(substs);
                let substs = List::from_arr([
                    GenericArg::Ty(deref_ty.try_fold_with(self)?),
                    GenericArg::Ty(alloc.clone()),
                ]);
                Ty::indexed(BaseTy::Adt(adt.clone(), substs), idx.clone())
            }
            Ref!(re, deref_ty, mutbl) => Ty::mk_ref(*re, deref_ty.try_fold_with(self)?, *mutbl),
            _ => tracked_span_bug!("invalid deref on `{ty:?}`"),
        };
        Ok(ty)
    }

    fn field(&mut self, ty: &Ty, f: FieldIdx) -> Result<Ty> {
        let ty = match ty.kind() {
            TyKind::Indexed(BaseTy::Tuple(fields), idx) => {
                let fields = self.try_fold_field_at(fields, f)?;
                Ty::indexed(BaseTy::Tuple(fields), idx.clone())
            }
            TyKind::Indexed(BaseTy::Closure(def_id, fields), idx) => {
                let fields = self.try_fold_field_at(fields, f)?;
                Ty::indexed(BaseTy::Closure(*def_id, fields), idx.clone())
            }
            TyKind::Downcast(adt, substs, variant, fields) => {
                let fields = self.try_fold_field_at(fields, f)?;
                Ty::downcast(adt.clone(), substs.clone(), *variant, fields)
            }
            _ => tracked_span_bug!("invalid field projection on `{ty:?}`"),
        };
        Ok(ty)
    }

    fn try_fold_field_at(&mut self, fields: &[Ty], f: FieldIdx) -> Result<List<Ty>> {
        let mut fields = fields.to_vec();
        fields[f.as_usize()] = fields[f.as_usize()].try_fold_with(self)?;
        Ok(fields.into())
    }
}
