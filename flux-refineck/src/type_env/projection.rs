use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        box_args,
        fold::{FallibleTypeFolder, TypeFoldable},
        BaseTy, GenericArg, Loc, Path, PtrKind, Ref, Sort, Ty, TyKind, VariantIdx, FIRST_VARIANT,
    },
    rustc::mir::{FieldIdx, PlaceElem},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::places_tree::{downcast, LocKind, LookupKey};
use crate::{
    checker::errors::CheckerErrKind,
    refine_tree::{RefineCtxt, UnpackFlags},
    type_env::places_tree::downcast_struct,
    CheckerConfig,
};

type Result<T = ()> = std::result::Result<T, CheckerErrKind>;

struct PlacesTree {
    map: FxHashMap<Loc, Binding>,
}

struct Binding {
    kind: LocKind,
    ty: Ty,
}

impl PlacesTree {
    pub(crate) fn unfold(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        key: &impl LookupKey,
        checker_conf: CheckerConfig,
    ) -> Result {
        let mut path = Path::from(key.loc());
        let mut cursor = Cursor::new(key);
        loop {
            let binding = self.get_loc_mut(&path.loc);
            let unfolder = Unfolder::new(genv, rcx, &mut cursor, checker_conf);
            match unfolder.run(&path, binding)? {
                Cont::Init => tracked_span_bug!(),
                Cont::Break(_) => break,
                Cont::Continue(new) => {
                    path = new;
                }
                Cont::Insert(loc, kind, ty) => {
                    self.insert(loc.clone(), kind, ty);
                    path = Path::from(loc);
                }
            }
        }
        Ok(())
    }

    pub(crate) fn lookup(
        &mut self,
        key: &impl LookupKey,
        delegate: impl LookupDelegate,
    ) -> Result<Ty> {
        let cursor = key.proj();
        let binding = self.get_loc_mut(&key.loc());
        let mut lookup = Lookup { cursor, result: binding.ty.clone(), delegate };
        binding.ty = binding.ty.try_fold_with(&mut lookup)?;
        Ok(lookup.result)
    }

    fn insert(&mut self, loc: Loc, kind: LocKind, ty: Ty) {
        self.map.insert(loc, Binding { kind, ty });
    }

    fn get_loc_mut(&mut self, loc: &Loc) -> &mut Binding {
        self.map
            .get_mut(loc)
            .unwrap_or_else(|| tracked_span_bug!("loc not foound {loc:?}"))
    }
}

struct Unfolder<'a, 'rcx, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    rcx: &'a mut RefineCtxt<'rcx>,
    cont: Cont,
    cursor: &'a mut Cursor,
    in_ref: bool,
    checker_conf: CheckerConfig,
}

enum Cont {
    Init,
    Break(Ty),
    Continue(Path),
    Insert(Loc, LocKind, Ty),
}

impl FallibleTypeFolder for Unfolder<'_, '_, '_> {
    type Error = CheckerErrKind;

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty> {
        let Some(elem) = self.cursor.next() else {
            let ty = self.unfold(ty)?;
            self.cont = Cont::Break(ty.clone());
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

impl<'a, 'rcx, 'tcx> Unfolder<'a, 'rcx, 'tcx> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        rcx: &'a mut RefineCtxt<'rcx>,
        cursor: &'a mut Cursor,
        checker_conf: CheckerConfig,
    ) -> Self {
        Unfolder { genv, rcx, cursor, cont: Cont::Init, in_ref: false, checker_conf }
    }

    fn run(mut self, path: &Path, binding: &mut Binding) -> Result<Cont> {
        let ty = path
            .projection()
            .iter()
            .try_fold(binding.ty.clone(), |ty, f| self.field(&ty, *f))?;

        binding.ty = ty.try_fold_with(&mut self)?;
        Ok(self.cont)
    }

    fn unfold(&mut self, ty: &Ty) -> Result<Ty> {
        if ty.is_box() {
            self.deref(ty)
        } else if ty.is_struct() {
            self.downcast(ty, FIRST_VARIANT)
        } else {
            Ok(ty.clone())
        }
    }

    fn deref(&mut self, ty: &Ty) -> Result<Ty> {
        let ty = match ty.kind() {
            TyKind::Ptr(pk, path) => {
                self.cont = Cont::Continue(path.clone());
                Ty::ptr(*pk, path.clone())
            }
            TyKind::Indexed(BaseTy::Adt(adt, substs), idx) if adt.is_box() => {
                let (deref_ty, alloc) = box_args(substs);
                if self.in_ref {
                    let substs = List::from_arr([
                        GenericArg::Ty(deref_ty.try_fold_with(self)?),
                        GenericArg::Ty(alloc.clone()),
                    ]);
                    Ty::indexed(BaseTy::Adt(adt.clone(), substs), idx.clone())
                } else {
                    let loc = Loc::from(self.rcx.define_var(&Sort::Loc));
                    self.cont =
                        Cont::Insert(loc.clone(), LocKind::Box(alloc.clone()), deref_ty.clone());
                    Ty::ptr(PtrKind::Box, Path::from(loc))
                }
            }
            Ref!(re, ty, mutbl) => {
                self.in_ref = true;
                Ty::mk_ref(*re, ty.try_fold_with(self)?, *mutbl)
            }
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

struct Lookup<I, D>
where
    D: LookupDelegate,
{
    result: Ty,
    delegate: D,
    cursor: I,
}

trait LookupDelegate {
    fn update(&mut self, ty: &Ty) -> Ty;
    fn result(&mut self, old: &Ty, new: &Ty) -> Ty;
}

struct Fold;

struct Block<F>(F)
where
    F: FnMut(&Ty) -> Ty;

impl<F> LookupDelegate for Block<F>
where
    F: FnMut(&Ty) -> Ty,
{
    fn update(&mut self, ty: &Ty) -> Ty {
        (self.0)(ty)
    }

    fn result(&mut self, old: &Ty, new: &Ty) -> Ty {
        old.clone()
    }
}

impl<I, D> FallibleTypeFolder for Lookup<I, D>
where
    I: Iterator<Item = PlaceElem>,
    D: LookupDelegate,
{
    type Error = CheckerErrKind;

    fn try_fold_ty(&mut self, ty: &Ty) -> Result<Ty> {
        let Some(elem) = self.cursor.next() else {
            let updated = self.delegate.update(ty);
            self.result = self.delegate.result(ty, &updated);
            return Ok(updated);
        };
        match elem {
            PlaceElem::Deref => self.deref(ty),
            PlaceElem::Field(f) => self.field(ty, f),
            PlaceElem::Downcast(_, _) => ty.try_fold_with(self),
            PlaceElem::Index(_) => todo!(),
        }
    }
}

impl<I, D> Lookup<I, D>
where
    I: Iterator<Item = PlaceElem>,
    D: LookupDelegate,
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

struct Cursor {
    proj: Vec<PlaceElem>,
}

impl Cursor {
    fn new(key: &impl LookupKey) -> Self {
        Self { proj: key.proj().collect() }
    }
    fn next(&mut self) -> Option<PlaceElem> {
        todo!()
        // self.proj.next()
    }
}
