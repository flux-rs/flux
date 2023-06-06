use std::iter;

use flux_common::tracked_span_bug;
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        box_args,
        fold::{FallibleTypeFolder, TypeFoldable},
        AdtDef, BaseTy, Binder, EarlyBinder, Expr, GenericArg, Index, Loc, Path, PtrKind, Ref,
        Sort, Ty, TyKind, VariantIdx, VariantSig, FIRST_VARIANT,
    },
    rustc::mir::{FieldIdx, Place, PlaceElem},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::{
    checker::errors::CheckerErrKind,
    refine_tree::{RefineCtxt, UnpackFlags},
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

#[derive(Clone, Eq, PartialEq)]
pub(super) enum LocKind {
    Local,
    Box(Ty),
    Universal,
}

pub(super) trait LookupKey {
    type Iter<'a>: Iterator<Item = PlaceElem> + 'a
    where
        Self: 'a;

    fn loc(&self) -> Loc;

    fn proj(&self) -> Self::Iter<'_>;
}

impl LookupKey for Place {
    type Iter<'a> = impl Iterator<Item = PlaceElem> + 'a;

    fn loc(&self) -> Loc {
        Loc::Local(self.local)
    }

    fn proj(&self) -> Self::Iter<'_> {
        self.projection.iter().copied()
    }
}

impl LookupKey for Path {
    type Iter<'a> = impl Iterator<Item = PlaceElem> + 'a;

    fn loc(&self) -> Loc {
        self.loc.clone()
    }

    fn proj(&self) -> Self::Iter<'_> {
        self.projection().iter().map(|f| PlaceElem::Field(*f))
    }
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

pub(crate) fn downcast(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    adt: &AdtDef,
    substs: &[GenericArg],
    variant_idx: VariantIdx,
    idx: &Index,
) -> Result<Vec<Ty>> {
    if adt.is_struct() {
        debug_assert_eq!(variant_idx.as_u32(), 0);
        downcast_struct(genv, adt, substs, idx)
    } else if adt.is_enum() {
        downcast_enum(genv, rcx, adt, variant_idx, substs, idx)
    } else {
        tracked_span_bug!("Downcast without struct or enum!")
    }
}

/// `downcast` on struct works as follows
/// Given a struct definition
///     struct S<A..>[(i...)] { fld : T, ...}
/// and a
///     * "place" `x: S<t..>[e..]`
/// the `downcast` returns a vector of `ty` for each `fld` of `x` where
///     * `x.fld : T[A := t ..][i := e...]`
/// i.e. by substituting the type and value indices using the types and values from `x`.
pub(crate) fn downcast_struct(
    genv: &GlobalEnv,
    adt: &AdtDef,
    substs: &[GenericArg],
    idx: &Index,
) -> Result<Vec<Ty>> {
    Ok(struct_variant(genv, adt.did())?
        .subst_generics(substs)
        .replace_bound_exprs(idx.expr.expect_tuple())
        .fields
        .to_vec())
}

fn struct_variant(genv: &GlobalEnv, def_id: DefId) -> Result<EarlyBinder<Binder<VariantSig>>> {
    debug_assert!(genv.adt_def(def_id)?.is_struct());
    genv.variant_sig(def_id, VariantIdx::from_u32(0))?
        .ok_or_else(|| CheckerErrKind::OpaqueStruct(def_id))
}

/// In contrast (w.r.t. `struct`) downcast on `enum` works as follows.
/// Given
///     * a "place" `x : T[i..]`
///     * a "variant" of type `forall z..,(y:t...) => E[j...]`
/// We want `downcast` to return a vector of types _and an assertion_ by
///     1. *Instantiate* the type to fresh names `z'...` to get `(y:t'...) => T[j'...]`
///     2. *Unpack* the fields using `y:t'...`
///     3. *Assert* the constraint `i == j'...`
pub(crate) fn downcast_enum(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    adt: &AdtDef,
    variant_idx: VariantIdx,
    substs: &[GenericArg],
    idx1: &Index,
) -> Result<Vec<Ty>> {
    let variant_def = genv
        .variant_sig(adt.did(), variant_idx)?
        .expect("enums cannot be opaque")
        .subst_generics(substs)
        .replace_bound_exprs_with(|sort| rcx.define_vars(sort));

    let (.., idx2) = variant_def.ret.expect_adt();
    // FIXME(nilehmann) flatten indices
    let exprs1 = idx1.expr.expect_tuple();
    let exprs2 = idx2.expr.expect_tuple();
    debug_assert_eq!(exprs1.len(), exprs2.len());
    let constr = Expr::and(iter::zip(exprs1, exprs2).filter_map(|(e1, e2)| {
        if !e1.is_abs() && !e2.is_abs() {
            Some(Expr::eq(e1, e2))
        } else {
            None
        }
    }));
    rcx.assume_pred(constr);

    Ok(variant_def.fields.to_vec())
}
