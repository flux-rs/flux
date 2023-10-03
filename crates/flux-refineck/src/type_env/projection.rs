use std::{clone::Clone, iter, ops::ControlFlow};

use flux_common::{iter::IterExt, tracked_span_bug};
use flux_middle::{
    global_env::GlobalEnv,
    intern::List,
    rty::{
        box_args,
        fold::{FallibleTypeFolder, TypeFoldable, TypeFolder, TypeVisitable, TypeVisitor},
        AdtDef, BaseTy, Binder, EarlyBinder, Expr, GenericArg, Index, Loc, Mutability, Path,
        PtrKind, Ref, Sort, Ty, TyKind, VariantIdx, VariantSig, FIRST_VARIANT,
    },
    rustc::mir::{FieldIdx, Place, PlaceElem},
};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;

use crate::{
    checker::errors::CheckerErrKind,
    constraint_gen::ConstrGen,
    refine_tree::{RefineCtxt, UnpackFlags},
    CheckerConfig,
};

type CheckerResult<T = ()> = std::result::Result<T, CheckerErrKind>;

#[derive(Clone, Default)]
pub(crate) struct PlacesTree {
    map: FxHashMap<Loc, Binding>,
}

#[derive(Clone)]
pub(crate) struct Binding {
    pub kind: LocKind,
    pub ty: Ty,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) enum LocKind {
    Local,
    Box(Ty),
    Universal,
}

pub(crate) trait LookupKey {
    type Iter<'a>: DoubleEndedIterator<Item = PlaceElem> + 'a
    where
        Self: 'a;

    fn loc(&self) -> Loc;

    fn proj(&self) -> Self::Iter<'_>;
}

impl LookupKey for Place {
    type Iter<'a> = impl DoubleEndedIterator<Item = PlaceElem> + 'a;

    fn loc(&self) -> Loc {
        Loc::Local(self.local)
    }

    fn proj(&self) -> Self::Iter<'_> {
        self.projection.iter().copied()
    }
}

impl LookupKey for Path {
    type Iter<'a> = impl DoubleEndedIterator<Item = PlaceElem> + 'a;

    fn loc(&self) -> Loc {
        self.loc.clone()
    }

    fn proj(&self) -> Self::Iter<'_> {
        self.projection().iter().map(|f| PlaceElem::Field(*f))
    }
}

pub(crate) struct LookupResult<'a> {
    pub ty: Ty,
    pub is_strg: bool,
    cursor: Cursor,
    bindings: &'a mut PlacesTree,
}

pub(crate) trait LookupMode {
    type Error = !;

    fn unpack(&mut self, ty: &Ty) -> Ty {
        ty.clone()
    }

    fn downcast_struct(
        &mut self,
        adt: &AdtDef,
        args: &[GenericArg],
        idx: &Index,
    ) -> Result<Vec<Ty>, Self::Error>;
}

struct Unfold<'a, 'rcx, 'tcx>(&'a GlobalEnv<'a, 'tcx>, &'a mut RefineCtxt<'rcx>);

impl LookupMode for Unfold<'_, '_, '_> {
    type Error = CheckerErrKind;

    fn unpack(&mut self, ty: &Ty) -> Ty {
        self.1.unpack_with(ty, UnpackFlags::SHALLOW)
    }

    fn downcast_struct(
        &mut self,
        adt: &AdtDef,
        args: &[GenericArg],
        idx: &Index,
    ) -> Result<Vec<Ty>, Self::Error> {
        downcast_struct(self.0, adt, args, idx)
    }
}

struct NoUnfold;

impl LookupMode for NoUnfold {
    fn downcast_struct(&mut self, _: &AdtDef, _: &[GenericArg], _: &Index) -> Result<Vec<Ty>, !> {
        tracked_span_bug!("cannot unfold in `NoUnfold` mode")
    }
}

impl PlacesTree {
    pub(crate) fn unfold(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        key: &impl LookupKey,
        checker_conf: CheckerConfig,
    ) -> CheckerResult {
        Unfolder::new(genv, rcx, key, checker_conf).run(self)
    }

    fn lookup_inner<M: LookupMode>(
        &mut self,
        key: &impl LookupKey,
        mut mode: M,
    ) -> Result<LookupResult, M::Error> {
        let mut cursor = Cursor::new(key);
        let mut ty = self.get_loc(&cursor.loc).ty.clone();
        let mut is_strg = true;
        while let Some(elem) = cursor.next() {
            ty = mode.unpack(&ty);
            match elem {
                PlaceElem::Deref => {
                    match ty.kind() {
                        TyKind::Indexed(BaseTy::Adt(adt, args), _) if adt.is_box() => {
                            ty = box_args(args).0.clone();
                        }
                        TyKind::Indexed(BaseTy::RawPtr(deref_ty, _), _) => {
                            is_strg = false;
                            ty = deref_ty.clone();
                        }
                        TyKind::Ptr(_, path) => {
                            cursor.change_root(path);
                            ty = self.get_loc(&cursor.loc).ty.clone();
                        }
                        Ref!(_, deref_ty, _) => {
                            is_strg = false;
                            ty = deref_ty.clone();
                        }
                        TyKind::Uninit => {
                            ty = Ty::uninit();
                            break;
                        }
                        _ => tracked_span_bug!("invalid deref `{ty:?}`"),
                    }
                }
                PlaceElem::Field(f) => {
                    match ty.kind() {
                        TyKind::Indexed(BaseTy::Tuple(fields), _) => {
                            ty = fields[f.as_usize()].clone();
                        }
                        TyKind::Indexed(BaseTy::Closure(_, fields), _) => {
                            ty = fields[f.as_usize()].clone();
                        }
                        TyKind::Downcast(.., fields) => {
                            ty = fields[f.as_usize()].clone();
                        }
                        TyKind::Indexed(BaseTy::Adt(adt, args), idx) => {
                            ty = mode.downcast_struct(adt, args, idx)?[f.as_usize()].clone();
                        }
                        _ => tracked_span_bug!("invalid field access `Field({f:?})` and `{ty:?}`"),
                    };
                }
                PlaceElem::Index(_) => {
                    is_strg = false;
                    match ty.kind() {
                        TyKind::Indexed(BaseTy::Array(array_ty, _), _) => {
                            ty = array_ty.clone();
                        }
                        TyKind::Indexed(BaseTy::Slice(slice_ty), _) => {
                            ty = slice_ty.clone();
                        }
                        _ => tracked_span_bug!("invalid index access `{ty:?}`"),
                    }
                }
                PlaceElem::Downcast(..) => {}
            }
        }
        cursor.reset();
        Ok(LookupResult { ty, is_strg, cursor, bindings: self })
    }

    pub(crate) fn lookup_unfolding(
        &mut self,
        genv: &GlobalEnv,
        rcx: &mut RefineCtxt,
        key: &impl LookupKey,
    ) -> CheckerResult<LookupResult> {
        self.lookup_inner(key, Unfold(genv, rcx))
    }

    pub(crate) fn lookup(&mut self, key: &impl LookupKey) -> LookupResult {
        self.lookup_inner(key, NoUnfold).into_ok()
    }

    pub(crate) fn paths(&self) -> Vec<Path> {
        let mut paths = vec![];
        self.iter_flatten(|path, _, _| paths.push(path));
        paths
    }

    pub(crate) fn get(&self, path: &Path) -> Ty {
        let mut ty = &self.get_loc(&path.loc).ty;
        for f in path.projection() {
            match ty.kind() {
                TyKind::Downcast(.., fields)
                | TyKind::Indexed(BaseTy::Closure(_, fields) | BaseTy::Tuple(fields), _) => {
                    ty = &fields[f.as_usize()];
                }
                TyKind::Uninit => return Ty::uninit(),
                _ => tracked_span_bug!("{ty:?}"),
            }
        }
        ty.clone()
    }

    pub(crate) fn fmap_mut(&mut self, mut f: impl FnMut(&Ty) -> Ty) {
        self.try_fmap_mut::<!>(|ty| Ok(f(ty))).into_ok();
    }

    fn try_fmap_mut<E>(&mut self, mut f: impl FnMut(&Ty) -> Result<Ty, E>) -> Result<(), E> {
        self.map.values_mut().try_for_each(|binding| {
            binding.ty = f(&binding.ty)?;
            Ok(())
        })
    }

    pub(crate) fn flatten(self) -> Vec<(Path, LocKind, Ty)> {
        let mut bindings = vec![];
        self.iter_flatten(|path, kind, ty| bindings.push((path, kind.clone(), ty.clone())));
        bindings
    }

    pub(crate) fn insert(&mut self, loc: Loc, kind: LocKind, ty: Ty) {
        self.map.insert(loc, Binding { kind, ty });
    }

    fn remove(&mut self, loc: &Loc) -> Binding {
        self.map.remove(loc).unwrap()
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&Loc, &Binding)> {
        self.map.iter()
    }

    fn iter_flatten(&self, mut f: impl FnMut(Path, &LocKind, &Ty)) {
        fn go(
            loc: &Loc,
            kind: &LocKind,
            ty: &Ty,
            proj: &mut Vec<FieldIdx>,
            f: &mut impl FnMut(Path, &LocKind, &Ty),
        ) {
            match ty.kind() {
                TyKind::Downcast(.., fields)
                | TyKind::Indexed(BaseTy::Tuple(fields) | BaseTy::Closure(_, fields), _) => {
                    for (idx, ty) in fields.iter().enumerate() {
                        proj.push(idx.into());
                        go(loc, kind, ty, proj, f);
                        proj.pop();
                    }
                }
                _ => f(Path::new(loc.clone(), proj.as_slice()), kind, ty),
            }
        }
        for (loc, binding) in &self.map {
            go(loc, &binding.kind, &binding.ty, &mut vec![], &mut f);
        }
    }

    pub(crate) fn get_loc(&self, loc: &Loc) -> &Binding {
        self.map
            .get(loc)
            .unwrap_or_else(|| tracked_span_bug!("loc not found {loc:?}"))
    }

    fn get_loc_mut(&mut self, loc: &Loc) -> &mut Binding {
        self.map
            .get_mut(loc)
            .unwrap_or_else(|| tracked_span_bug!("loc not found {loc:?}"))
    }
}

impl LookupResult<'_> {
    pub(crate) fn update(self, new: Ty) -> Ty {
        let old = self.ty.clone();
        Updater::update(self.bindings, self.cursor, new);
        old
    }

    pub(crate) fn unblock(self, rcx: &mut RefineCtxt) {
        if self.ty.is_uninit() {
            return;
        }
        let mut unblocked = self.ty.unblocked();
        if self.is_strg {
            unblocked = rcx.unpack(&unblocked);
        }
        Updater::update(self.bindings, self.cursor, unblocked);
    }

    pub(crate) fn block_with(self, new_ty: Ty) -> Ty {
        self.update(Ty::blocked(new_ty))
    }

    pub(crate) fn fold(self, rcx: &mut RefineCtxt, gen: &mut ConstrGen) -> CheckerResult<Ty> {
        let ty = fold(self.bindings, rcx, gen, &self.ty, self.is_strg)?;
        self.update(ty.clone());
        Ok(ty)
    }

    pub(crate) fn path(&self) -> Path {
        self.cursor.to_path()
    }
}

struct Unfolder<'a, 'rcx, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    rcx: &'a mut RefineCtxt<'rcx>,
    insertions: Vec<(Loc, Binding)>,
    cursor: Cursor,
    in_ref: Option<Mutability>,
    checker_conf: CheckerConfig,
    has_work: bool,
}

impl FallibleTypeFolder for Unfolder<'_, '_, '_> {
    type Error = CheckerErrKind;

    fn try_fold_ty(&mut self, ty: &Ty) -> CheckerResult<Ty> {
        let Some(elem) = self.cursor.next() else {
            return self.unfold(ty);
        };
        let ty = self.rcx.unpack_with(ty, UnpackFlags::SHALLOW);
        match elem {
            PlaceElem::Deref => self.deref(&ty),
            PlaceElem::Field(f) => self.field(&ty, f),
            PlaceElem::Index(_) => {
                self.index(&ty)?;
                Ok(ty.clone())
            }
            PlaceElem::Downcast(_, variant) => self.downcast(&ty, variant)?.try_fold_with(self),
        }
    }
}

impl<'a, 'rcx, 'tcx> Unfolder<'a, 'rcx, 'tcx> {
    fn new(
        genv: &'a GlobalEnv<'a, 'tcx>,
        rcx: &'a mut RefineCtxt<'rcx>,
        key: &impl LookupKey,
        checker_conf: CheckerConfig,
    ) -> Self {
        Unfolder {
            genv,
            rcx,
            cursor: Cursor::new(key),
            insertions: vec![],
            in_ref: None,
            checker_conf,
            has_work: true,
        }
    }

    fn run(mut self, bindings: &mut PlacesTree) -> CheckerResult {
        while self.should_continue() {
            let binding = bindings.get_loc_mut(&self.cursor.loc);
            binding.ty = binding.ty.try_fold_with(&mut self)?;
            for (loc, binding) in self.insertions.drain(..) {
                bindings.insert(loc, binding.kind, binding.ty);
            }
        }
        Ok(())
    }

    fn unfold(&mut self, ty: &Ty) -> CheckerResult<Ty> {
        if let TyKind::Indexed(BaseTy::Adt(adt, args), _) = ty.kind() && adt.is_box() {
            if self.in_ref.is_some() {
                Ok(ty.clone())
            } else {
                let (deref_ty, alloc) = box_args(args);
                let loc = self.unfold_box(deref_ty, alloc);
                Ok(Ty::ptr(PtrKind::Box, Path::from(loc)))
            }
        } else if ty.is_struct() {
            let ty = self.rcx.unpack_with(ty, UnpackFlags::SHALLOW);
            let ty = self.downcast(&ty, FIRST_VARIANT)?;
            Ok(ty)
        } else if ty.is_array() || ty.is_slice() {
            Ok(self.rcx.unpack_with(ty, UnpackFlags::SHALLOW))
        } else {
            Ok(ty.clone())
        }
    }

    fn deref(&mut self, ty: &Ty) -> CheckerResult<Ty> {
        let ty = match ty.kind() {
            TyKind::Ptr(pk, path) => {
                self.change_root(path);
                Ty::ptr(*pk, path.clone())
            }
            TyKind::Indexed(BaseTy::Adt(adt, args), idx) if adt.is_box() => {
                let (deref_ty, alloc) = box_args(args);
                if self.in_ref.is_some() {
                    let args = List::from_arr([
                        GenericArg::Ty(deref_ty.try_fold_with(self)?),
                        GenericArg::Ty(alloc.clone()),
                    ]);
                    Ty::indexed(BaseTy::Adt(adt.clone(), args), idx.clone())
                } else {
                    let loc = self.unfold_box(deref_ty, alloc);
                    let path = Path::from(loc);
                    self.change_root(&path);
                    Ty::ptr(PtrKind::Box, path)
                }
            }
            Ref!(re, ty, mutbl) => {
                self.in_ref = self.in_ref.max(Some(*mutbl));
                Ty::mk_ref(*re, ty.try_fold_with(self)?, *mutbl)
            }
            _ => tracked_span_bug!("invalid deref of `{ty:?}`"),
        };
        Ok(ty)
    }

    fn unfold_box(&mut self, deref_ty: &Ty, alloc: &Ty) -> Loc {
        let loc = Loc::from(self.rcx.define_var(&Sort::Loc));
        self.insertions.push((
            loc.clone(),
            Binding { kind: LocKind::Box(alloc.clone()), ty: deref_ty.clone() },
        ));
        loc
    }

    fn field(&mut self, ty: &Ty, f: FieldIdx) -> CheckerResult<Ty> {
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
            TyKind::Indexed(BaseTy::Adt(adt, args), idx) => {
                let mut fields = downcast_struct(self.genv, adt, args, idx)?
                    .into_iter()
                    .map(|ty| {
                        let ty = self.rcx.unpack_with(&ty, self.unpack_flags_for_downcast());
                        self.assume_invariants(&ty);
                        ty
                    })
                    .collect_vec();
                fields[f.as_usize()] = fields[f.as_usize()].try_fold_with(self)?;
                let args = args.with_holes();
                Ty::downcast(adt.clone(), args, ty.clone(), FIRST_VARIANT, fields.into())
            }
            TyKind::Downcast(adt, args, ty, variant, fields) => {
                let mut fields = fields.to_vec();
                fields[f.as_usize()] = fields[f.as_usize()].try_fold_with(self)?;
                Ty::downcast(adt.clone(), args.clone(), ty.clone(), *variant, fields.into())
            }
            _ => tracked_span_bug!("invalid field access for `{ty:?}`"),
        };
        Ok(ty)
    }

    fn downcast(&mut self, ty: &Ty, variant: VariantIdx) -> CheckerResult<Ty> {
        let ty = match ty.kind() {
            TyKind::Indexed(BaseTy::Adt(adt, args), idx) => {
                let fields = downcast(self.genv, self.rcx, adt, args, variant, idx)?
                    .into_iter()
                    .map(|ty| {
                        let ty = self.rcx.unpack_with(&ty, self.unpack_flags_for_downcast());
                        self.assume_invariants(&ty);
                        ty
                    })
                    .collect_vec();
                Ty::downcast(adt.clone(), args.with_holes(), ty.clone(), variant, fields.into())
            }
            TyKind::Downcast(.., variant2, _) => {
                debug_assert_eq!(variant, *variant2);
                ty.clone()
            }
            _ => tracked_span_bug!("invalid downcast `{ty:?}`"),
        };
        Ok(ty)
    }

    fn index(&mut self, ty: &Ty) -> CheckerResult {
        match ty.kind() {
            TyKind::Indexed(BaseTy::Array(arr_ty, _), _) => {
                arr_ty.try_fold_with(self)?;
            }
            TyKind::Indexed(BaseTy::Slice(slice_ty), _) => {
                slice_ty.try_fold_with(self)?;
            }
            _ => tracked_span_bug!("invalid index on `{ty:?}`"),
        }
        Ok(())
    }

    fn assume_invariants(&mut self, ty: &Ty) {
        self.rcx
            .assume_invariants(ty, self.checker_conf.check_overflow);
    }

    fn change_root(&mut self, path: &Path) {
        self.has_work = true;
        self.cursor.change_root(path);
    }

    fn unpack_flags_for_downcast(&self) -> UnpackFlags {
        if self.in_ref == Some(Mutability::Mut) {
            UnpackFlags::NO_UNPACK_EXISTS
        } else {
            UnpackFlags::empty()
        }
    }

    fn should_continue(&mut self) -> bool {
        if self.has_work {
            self.has_work = false;
            true
        } else {
            false
        }
    }
}

struct Updater<'a> {
    new_ty: Ty,
    cursor: &'a mut Cursor,
}

impl TypeFolder for Updater<'_> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        let Some(elem) = self.cursor.next() else {
            return self.new_ty.clone();
        };
        match elem {
            PlaceElem::Deref => self.deref(ty),
            PlaceElem::Field(f) => self.field(ty, f),
            PlaceElem::Downcast(_, _) => ty.fold_with(self),
            PlaceElem::Index(_) => {
                tracked_span_bug!("cannot update inside array or slice")
            }
        }
    }
}

impl<'a> Updater<'a> {
    fn new(cursor: &'a mut Cursor, new_ty: Ty) -> Self {
        Self { new_ty, cursor }
    }

    fn update(bindings: &mut PlacesTree, mut cursor: Cursor, new_ty: Ty) {
        let binding = bindings.get_loc_mut(&cursor.loc);
        let mut lookup = Updater::new(&mut cursor, new_ty);
        binding.ty = binding.ty.fold_with(&mut lookup);
    }

    fn deref(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(BaseTy::Adt(adt, args), idx) if adt.is_box() => {
                let (deref_ty, alloc) = box_args(args);
                let args = List::from_arr([
                    GenericArg::Ty(deref_ty.fold_with(self)),
                    GenericArg::Ty(alloc.clone()),
                ]);
                Ty::indexed(BaseTy::Adt(adt.clone(), args), idx.clone())
            }
            TyKind::Ptr(..) => {
                tracked_span_bug!("cannot update through pointer");
            }
            Ref!(re, deref_ty, mutbl) => Ty::mk_ref(*re, deref_ty.fold_with(self), *mutbl),
            _ => tracked_span_bug!("invalid deref on `{ty:?}`"),
        }
    }

    fn field(&mut self, ty: &Ty, f: FieldIdx) -> Ty {
        match ty.kind() {
            TyKind::Indexed(BaseTy::Tuple(fields), idx) => {
                let fields = self.fold_field_at(fields, f);
                Ty::indexed(BaseTy::Tuple(fields), idx.clone())
            }
            TyKind::Indexed(BaseTy::Closure(def_id, fields), idx) => {
                let fields = self.fold_field_at(fields, f);
                Ty::indexed(BaseTy::Closure(*def_id, fields), idx.clone())
            }
            TyKind::Downcast(adt, args, ty, variant, fields) => {
                let fields = self.fold_field_at(fields, f);
                Ty::downcast(adt.clone(), args.clone(), ty.clone(), *variant, fields)
            }
            _ => tracked_span_bug!("invalid field projection on `{ty:?}`"),
        }
    }

    fn fold_field_at(&mut self, fields: &[Ty], f: FieldIdx) -> List<Ty> {
        let mut fields = fields.to_vec();
        fields[f.as_usize()] = fields[f.as_usize()].fold_with(self);
        fields.into()
    }
}

struct Cursor {
    loc: Loc,
    proj: Vec<PlaceElem>,
    pos: usize,
}

impl Cursor {
    fn new(key: &impl LookupKey) -> Self {
        let proj = key.proj().rev().collect_vec();
        let pos = proj.len();
        Self { loc: key.loc(), proj, pos }
    }

    fn change_root(&mut self, path: &Path) {
        self.proj.truncate(self.pos);
        self.proj.extend(
            path.projection()
                .iter()
                .rev()
                .copied()
                .map(PlaceElem::Field),
        );
        self.loc = path.loc.clone();
        self.pos = self.proj.len();
    }

    fn to_path(&self) -> Path {
        let mut proj = vec![];
        for elem in self.proj.iter().rev() {
            match *elem {
                PlaceElem::Field(f) => proj.push(f),
                PlaceElem::Downcast(_, _) => {}
                PlaceElem::Deref | PlaceElem::Index(_) => {
                    break;
                }
            }
        }
        Path::new(self.loc.clone(), List::from_vec(proj))
    }

    fn next(&mut self) -> Option<PlaceElem> {
        if self.pos > 0 {
            self.pos -= 1;
            Some(self.proj[self.pos])
        } else {
            None
        }
    }

    fn reset(&mut self) {
        self.pos = self.proj.len();
    }
}

pub(crate) fn downcast(
    genv: &GlobalEnv,
    rcx: &mut RefineCtxt,
    adt: &AdtDef,
    args: &[GenericArg],
    variant_idx: VariantIdx,
    idx: &Index,
) -> CheckerResult<Vec<Ty>> {
    if adt.is_struct() {
        debug_assert_eq!(variant_idx.as_u32(), 0);
        downcast_struct(genv, adt, args, idx)
    } else if adt.is_enum() {
        downcast_enum(genv, rcx, adt, variant_idx, args, idx)
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
    args: &[GenericArg],
    idx: &Index,
) -> CheckerResult<Vec<Ty>> {
    Ok(struct_variant(genv, adt.did())?
        .instantiate(args, &[])
        .replace_bound_exprs(idx.expr.expect_tuple())
        .fields
        .to_vec())
}

fn struct_variant(
    genv: &GlobalEnv,
    def_id: DefId,
) -> CheckerResult<EarlyBinder<Binder<VariantSig>>> {
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
    args: &[GenericArg],
    idx1: &Index,
) -> CheckerResult<Vec<Ty>> {
    let variant_def = genv
        .variant_sig(adt.did(), variant_idx)?
        .expect("enums cannot be opaque")
        .instantiate(args, &[])
        .replace_bound_exprs_with(|sort, _| rcx.define_vars(sort));

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

fn fold(
    bindings: &mut PlacesTree,
    rcx: &mut RefineCtxt,
    gen: &mut ConstrGen,
    ty: &Ty,
    is_strg: bool,
) -> CheckerResult<Ty> {
    match ty.kind() {
        TyKind::Ptr(PtrKind::Box, path) => {
            let loc = path.to_loc().unwrap();
            let binding = bindings.remove(&loc);
            let LocKind::Box(alloc) = binding.kind else {
                tracked_span_bug!("box pointer to non-box loc");
            };
            let deref_ty = fold(bindings, rcx, gen, &binding.ty, is_strg)?;
            Ok(gen.genv.mk_box(deref_ty, alloc))
        }
        Ref!(re, deref_ty, mutbl) => {
            let deref_ty = fold(bindings, rcx, gen, deref_ty, is_strg)?;
            Ok(Ty::mk_ref(*re, deref_ty, *mutbl))
        }
        TyKind::Downcast(adt, args, ty_, variant_idx, fields) => {
            if is_strg {
                let variant_sig = gen
                    .genv
                    .variant_sig(adt.did(), *variant_idx)?
                    .expect("unexpected opaque struct");

                let fields = fields
                    .iter()
                    .map(|ty| fold(bindings, rcx, gen, ty, is_strg))
                    .try_collect_vec()?;

                let partially_moved = fields.iter().any(|ty| ty.is_uninit());
                let ty = if partially_moved {
                    Ty::uninit()
                } else {
                    gen.check_constructor(rcx, variant_sig, args, &fields)
                        .unwrap_or_else(|err| tracked_span_bug!("{err:?}"))
                };

                Ok(ty)
            } else {
                Ok(ty_.clone())
            }
        }
        TyKind::Indexed(BaseTy::Tuple(fields), idx) => {
            debug_assert_eq!(idx.expr, Expr::unit());

            let fields = fields
                .iter()
                .map(|ty| fold(bindings, rcx, gen, ty, is_strg))
                .try_collect_vec()?;

            let partially_moved = fields.iter().any(|ty| ty.is_uninit());
            let ty = if partially_moved { Ty::uninit() } else { Ty::tuple(fields) };
            Ok(ty)
        }
        _ => Ok(ty.clone()),
    }
}

mod pretty {
    use std::fmt;

    use flux_middle::pretty::*;
    use itertools::Itertools;
    use rustc_middle::ty::TyCtxt;

    use super::*;

    impl Pretty for PlacesTree {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "{{{}}}",
                ^self
                    .iter()
                    .filter(|(_, binding)| !cx.hide_uninit || !binding.ty.is_uninit())
                    .sorted_by(|(loc1, _), (loc2, _)| loc1.cmp(loc2))
                    .format_with(", ", |(loc, binding), f| {
                        f(&format_args_cx!("{:?}:{:?} {:?}", loc, &binding.kind, &binding.ty))
                    })
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx)
                .kvar_args(KVarArgs::Hide)
                .hide_binder(true)
        }
    }

    impl Pretty for LocKind {
        fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match self {
                LocKind::Local | LocKind::Universal => Ok(()),
                LocKind::Box(_) => w!("[box]"),
            }
        }
    }

    impl_debug_with_default_cx!(PlacesTree);
}

impl TypeVisitable for PlacesTree {
    fn visit_with<V: TypeVisitor>(&self, _visitor: &mut V) -> ControlFlow<V::BreakTy, ()> {
        unimplemented!()
    }
}

impl TypeFoldable for PlacesTree {
    fn try_fold_with<F: FallibleTypeFolder>(&self, folder: &mut F) -> Result<Self, F::Error> {
        let mut this = self.clone();
        this.try_fmap_mut(|ty| ty.try_fold_with(folder))?;
        Ok(this)
    }
}
