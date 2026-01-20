//! A canonical type is a type where all [existentials] and [constraint predicates] are *hoisted* to
//! the top level. For example, the canonical version of `∃a. {∃b. i32[a + b] | b > 0}` is
//! `∃a,b. {i32[a + b] | b > 0}`.
//!
//! Type constructors introduce scopes that can limit the hoisting. For instance, it is generally
//! not permitted to hoist an existential out of a generic argument. For example, in `Vec<∃v. i32[v]>`
//! the existential inside the `Vec` cannot be hoisted out.
//!
//! However, some type constructors are more "lenient" with respect to hoisting. Consider the tuple
//! `(∃a. i32[a], ∃b. i32[b])`. Hoisting the existentials results in `∃a,b. (i32[a], i32[b])` which
//! is an equivalent type (in the sense that subtyping holds both ways). The same applies to shared
//! references: `&∃a. i32[a]` is equivalent to `∃a. &i32[a]`. We refer to this class of type
//! constructors as *transparent*. Hoisting existential out of transparent type constructors is useful
//! as it allows the logical information to be extracted from the type.
//!
//! And important case is mutable references. In some situations, it is sound to hoist out of mutable
//! references. For example, if we have a variable in the environment of type `&mut ∃v. T[v]`, it is
//! sound to treat it as `&mut T[a]` for a freshly generated `a` (assuming the lifetime of the
//! reference is alive). However, this may result in a type that is *too specific* because the index
//! `a` cannot be updated anymore.
//!
//! By default, we do *shallow* hoisting, i.e., we stop at the first type constructor. This is enough
//! for cases where we need to inspect a type structurally one level. The amount of hoisting can be
//! controlled by configuring the [`Hoister`] struct.
//!
//! It's also important to note that canonizalization doesn't imply any form of semantic equality
//! and it is just a best effort to facilitate syntactic manipulation. For example, the types
//! `∃a,b. (i32[a], i32[b])` and `∃a,b. (i32[b], i32[a])` are semantically equal but hoisting won't
//! account for it.
//!
//! [existentials]: TyKind::Exists
//! [constraint predicates]: TyKind::Constr
use std::fmt::Write;

use flux_arc_interner::List;
use flux_macros::{TypeFoldable, TypeVisitable};
use itertools::Itertools;
use rustc_ast::Mutability;
use rustc_span::Symbol;
use rustc_type_ir::{BoundVar, INNERMOST};

use super::{
    BaseTy, Binder, BoundVariableKind, Expr, FnSig, GenericArg, GenericArgsExt, PolyFnSig,
    SubsetTy, Ty, TyCtor, TyKind, TyOrBase,
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable, TypeVisitable},
};
use crate::rty::{BoundReftKind, ExprKind, HoleKind};

/// The [`Hoister`] struct is responsible for hoisting existentials and predicates out of a type.
/// It can be configured to stop hoisting at specific type constructors.
///
/// The struct is generic on a delegate `D` because we use it to do *local* hoisting, keeping
/// variables bound with a [`Binder`], and for *freeing* variables into the refinement context.
// Should we use a builder for this?
pub struct Hoister<D> {
    pub delegate: D,
    in_boxes: bool,
    in_downcast: bool,
    in_mut_refs: bool,
    in_shr_refs: bool,
    in_strg_refs: bool,
    in_tuples: bool,
    existentials: bool,
    slices: bool,
}

pub trait HoisterDelegate {
    fn hoist_exists(&mut self, ty_ctor: &TyCtor) -> Ty;
    fn hoist_constr(&mut self, pred: Expr);
}

impl<D> Hoister<D> {
    pub fn with_delegate(delegate: D) -> Self {
        Hoister {
            delegate,
            in_tuples: false,
            in_shr_refs: false,
            in_mut_refs: false,
            in_strg_refs: false,
            in_boxes: false,
            in_downcast: false,
            existentials: true,
            slices: false,
        }
    }

    pub fn hoist_inside_shr_refs(mut self, shr_refs: bool) -> Self {
        self.in_shr_refs = shr_refs;
        self
    }

    pub fn hoist_inside_mut_refs(mut self, mut_refs: bool) -> Self {
        self.in_mut_refs = mut_refs;
        self
    }

    pub fn hoist_inside_strg_refs(mut self, strg_refs: bool) -> Self {
        self.in_strg_refs = strg_refs;
        self
    }

    pub fn hoist_inside_tuples(mut self, tuples: bool) -> Self {
        self.in_tuples = tuples;
        self
    }

    pub fn hoist_inside_boxes(mut self, boxes: bool) -> Self {
        self.in_boxes = boxes;
        self
    }

    pub fn hoist_inside_downcast(mut self, downcast: bool) -> Self {
        self.in_downcast = downcast;
        self
    }

    pub fn hoist_existentials(mut self, exists: bool) -> Self {
        self.existentials = exists;
        self
    }

    pub fn hoist_slices(mut self, slices: bool) -> Self {
        self.slices = slices;
        self
    }

    pub fn transparent(self) -> Self {
        self.hoist_inside_boxes(true)
            .hoist_inside_downcast(true)
            .hoist_inside_mut_refs(false)
            .hoist_inside_shr_refs(true)
            .hoist_inside_strg_refs(true)
            .hoist_inside_tuples(true)
            .hoist_slices(true)
    }

    pub fn shallow(self) -> Self {
        self.hoist_inside_boxes(false)
            .hoist_inside_downcast(false)
            .hoist_inside_mut_refs(false)
            .hoist_inside_shr_refs(false)
            .hoist_inside_strg_refs(false)
            .hoist_inside_tuples(false)
    }
}

impl<D: HoisterDelegate> Hoister<D> {
    pub fn hoist(&mut self, ty: &Ty) -> Ty {
        ty.fold_with(self)
    }
}

/// Is `ty` of the form `&m (&m ... (&m T))` where `T` is an exi-indexed slice?
/// We need to do a "transitive" check to deal with cases like `&mut &mut [i32]`
/// which arise from closures like that in `tests/tests/pos/surface/closure03.rs`.
fn is_indexed_slice(ty: &Ty) -> bool {
    let Some(bty) = ty.as_bty_skipping_existentials() else {
        return false;
    };
    match bty {
        BaseTy::Slice(_) => true,
        BaseTy::Ref(_, ty, _) => is_indexed_slice(ty),
        _ => false,
    }
}

impl<D: HoisterDelegate> TypeFolder for Hoister<D> {
    fn fold_ty(&mut self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, idx) => Ty::indexed(bty.fold_with(self), idx.clone()),
            TyKind::Exists(ty_ctor) if self.existentials => {
                // Avoid hoisting useless parameters for unit sorts. This is important for
                // canonicalization because we assume mutable references won't be under a
                // binder after we canonicalize them.
                // FIXME(nilehmann) this same logic is repeated in a couple of places, e.g.,
                // TyCtor::to_ty
                match &ty_ctor.vars()[..] {
                    [BoundVariableKind::Refine(sort, ..)] => {
                        if sort.is_unit() {
                            ty_ctor.replace_bound_reft(&Expr::unit())
                        } else if let Some(def_id) = sort.is_unit_adt() {
                            ty_ctor.replace_bound_reft(&Expr::unit_struct(def_id))
                        } else {
                            self.delegate.hoist_exists(ty_ctor)
                        }
                    }
                    _ => self.delegate.hoist_exists(ty_ctor),
                }
                .fold_with(self)
            }
            TyKind::Constr(pred, ty) => {
                self.delegate.hoist_constr(pred.clone());
                ty.fold_with(self)
            }
            TyKind::StrgRef(..) if self.in_strg_refs => ty.super_fold_with(self),
            TyKind::Downcast(..) if self.in_downcast => ty.super_fold_with(self),
            _ => ty.clone(),
        }
    }

    fn fold_bty(&mut self, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, args) if adt_def.is_box() && self.in_boxes => {
                let (boxed, alloc) = args.box_args();
                let args = List::from_arr([
                    GenericArg::Ty(boxed.fold_with(self)),
                    GenericArg::Ty(alloc.clone()),
                ]);
                BaseTy::Adt(adt_def.clone(), args)
            }
            BaseTy::Ref(re, ty, mutability) if is_indexed_slice(ty) && self.slices => {
                BaseTy::Ref(*re, ty.fold_with(self), *mutability)
            }
            BaseTy::Ref(re, ty, Mutability::Not) if self.in_shr_refs => {
                BaseTy::Ref(*re, ty.fold_with(self), Mutability::Not)
            }
            BaseTy::Ref(re, ty, Mutability::Mut) if self.in_mut_refs => {
                BaseTy::Ref(*re, ty.fold_with(self), Mutability::Mut)
            }
            BaseTy::Tuple(tys) if self.in_tuples => BaseTy::Tuple(tys.fold_with(self)),
            _ => bty.clone(),
        }
    }
}

#[derive(Default)]
pub struct LocalHoister {
    vars: Vec<BoundVariableKind>,
    preds: Vec<Expr>,
    pub name: Option<Symbol>,
}

impl LocalHoister {
    pub fn new(vars: Vec<BoundVariableKind>) -> Self {
        LocalHoister { vars, preds: vec![], name: None }
    }

    pub fn bind<T>(self, f: impl FnOnce(List<BoundVariableKind>, Vec<Expr>) -> T) -> Binder<T> {
        let vars = List::from_vec(self.vars);
        Binder::bind_with_vars(f(vars.clone(), self.preds), vars)
    }
}

impl HoisterDelegate for &mut LocalHoister {
    fn hoist_exists(&mut self, ty_ctor: &TyCtor) -> Ty {
        ty_ctor.replace_bound_refts_with(|sort, mode, kind| {
            let idx = self.vars.len();
            let kind = if let Some(name) = self.name { BoundReftKind::Named(name) } else { kind };
            self.vars
                .push(BoundVariableKind::Refine(sort.clone(), mode, kind));
            Expr::bvar(INNERMOST, BoundVar::from_usize(idx), kind)
        })
    }

    fn hoist_constr(&mut self, pred: Expr) {
        self.preds.push(pred);
    }
}

impl PolyFnSig {
    /// Convert a function signature with existentials to one where they are all
    /// bound at the top level. Performs a transparent (i.e. not shallow)
    /// canonicalization.
    /// The uses the `LocalHoister` machinery to convert a function template _without_
    /// binders, e.g. `fn ({v.i32 | *}) -> {v.i32|*})`
    /// into one _with_ input binders, e.g. `forall <a:int>. fn ({i32[a]|*}) -> {v.i32|*}`
    /// after which the hole-filling machinery can be used to fill in the holes.
    /// This lets us get "dependent signatures" for closures, where the output
    /// can refer to the input. e.g. see `tests/pos/surface/closure09.rs`
    pub fn hoist_input_binders(&self) -> Self {
        let original_vars = self.vars().to_vec();
        let fn_sig = self.skip_binder_ref();

        let mut delegate =
            LocalHoister { vars: original_vars, preds: fn_sig.requires().to_vec(), name: None };
        let mut hoister = Hoister::with_delegate(&mut delegate).transparent();

        let inputs = fn_sig
            .inputs()
            .iter()
            .map(|ty| hoister.hoist(ty))
            .collect_vec();

        delegate.bind(|_vars, mut preds| {
            let mut keep_hole = true;
            preds.retain(|pred| {
                if let ExprKind::Hole(HoleKind::Pred) = pred.kind() {
                    std::mem::replace(&mut keep_hole, false)
                } else {
                    true
                }
            });

            FnSig::new(
                fn_sig.safety,
                fn_sig.abi,
                preds.into(),
                inputs.into(),
                fn_sig.output().clone(),
                fn_sig.no_panic,
                fn_sig.lifted,
            )
        })
    }
}

impl Ty {
    /// Hoist existentials and predicates inside the type stopping when encountering the first
    /// type constructor.
    pub fn shallow_canonicalize(&self) -> CanonicalTy {
        let mut delegate = LocalHoister::default();
        let ty = self.shift_in_escaping(1);
        let ty = Hoister::with_delegate(&mut delegate).hoist(&ty);
        let constr_ty = delegate.bind(|_, preds| {
            let pred = Expr::and_from_iter(preds);
            CanonicalConstrTy { ty, pred }
        });
        if constr_ty.vars().is_empty() {
            CanonicalTy::Constr(constr_ty.skip_binder().shift_out_escaping(1))
        } else {
            CanonicalTy::Exists(constr_ty)
        }
    }
}

#[derive(TypeVisitable, TypeFoldable)]
pub struct CanonicalConstrTy {
    /// Guaranteed to not have any (shallow) [existential] or [constraint] types
    ///
    /// [existential]: TyKind::Exists
    /// [constraint]: TyKind::Constr
    ty: Ty,
    pred: Expr,
}

impl CanonicalConstrTy {
    pub fn ty(&self) -> Ty {
        self.ty.clone()
    }

    pub fn pred(&self) -> Expr {
        self.pred.clone()
    }

    pub fn to_ty(&self) -> Ty {
        Ty::constr(self.pred(), self.ty())
    }
}

/// A (shallowly) canonicalized type. This can be either of the form `{T | p}` or `∃v0,…,vn. {T | p}`,
/// where `T` doesnt have any (shallow) [existential] or [constraint] types.
///
/// When canonicalizing a type without a [constraint] type, `p` will be [`Expr::tt()`].
///
/// [existential]: TyKind::Exists
/// [constraint]: TyKind::Constr
#[derive(TypeVisitable)]
pub enum CanonicalTy {
    /// A type of the form `{T | p}`
    Constr(CanonicalConstrTy),
    /// A type of the form `∃v0,…,vn. {T | p}`
    Exists(Binder<CanonicalConstrTy>),
}

impl CanonicalTy {
    pub fn to_ty(&self) -> Ty {
        match self {
            CanonicalTy::Constr(constr_ty) => constr_ty.to_ty(),
            CanonicalTy::Exists(poly_constr_ty) => {
                Ty::exists(poly_constr_ty.as_ref().map(CanonicalConstrTy::to_ty))
            }
        }
    }

    pub fn as_ty_or_base(&self) -> TyOrBase {
        match self {
            CanonicalTy::Constr(constr_ty) => {
                if let TyKind::Indexed(bty, idx) = constr_ty.ty.kind() {
                    // given {b[e] | p} return λv. {b[v] | p ∧ v == e}

                    // HACK(nilehmann) avoid adding trivial `v == ()` equalities, if we don't do it,
                    // some debug assertions fail. The assertions expect types to be unrefined so they
                    // only check for syntactical equality. We should change those cases to handle
                    // refined types and/or ensure some canonical representation for unrefined types.
                    let pred = if idx.is_unit() {
                        constr_ty.pred.clone()
                    } else {
                        Expr::and(&constr_ty.pred, Expr::eq(Expr::nu(), idx.shift_in_escaping(1)))
                    };
                    let sort = bty.sort();
                    let constr = SubsetTy::new(bty.shift_in_escaping(1), Expr::nu(), pred);
                    TyOrBase::Base(Binder::bind_with_sort(constr, sort))
                } else {
                    TyOrBase::Ty(self.to_ty())
                }
            }
            CanonicalTy::Exists(poly_constr_ty) => {
                let constr = poly_constr_ty.as_ref().skip_binder();
                if let TyKind::Indexed(bty, idx) = constr.ty.kind()
                    && idx.is_nu()
                {
                    let ctor = poly_constr_ty
                        .as_ref()
                        .map(|constr| SubsetTy::new(bty.clone(), idx, &constr.pred));
                    TyOrBase::Base(ctor)
                } else {
                    TyOrBase::Ty(self.to_ty())
                }
            }
        }
    }
}

mod pretty {
    use super::*;
    use crate::pretty::*;

    impl Pretty for CanonicalConstrTy {
        fn fmt(&self, cx: &PrettyCx, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if self.pred().is_trivially_true() {
                w!(cx, f, "{:?}", &self.ty)
            } else {
                w!(cx, f, "{{ {:?} | {:?} }}", &self.ty, &self.pred)
            }
        }
    }

    impl Pretty for CanonicalTy {
        fn fmt(&self, cx: &PrettyCx, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                CanonicalTy::Constr(constr) => w!(cx, f, "{:?}", constr),
                CanonicalTy::Exists(poly_constr) => {
                    let redundant_bvars = poly_constr.skip_binder_ref().redundant_bvars();
                    cx.with_bound_vars_removable(
                        poly_constr.vars(),
                        redundant_bvars,
                        None,
                        |f_body| {
                            let constr = poly_constr.skip_binder_ref();
                            if constr.pred().is_trivially_true() {
                                w!(cx, f_body, "{:?}", &constr.ty)
                            } else {
                                w!(cx, f_body, "{{ {:?} | {:?} }}", &constr.ty, &constr.pred)
                            }
                        },
                        |(), bound_var_layer, body| {
                            let vars = poly_constr
                                .vars()
                                .into_iter()
                                .enumerate()
                                .filter_map(|(idx, var)| {
                                    let not_removed = !bound_var_layer
                                        .successfully_removed_vars
                                        .contains(&BoundVar::from_usize(idx));
                                    let refine_var = matches!(var, BoundVariableKind::Refine(..));
                                    if not_removed && refine_var { Some(var.clone()) } else { None }
                                })
                                .collect_vec();
                            if vars.is_empty() {
                                write!(f, "{}", body)
                            } else {
                                let left = "{";
                                let right = format!(". {} }}", body);
                                cx.fmt_bound_vars(false, left, &vars, &right, f)
                            }
                        },
                    )
                }
            }
        }
    }

    impl_debug_with_default_cx!(CanonicalTy, CanonicalConstrTy);
}
