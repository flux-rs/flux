//! Check whether two refinemnt types/signatures are structurally compatible.
//!
//! Used to check if a user spec is compatible with the underlying rust type. The code also
//! infer types annotated with `_` in the surface syntax.

use std::{fmt, iter};

use flux_common::bug;
use flux_errors::Errors;
use flux_middle::{
    def_id::MaybeExternId,
    fhir,
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{
        self,
        fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
        refining::{Refine as _, Refiner},
    },
};
use flux_rustc_bridge::ty::{self, FieldIdx, VariantIdx};
use rustc_ast::Mutability;
use rustc_data_structures::unord::UnordMap;
use rustc_type_ir::{DebruijnIndex, INNERMOST, InferConst};

pub(crate) fn type_alias(
    genv: GlobalEnv,
    alias: &fhir::TyAlias,
    alias_ty: &rty::TyCtor,
    def_id: MaybeExternId,
) -> QueryResult<rty::TyCtor> {
    let rust_ty = genv.lower_type_of(def_id.resolved_id())?.skip_binder();
    let expected = rust_ty.refine(&Refiner::default_for_item(genv, def_id.resolved_id())?)?;
    let mut zipper = Zipper::new(genv, def_id);

    if zipper
        .enter_a_binder(alias_ty, |zipper, ty| zipper.zip_ty(ty, &expected))
        .is_err()
    {
        zipper
            .errors
            .emit(errors::IncompatibleRefinement::type_alias(genv, def_id, alias));
    }

    zipper.errors.to_result()?;

    Ok(zipper.holes.replace_holes(alias_ty))
}

pub(crate) fn fn_sig(
    genv: GlobalEnv,
    decl: &fhir::FnDecl,
    fn_sig: &rty::PolyFnSig,
    def_id: MaybeExternId,
) -> QueryResult<rty::PolyFnSig> {
    let rust_fn_sig = genv.lower_fn_sig(def_id.resolved_id())?.skip_binder();

    let expected = Refiner::default_for_item(genv, def_id.resolved_id())?.refine(&rust_fn_sig)?;

    let mut zipper = Zipper::new(genv, def_id);
    if let Err(err) = zipper.zip_poly_fn_sig(fn_sig, &expected) {
        zipper.emit_fn_sig_err(err, decl);
    }

    zipper.errors.to_result()?;

    Ok(zipper.holes.replace_holes(fn_sig))
}

pub(crate) fn variants(
    genv: GlobalEnv,
    variants: &[rty::PolyVariant],
    adt_def_id: MaybeExternId,
) -> QueryResult<Vec<rty::PolyVariant>> {
    let refiner = Refiner::default_for_item(genv, adt_def_id.resolved_id())?;
    let mut zipper = Zipper::new(genv, adt_def_id);
    // TODO check same number of variants
    for (i, variant) in variants.iter().enumerate() {
        let variant_idx = VariantIdx::from_usize(i);
        let expected = refiner.refine_variant_def(adt_def_id.resolved_id(), variant_idx)?;
        zipper.zip_variant(variant, &expected, variant_idx);
    }

    zipper.errors.to_result()?;

    Ok(variants
        .iter()
        .map(|v| zipper.holes.replace_holes(v))
        .collect())
}

struct Zipper<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    owner_id: MaybeExternId,
    locs: UnordMap<rty::Loc, rty::Ty>,
    holes: Holes,
    /// Number of binders we've entered in `a`
    a_binders: u32,
    /// Each element in the vector correspond to a binder in `b`. For some binders we map it to
    /// a corresponding binder in `a`. We assume that expressions filling holes will only contain
    /// variables pointing to some of these mapped binders.
    b_binder_to_a_binder: Vec<Option<u32>>,
    errors: Errors<'genv>,
}

#[derive(Default)]
struct Holes {
    sorts: UnordMap<rty::SortVid, rty::Sort>,
    subset_tys: UnordMap<rty::TyVid, rty::SubsetTy>,
    types: UnordMap<rty::TyVid, rty::Ty>,
    regions: UnordMap<rty::RegionVid, rty::Region>,
    consts: UnordMap<rty::ConstVid, rty::Const>,
}

impl TypeFolder for &Holes {
    fn fold_sort(&mut self, sort: &rty::Sort) -> rty::Sort {
        if let rty::Sort::Infer(vid) = sort {
            self.sorts
                .get(vid)
                .cloned()
                .unwrap_or_else(|| bug!("unfilled sort hole {vid:?}"))
        } else {
            sort.super_fold_with(self)
        }
    }

    fn fold_ty(&mut self, ty: &rty::Ty) -> rty::Ty {
        if let rty::TyKind::Infer(vid) = ty.kind() {
            self.types
                .get(vid)
                .cloned()
                .unwrap_or_else(|| bug!("unfilled type hole {vid:?}"))
        } else {
            ty.super_fold_with(self)
        }
    }

    fn fold_subset_ty(&mut self, constr: &rty::SubsetTy) -> rty::SubsetTy {
        if let rty::BaseTy::Infer(vid) = &constr.bty {
            self.subset_tys
                .get(vid)
                .cloned()
                .unwrap_or_else(|| bug!("unfilled type hole {vid:?}"))
        } else {
            constr.super_fold_with(self)
        }
    }

    fn fold_region(&mut self, r: &rty::Region) -> rty::Region {
        if let rty::Region::ReVar(vid) = r {
            self.regions
                .get(vid)
                .copied()
                .unwrap_or_else(|| bug!("unfilled region hole {vid:?}"))
        } else {
            *r
        }
    }

    fn fold_const(&mut self, ct: &rty::Const) -> rty::Const {
        if let rty::ConstKind::Infer(InferConst::Var(cid)) = ct.kind {
            self.consts
                .get(&cid)
                .cloned()
                .unwrap_or_else(|| bug!("unfilled const hole {cid:?}"))
        } else {
            ct.super_fold_with(self)
        }
    }
}

impl Holes {
    fn replace_holes<T: TypeFoldable>(&self, t: &T) -> T {
        let mut this = self;
        t.fold_with(&mut this)
    }
}

impl<'genv, 'tcx> Zipper<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, owner_id: MaybeExternId) -> Self {
        Self {
            genv,
            owner_id,
            locs: UnordMap::default(),
            holes: Default::default(),
            a_binders: 0,
            b_binder_to_a_binder: vec![],
            errors: Errors::new(genv.sess()),
        }
    }

    fn zip_poly_fn_sig(&mut self, a: &rty::PolyFnSig, b: &rty::PolyFnSig) -> Result<(), FnSigErr> {
        self.enter_binders(a, b, |this, a, b| this.zip_fn_sig(a, b))
    }

    fn zip_variant(&mut self, a: &rty::PolyVariant, b: &rty::PolyVariant, variant_idx: VariantIdx) {
        self.enter_binders(a, b, |this, a, b| {
            // The args are always `GenericArgs::identity_for_item` inside the `EarlyBinder`
            debug_assert_eq!(a.args, b.args);

            if a.fields.len() != b.fields.len() {
                this.errors.emit(errors::FieldCountMismatch::new(
                    this.genv,
                    a.fields.len(),
                    this.owner_id,
                    variant_idx,
                ));
                return;
            }
            for (i, (ty_a, ty_b)) in iter::zip(&a.fields, &b.fields).enumerate() {
                let field_idx = FieldIdx::from_usize(i);
                if this.zip_ty(ty_a, ty_b).is_err() {
                    this.errors.emit(errors::IncompatibleRefinement::field(
                        this.genv,
                        this.owner_id,
                        variant_idx,
                        field_idx,
                    ));
                }
            }
        });
    }

    fn zip_fn_sig(&mut self, a: &rty::FnSig, b: &rty::FnSig) -> Result<(), FnSigErr> {
        if a.inputs().len() != b.inputs().len() {
            Err(FnSigErr::ArgCountMismatch)?;
        }
        for (i, (ty_a, ty_b)) in iter::zip(a.inputs(), b.inputs()).enumerate() {
            self.zip_ty(ty_a, ty_b).map_err(|_| FnSigErr::FnInput(i))?;
        }
        self.enter_binders(&a.output, &b.output, |this, output_a, output_b| {
            this.zip_output(output_a, output_b)
        })
    }

    fn zip_output(&mut self, a: &rty::FnOutput, b: &rty::FnOutput) -> Result<(), FnSigErr> {
        self.zip_ty(&a.ret, &b.ret).map_err(FnSigErr::FnOutput)?;

        for (i, ensures) in a.ensures.iter().enumerate() {
            if let rty::Ensures::Type(path, ty_a) = ensures {
                let loc = path.to_loc().unwrap();
                let ty_b = self.locs.get(&loc).unwrap().shift_in_escaping(1);
                self.zip_ty(ty_a, &ty_b)
                    .map_err(|_| FnSigErr::Ensures { i, expected: ty_b })?;
            }
        }
        Ok(())
    }

    fn zip_ty(&mut self, a: &rty::Ty, b: &rty::Ty) -> Result<(), Mismatch> {
        match (a.kind(), b.kind()) {
            (rty::TyKind::Infer(vid), _) => {
                assert_ne!(vid.as_u32(), 0);
                let b = self.adjust_bvars(b);
                self.holes.types.insert(*vid, b);
                Ok(())
            }
            (rty::TyKind::Exists(ctor_a), _) => {
                self.enter_a_binder(ctor_a, |this, ty_a| this.zip_ty(ty_a, b))
            }
            (_, rty::TyKind::Exists(ctor_b)) => {
                self.enter_b_binder(ctor_b, |this, ty_b| this.zip_ty(a, ty_b))
            }
            (rty::TyKind::Constr(_, ty_a), _) => self.zip_ty(ty_a, b),
            (_, rty::TyKind::Constr(_, ty_b)) => self.zip_ty(a, ty_b),
            (rty::TyKind::Indexed(bty_a, _), rty::TyKind::Indexed(bty_b, _)) => {
                self.zip_bty(bty_a, bty_b)
            }
            (rty::TyKind::StrgRef(re_a, path, ty_a), rty::Ref!(re_b, ty_b, Mutability::Mut)) => {
                let loc = path.to_loc().unwrap();
                self.locs.insert(loc, ty_b.clone());

                self.zip_region(re_a, re_b);
                self.zip_ty(ty_a, ty_b)
            }
            (rty::TyKind::Param(pty_a), rty::TyKind::Param(pty_b)) => {
                assert_eq_or_incompatible(pty_a, pty_b)
            }
            (
                rty::TyKind::Ptr(_, _)
                | rty::TyKind::Discr(..)
                | rty::TyKind::Downcast(_, _, _, _, _)
                | rty::TyKind::Blocked(_)
                | rty::TyKind::Uninit,
                _,
            ) => {
                bug!("unexpected type {a:?}");
            }
            _ => Err(Mismatch::new(a, b)),
        }
    }

    fn zip_bty(&mut self, a: &rty::BaseTy, b: &rty::BaseTy) -> Result<(), Mismatch> {
        match (a, b) {
            (rty::BaseTy::Int(ity_a), rty::BaseTy::Int(ity_b)) => {
                assert_eq_or_incompatible(ity_a, ity_b)
            }
            (rty::BaseTy::Uint(uity_a), rty::BaseTy::Uint(uity_b)) => {
                assert_eq_or_incompatible(uity_a, uity_b)
            }
            (rty::BaseTy::Bool, rty::BaseTy::Bool) => Ok(()),
            (rty::BaseTy::Str, rty::BaseTy::Str) => Ok(()),
            (rty::BaseTy::Char, rty::BaseTy::Char) => Ok(()),
            (rty::BaseTy::Float(fty_a), rty::BaseTy::Float(fty_b)) => {
                assert_eq_or_incompatible(fty_a, fty_b)
            }
            (rty::BaseTy::Slice(ty_a), rty::BaseTy::Slice(ty_b)) => self.zip_ty(ty_a, ty_b),
            (rty::BaseTy::Adt(adt_def_a, args_a), rty::BaseTy::Adt(adt_def_b, args_b)) => {
                assert_eq_or_incompatible(adt_def_a.did(), adt_def_b.did())?;
                assert_eq_or_incompatible(args_a.len(), args_b.len())?;
                for (arg_a, arg_b) in iter::zip(args_a, args_b) {
                    self.zip_generic_arg(arg_a, arg_b)?;
                }
                Ok(())
            }
            (rty::BaseTy::RawPtr(ty_a, mutbl_a), rty::BaseTy::RawPtr(ty_b, mutbl_b)) => {
                assert_eq_or_incompatible(mutbl_a, mutbl_b)?;
                self.zip_ty(ty_a, ty_b)
            }
            (rty::BaseTy::Ref(re_a, ty_a, mutbl_a), rty::BaseTy::Ref(re_b, ty_b, mutbl_b)) => {
                assert_eq_or_incompatible(mutbl_a, mutbl_b)?;
                self.zip_region(re_a, re_b);
                self.zip_ty(ty_a, ty_b)
            }
            (rty::BaseTy::FnPtr(poly_sig_a), rty::BaseTy::FnPtr(poly_sig_b)) => {
                self.zip_poly_fn_sig(poly_sig_a, poly_sig_b)
                    .map_err(|_| Mismatch::new(poly_sig_a, poly_sig_b))
            }
            (rty::BaseTy::Tuple(tys_a), rty::BaseTy::Tuple(tys_b)) => {
                assert_eq_or_incompatible(tys_a.len(), tys_b.len())?;
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.zip_ty(ty_a, ty_b)?;
                }
                Ok(())
            }
            (rty::BaseTy::Alias(kind_a, aty_a), rty::BaseTy::Alias(kind_b, aty_b)) => {
                assert_eq_or_incompatible(kind_a, kind_b)?;
                assert_eq_or_incompatible(aty_a.def_id, aty_b.def_id)?;
                assert_eq_or_incompatible(aty_a.args.len(), aty_b.args.len())?;
                for (arg_a, arg_b) in iter::zip(&aty_a.args, &aty_b.args) {
                    self.zip_generic_arg(arg_a, arg_b)?;
                }
                Ok(())
            }
            (rty::BaseTy::Array(ty_a, len_a), rty::BaseTy::Array(ty_b, len_b)) => {
                self.zip_const(len_a, len_b)?;
                self.zip_ty(ty_a, ty_b)
            }
            (rty::BaseTy::Never, rty::BaseTy::Never) => Ok(()),
            (rty::BaseTy::Param(pty_a), rty::BaseTy::Param(pty_b)) => {
                assert_eq_or_incompatible(pty_a, pty_b)
            }
            (rty::BaseTy::Dynamic(preds_a, re_a), rty::BaseTy::Dynamic(preds_b, re_b)) => {
                assert_eq_or_incompatible(preds_a.len(), preds_b.len())?;
                for (pred_a, pred_b) in iter::zip(preds_a, preds_b) {
                    self.zip_poly_existential_pred(pred_a, pred_b)?;
                }
                self.zip_region(re_a, re_b);
                Ok(())
            }
            (rty::BaseTy::Foreign(def_id_a), rty::BaseTy::Foreign(def_id_b)) => {
                assert_eq_or_incompatible(def_id_a, def_id_b)
            }
            (rty::BaseTy::Closure(..) | rty::BaseTy::Coroutine(..), _) => {
                bug!("unexpected type `{a:?}`");
            }
            _ => Err(Mismatch::new(a, b)),
        }
    }

    fn zip_generic_arg(
        &mut self,
        a: &rty::GenericArg,
        b: &rty::GenericArg,
    ) -> Result<(), Mismatch> {
        match (a, b) {
            (rty::GenericArg::Ty(ty_a), rty::GenericArg::Ty(ty_b)) => self.zip_ty(ty_a, ty_b),
            (rty::GenericArg::Base(ctor_a), rty::GenericArg::Base(ctor_b)) => {
                self.zip_sorts(&ctor_a.sort(), &ctor_b.sort());
                self.enter_binders(ctor_a, ctor_b, |this, sty_a, sty_b| {
                    this.zip_subset_ty(sty_a, sty_b)
                })
            }
            (rty::GenericArg::Lifetime(re_a), rty::GenericArg::Lifetime(re_b)) => {
                self.zip_region(re_a, re_b);
                Ok(())
            }
            (rty::GenericArg::Const(ct_a), rty::GenericArg::Const(ct_b)) => {
                self.zip_const(ct_a, ct_b)
            }
            _ => Err(Mismatch::new(a, b)),
        }
    }

    fn zip_sorts(&mut self, a: &rty::Sort, b: &rty::Sort) {
        if let rty::Sort::Infer(vid) = a {
            assert_ne!(vid.as_u32(), 0);
            self.holes.sorts.insert(*vid, b.clone());
        }
    }

    fn zip_subset_ty(&mut self, a: &rty::SubsetTy, b: &rty::SubsetTy) -> Result<(), Mismatch> {
        if let rty::BaseTy::Infer(vid) = a.bty {
            assert_ne!(vid.as_u32(), 0);
            let b = self.adjust_bvars(b);
            self.holes.subset_tys.insert(vid, b);
            Ok(())
        } else {
            self.zip_bty(&a.bty, &b.bty)
        }
    }

    fn zip_const(&mut self, a: &rty::Const, b: &ty::Const) -> Result<(), Mismatch> {
        match (&a.kind, &b.kind) {
            (rty::ConstKind::Infer(ty::InferConst::Var(cid)), _) => {
                self.holes.consts.insert(*cid, b.clone());
                Ok(())
            }
            (rty::ConstKind::Param(param_const_a), ty::ConstKind::Param(param_const_b)) => {
                assert_eq_or_incompatible(param_const_a, param_const_b)
            }
            (rty::ConstKind::Value(ty_a, val_a), ty::ConstKind::Value(ty_b, val_b)) => {
                assert_eq_or_incompatible(ty_a, ty_b)?;
                assert_eq_or_incompatible(val_a, val_b)
            }
            (rty::ConstKind::Unevaluated(c1), ty::ConstKind::Unevaluated(c2)) => {
                assert_eq_or_incompatible(c1, c2)
            }
            _ => Err(Mismatch::new(a, b)),
        }
    }

    fn zip_region(&mut self, a: &rty::Region, b: &ty::Region) {
        if let rty::Region::ReVar(vid) = a {
            let re = self.adjust_bvars(b);
            self.holes.regions.insert(*vid, re);
        }
    }

    fn zip_poly_existential_pred(
        &mut self,
        a: &rty::Binder<rty::ExistentialPredicate>,
        b: &rty::Binder<rty::ExistentialPredicate>,
    ) -> Result<(), Mismatch> {
        self.enter_binders(a, b, |this, a, b| {
            match (a, b) {
                (
                    rty::ExistentialPredicate::Trait(trait_ref_a),
                    rty::ExistentialPredicate::Trait(trait_ref_b),
                ) => {
                    assert_eq_or_incompatible(trait_ref_a.def_id, trait_ref_b.def_id)?;
                    assert_eq_or_incompatible(trait_ref_a.args.len(), trait_ref_b.args.len())?;
                    for (arg_a, arg_b) in iter::zip(&trait_ref_a.args, &trait_ref_b.args) {
                        this.zip_generic_arg(arg_a, arg_b)?;
                    }
                    Ok(())
                }
                (
                    rty::ExistentialPredicate::Projection(projection_a),
                    rty::ExistentialPredicate::Projection(projection_b),
                ) => {
                    assert_eq_or_incompatible(projection_a.def_id, projection_b.def_id)?;
                    assert_eq_or_incompatible(projection_a.args.len(), projection_b.args.len())?;
                    for (arg_a, arg_b) in iter::zip(&projection_a.args, &projection_b.args) {
                        this.zip_generic_arg(arg_a, arg_b)?;
                    }
                    this.enter_binders(&projection_a.term, &projection_b.term, |this, a, b| {
                        this.zip_bty(&a.bty, &b.bty)
                    })
                }
                (
                    rty::ExistentialPredicate::AutoTrait(def_id_a),
                    rty::ExistentialPredicate::AutoTrait(def_id_b),
                ) => assert_eq_or_incompatible(def_id_a, def_id_b),
                _ => Err(Mismatch::new(a, b)),
            }
        })
    }

    /// Enter a binder in both `a` and `b` creating a mapping between the two.
    fn enter_binders<T, R>(
        &mut self,
        a: &rty::Binder<T>,
        b: &rty::Binder<T>,
        f: impl FnOnce(&mut Self, &T, &T) -> R,
    ) -> R {
        self.b_binder_to_a_binder.push(Some(self.a_binders));
        self.a_binders += 1;
        let r = f(self, a.skip_binder_ref(), b.skip_binder_ref());
        self.a_binders -= 1;
        self.b_binder_to_a_binder.pop();
        r
    }

    /// Enter a binder in `a` without a corresponding mapping in `b`
    fn enter_a_binder<T, R>(
        &mut self,
        t: &rty::Binder<T>,
        f: impl FnOnce(&mut Self, &T) -> R,
    ) -> R {
        self.a_binders += 1;
        let r = f(self, t.skip_binder_ref());
        self.a_binders -= 1;
        r
    }

    /// Enter a binder in `b` without a corresponding mapping in `a`
    fn enter_b_binder<T, R>(
        &mut self,
        t: &rty::Binder<T>,
        f: impl FnOnce(&mut Self, &T) -> R,
    ) -> R {
        self.b_binder_to_a_binder.push(None);
        let r = f(self, t.skip_binder_ref());
        self.b_binder_to_a_binder.pop();
        r
    }

    fn adjust_bvars<T: TypeFoldable + Clone + std::fmt::Debug>(&self, t: &T) -> T {
        struct Adjuster<'a, 'genv, 'tcx> {
            current_index: DebruijnIndex,
            zipper: &'a Zipper<'genv, 'tcx>,
        }

        impl Adjuster<'_, '_, '_> {
            fn adjust(&self, debruijn: DebruijnIndex) -> DebruijnIndex {
                let b_binders = self.zipper.b_binder_to_a_binder.len();
                let mapped_binder = self.zipper.b_binder_to_a_binder
                    [b_binders - debruijn.as_usize() - 1]
                    .unwrap_or_else(|| {
                        bug!("bound var without corresponding binder: `{debruijn:?}`")
                    });
                DebruijnIndex::from_u32(self.zipper.a_binders - mapped_binder - 1)
                    .shifted_in(self.current_index.as_u32())
            }
        }

        impl TypeFolder for Adjuster<'_, '_, '_> {
            fn enter_binder(&mut self, _: &rty::BoundVariableKinds) {
                self.current_index.shift_in(1);
            }

            fn exit_binder(&mut self) {
                self.current_index.shift_out(1);
            }

            fn fold_region(&mut self, re: &rty::Region) -> rty::Region {
                if let rty::ReBound(debruijn, br) = *re
                    && debruijn >= self.current_index
                {
                    rty::ReBound(self.adjust(debruijn), br)
                } else {
                    *re
                }
            }

            fn fold_expr(&mut self, expr: &rty::Expr) -> rty::Expr {
                if let rty::ExprKind::Var(rty::Var::Bound(debruijn, breft)) = expr.kind()
                    && *debruijn >= self.current_index
                {
                    rty::Expr::bvar(self.adjust(*debruijn), breft.var, breft.kind)
                } else {
                    expr.super_fold_with(self)
                }
            }
        }
        t.fold_with(&mut Adjuster { current_index: INNERMOST, zipper: self })
    }

    fn emit_fn_sig_err(&mut self, err: FnSigErr, decl: &fhir::FnDecl) {
        match err {
            FnSigErr::ArgCountMismatch => {
                self.errors.emit(errors::IncompatibleParamCount::new(
                    self.genv,
                    decl,
                    self.owner_id,
                ));
            }
            FnSigErr::FnInput(i) => {
                self.errors.emit(errors::IncompatibleRefinement::fn_input(
                    self.genv,
                    self.owner_id,
                    decl,
                    i,
                ));
            }
            FnSigErr::FnOutput(_) => {
                self.errors.emit(errors::IncompatibleRefinement::fn_output(
                    self.genv,
                    self.owner_id,
                    decl,
                ));
            }
            FnSigErr::Ensures { i, expected } => {
                self.errors.emit(errors::IncompatibleRefinement::ensures(
                    self.genv,
                    self.owner_id,
                    decl,
                    &expected,
                    i,
                ));
            }
        }
    }
}

fn assert_eq_or_incompatible<T: Eq + fmt::Debug>(a: T, b: T) -> Result<(), Mismatch> {
    if a != b {
        return Err(Mismatch::new(a, b));
    }
    Ok(())
}

#[expect(dead_code, reason = "we use the the String for debugging")]
struct Mismatch(String);

impl Mismatch {
    fn new<T: fmt::Debug>(a: T, b: T) -> Self {
        Self(format!("{a:?} != {b:?}"))
    }
}

enum FnSigErr {
    ArgCountMismatch,
    FnInput(usize),
    #[expect(dead_code, reason = "we use the struct for debugging")]
    FnOutput(Mismatch),
    Ensures {
        i: usize,
        expected: rty::Ty,
    },
}

mod errors {
    use flux_common::span_bug;
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_middle::{def_id::MaybeExternId, fhir, global_env::GlobalEnv, rty};
    use flux_rustc_bridge::{
        ToRustc,
        ty::{FieldIdx, VariantIdx},
    };
    use rustc_span::{DUMMY_SP, Span};

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incompatible_refinement, code = E0999)]
    #[note]
    pub(super) struct IncompatibleRefinement<'tcx> {
        #[primary_span]
        #[label]
        span: Span,
        #[label(fhir_analysis_expected_label)]
        expected_span: Option<Span>,
        expected_ty: rustc_middle::ty::Ty<'tcx>,
        def_descr: &'static str,
    }

    impl<'tcx> IncompatibleRefinement<'tcx> {
        pub(super) fn type_alias(
            genv: GlobalEnv<'_, 'tcx>,
            def_id: MaybeExternId,
            type_alias: &fhir::TyAlias,
        ) -> Self {
            let tcx = genv.tcx();
            Self {
                span: type_alias.ty.span,
                def_descr: tcx.def_descr(def_id.resolved_id()),
                expected_span: Some(tcx.def_span(def_id)),
                expected_ty: tcx.type_of(def_id).skip_binder(),
            }
        }

        pub(super) fn fn_input(
            genv: GlobalEnv<'_, 'tcx>,
            fn_id: MaybeExternId,
            decl: &fhir::FnDecl,
            pos: usize,
        ) -> Self {
            let expected_span = match fn_id {
                MaybeExternId::Local(local_id) => {
                    genv.tcx()
                        .hir_node_by_def_id(local_id)
                        .fn_decl()
                        .and_then(|fn_decl| fn_decl.inputs.get(pos))
                        .map(|input| input.span)
                }
                MaybeExternId::Extern(_, extern_id) => Some(genv.tcx().def_span(extern_id)),
            };

            let expected_ty = genv
                .tcx()
                .fn_sig(fn_id.resolved_id())
                .skip_binder()
                .inputs()
                .map_bound(|inputs| inputs[pos])
                .skip_binder();

            Self {
                span: decl.inputs[pos].span,
                def_descr: genv.tcx().def_descr(fn_id.resolved_id()),
                expected_span,
                expected_ty,
            }
        }

        pub(super) fn fn_output(
            genv: GlobalEnv<'_, 'tcx>,
            fn_id: MaybeExternId,
            decl: &fhir::FnDecl,
        ) -> Self {
            let expected_span = match fn_id {
                MaybeExternId::Local(local_id) => {
                    genv.tcx()
                        .hir_node_by_def_id(local_id)
                        .fn_decl()
                        .map(|fn_decl| fn_decl.output.span())
                }
                MaybeExternId::Extern(_, extern_id) => Some(genv.tcx().def_span(extern_id)),
            };

            let expected_ty = genv
                .tcx()
                .fn_sig(fn_id.resolved_id())
                .skip_binder()
                .output()
                .skip_binder();
            let spec_span = decl.output.ret.span;
            Self {
                span: spec_span,
                def_descr: genv.tcx().def_descr(fn_id.resolved_id()),
                expected_span,
                expected_ty,
            }
        }

        pub(super) fn ensures(
            genv: GlobalEnv<'_, 'tcx>,
            fn_id: MaybeExternId,
            decl: &fhir::FnDecl,
            expected: &rty::Ty,
            i: usize,
        ) -> Self {
            let fhir::Ensures::Type(_, ty) = &decl.output.ensures[i] else {
                span_bug!(decl.span, "expected `fhir::Ensures::Type`");
            };
            let tcx = genv.tcx();
            Self {
                span: ty.span,
                def_descr: tcx.def_descr(fn_id.resolved_id()),
                expected_span: None,
                expected_ty: expected.to_rustc(tcx),
            }
        }

        pub(super) fn field(
            genv: GlobalEnv<'_, 'tcx>,
            adt_id: MaybeExternId,
            variant_idx: VariantIdx,
            field_idx: FieldIdx,
        ) -> Self {
            let tcx = genv.tcx();
            let adt_def = tcx.adt_def(adt_id);
            let field_def = &adt_def.variant(variant_idx).fields[field_idx];

            let item = genv.fhir_expect_item(adt_id.local_id()).unwrap();
            let span = match &item.kind {
                fhir::ItemKind::Enum(enum_def) => {
                    enum_def.variants[variant_idx.as_usize()].fields[field_idx.as_usize()]
                        .ty
                        .span
                }
                fhir::ItemKind::Struct(struct_def)
                    if let fhir::StructKind::Transparent { fields } = &struct_def.kind =>
                {
                    fields[field_idx.as_usize()].ty.span
                }
                _ => DUMMY_SP,
            };

            Self {
                span,
                def_descr: tcx.def_descr(field_def.did),
                expected_span: Some(tcx.def_span(field_def.did)),
                expected_ty: tcx.type_of(field_def.did).skip_binder(),
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incompatible_param_count, code = E0999)]
    pub(super) struct IncompatibleParamCount {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
        expected: usize,
        def_descr: &'static str,
    }

    impl IncompatibleParamCount {
        pub(super) fn new(genv: GlobalEnv, decl: &fhir::FnDecl, def_id: MaybeExternId) -> Self {
            let def_descr = genv.tcx().def_descr(def_id.resolved_id());

            let span = if !decl.inputs.is_empty() {
                decl.inputs[decl.inputs.len() - 1]
                    .span
                    .with_lo(decl.inputs[0].span.lo())
            } else {
                decl.span
            };

            let expected_span = if let Some(local_id) = def_id.as_local()
                && let expected_decl = genv.tcx().hir_node_by_def_id(local_id).fn_decl().unwrap()
                && !expected_decl.inputs.is_empty()
            {
                expected_decl.inputs[expected_decl.inputs.len() - 1]
                    .span
                    .with_lo(expected_decl.inputs[0].span.lo())
            } else {
                genv.tcx().def_span(def_id)
            };

            let expected = genv
                .tcx()
                .fn_sig(def_id)
                .skip_binder()
                .skip_binder()
                .inputs()
                .len();

            Self { span, found: decl.inputs.len(), expected_span, expected, def_descr }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_field_count_mismatch, code = E0999)]
    pub(super) struct FieldCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        fields: usize,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
        expected_fields: usize,
    }

    impl FieldCountMismatch {
        pub(super) fn new(
            genv: GlobalEnv,
            found: usize,
            adt_def_id: MaybeExternId,
            variant_idx: VariantIdx,
        ) -> Self {
            let adt_def = genv.tcx().adt_def(adt_def_id);
            let expected_variant = adt_def.variant(variant_idx);

            // Get the span of the variant if this is an enum. Structs cannot have produce a field
            // count mismatch.
            let span = if let Ok(fhir::Node::Item(item)) = genv.fhir_node(adt_def_id.local_id())
                && let fhir::ItemKind::Enum(enum_def) = &item.kind
                && let Some(variant) = enum_def.variants.get(variant_idx.as_usize())
            {
                variant.span
            } else {
                DUMMY_SP
            };

            Self {
                span,
                fields: found,
                expected_span: genv.tcx().def_span(expected_variant.def_id),
                expected_fields: expected_variant.fields.len(),
            }
        }
    }
}
