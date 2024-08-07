use std::iter;

use flux_common::bug;
use flux_middle::{
    fhir::{self, FhirId},
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::{
        self,
        fold::{BottomUpFolder, TypeFoldable},
        refining::Refiner,
    },
    rustc::{
        lowering::{self, UnsupportedReason},
        ty,
    },
};
use rustc_ast::Mutability;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::Diagnostic;
use rustc_hir::{self as hir, def_id::LocalDefId};
use rustc_span::ErrorGuaranteed;
use rustc_type_ir::{DebruijnIndex, InferConst, INNERMOST};

pub(crate) fn fn_sig(
    genv: GlobalEnv,
    decl: &fhir::FnDecl,
    fn_sig: &rty::PolyFnSig,
    def_id: LocalDefId,
) -> QueryResult<rty::PolyFnSig> {
    // FIXME(nilehmann) we should call `genv.lower_fn_sig`, but that function normalizes the
    // signature to evaluate constants before lowering it. This also normalizes projections which
    // we don't want here because we need the signatures to match syntactically.
    // FIXME(nilehmann) we should check against the extern signature if this is an extern spec.
    // Unfortunately, doing this makes `neg/vec01.rs` fail because checking against the real
    // signature of `<Vec as Index<usize>>::index` requires deep normalization.
    let rust_fn_sig = lowering::lower_fn_sig(genv.tcx(), genv.tcx().fn_sig(def_id).skip_binder())
        .map_err(UnsupportedReason::into_err)
        .map_err(|err| QueryErr::unsupported(def_id.to_def_id(), err))?;
    let generics = genv.generics_of(def_id)?;
    let expected = Refiner::default(genv, &generics).refine_poly_fn_sig(&rust_fn_sig)?;

    let mut zipper = TyZipper::new(genv, def_id);
    zipper.enter_binders(fn_sig, &expected, |zipper, fn_sig, expected| {
        zipper.zip_fn_sig(decl, fn_sig, expected)
    })?;

    // let mut zipper = Zipper::new(genv, def_id)?;

    // zipper.enter_binders(fn_sig, rust_fn_sig, |zipper, fn_sig, rust_fn_sig| {
    //     zipper.zip_fn_sig(fn_sig, rust_fn_sig)
    // })?;

    Ok(zipper.replace_holes(fn_sig))
}

pub(crate) fn variants(
    genv: GlobalEnv,
    variants: &[rty::PolyVariant],
    adt_def_id: LocalDefId,
) -> QueryResult<Vec<rty::PolyVariant>> {
    let adt_def = genv.adt_def(adt_def_id)?;
    let mut zipper = Zipper::new(genv, adt_def_id)?;
    let def_id = genv.resolve_maybe_extern_id(adt_def_id.to_def_id());
    let adt_ty = genv.lower_type_of(def_id)?.skip_binder();
    for (variant, variant_def) in iter::zip(variants, adt_def.variants()) {
        zipper.zip_variant(variant, variant_def, &adt_ty)?;
    }

    Ok(variants.iter().map(|v| zipper.replace_holes(v)).collect())
}

struct Zipper<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    generics: rty::Generics,
    locs: UnordMap<rty::Loc, ty::Ty>,
    type_holes: UnordMap<FhirId, rty::Ty>,
    region_holes: UnordMap<rty::RegionVid, rty::Region>,
    const_holes: UnordMap<rty::ConstVid, rty::Const>,
    rty_index: DebruijnIndex,
    ty_index: DebruijnIndex,
}

impl<'genv, 'tcx> Zipper<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, owner: LocalDefId) -> QueryResult<Self> {
        Ok(Self {
            genv,
            generics: genv.generics_of(owner)?,
            locs: UnordMap::default(),
            type_holes: Default::default(),
            region_holes: Default::default(),
            const_holes: Default::default(),
            rty_index: INNERMOST,
            ty_index: INNERMOST,
        })
    }

    fn zip_variant(
        &mut self,
        a: &rty::PolyVariant,
        b: &ty::VariantDef,
        adt_ty: &ty::Ty,
    ) -> QueryResult {
        self.enter_rty_binder(a, |this, a| {
            debug_assert_eq!(a.fields.len(), b.fields.len());
            for (ty_a, field_def_b) in iter::zip(&a.fields, &b.fields) {
                let ty_b = this.genv.lower_type_of(field_def_b.did)?.skip_binder();
                this.zip_ty(ty_a, &ty_b)?;
            }
            this.zip_ty(&a.ret(), adt_ty)?;
            Ok(())
        })
    }

    fn zip_fn_sig(&mut self, a: &rty::FnSig, b: &ty::FnSig) -> QueryResult {
        debug_assert_eq!(a.inputs().len(), b.inputs().len());
        for (a, b) in iter::zip(a.inputs(), b.inputs()) {
            self.zip_ty(a, b)?;
        }
        self.enter_rty_binder(a.output(), |this, output| {
            this.zip_ty(&output.ret, b.output())?;
            for ensures in &output.ensures {
                if let rty::Ensures::Type(path, ty_a) = ensures {
                    let loc = path.to_loc().unwrap();
                    let ty_b = this.locs.get(&loc).unwrap().clone();
                    this.zip_ty(ty_a, &ty_b)?;
                }
            }
            Ok(())
        })
    }

    fn zip_ty(&mut self, a: &rty::Ty, b: &ty::Ty) -> QueryResult {
        match (a.kind(), b.kind()) {
            (rty::TyKind::Hole(fhir_id), _) => {
                let ty = self.genv.refine_default(&self.generics, b)?;
                let ty = self.adjust_binders(&ty);
                self.type_holes.insert(*fhir_id, ty);
            }
            (rty::TyKind::Indexed(bty, _), _) => {
                self.zip_bty(bty, b)?;
            }
            (rty::TyKind::Exists(ctor), _) => {
                self.enter_rty_binder(ctor, |this, ty| this.zip_ty(ty, b))?;
            }
            (rty::TyKind::Constr(_, ty), _) => self.zip_ty(ty, b)?,
            (
                rty::TyKind::StrgRef(re_a, path, ty_a),
                ty::TyKind::Ref(re_b, ty_b, Mutability::Mut),
            ) => {
                let loc = path.to_loc().unwrap();
                self.locs.insert(loc, ty_b.clone());

                self.zip_region(re_a, re_b);
                self.zip_ty(ty_a, ty_b)?;
            }
            (rty::TyKind::Param(pty_a), ty::TyKind::Param(pty_b)) => {
                debug_assert_eq!(pty_a, pty_b);
            }
            (rty::TyKind::Alias(kind_a, aty_a), ty::TyKind::Alias(kind_b, aty_b)) => {
                debug_assert_eq!(kind_a, kind_b);
                debug_assert_eq!(aty_a.def_id, aty_b.def_id);
                debug_assert_eq!(aty_a.args.len(), aty_b.args.len());
                for (arg_a, arg_b) in iter::zip(&aty_a.args, &aty_b.args) {
                    self.zip_generic_arg(arg_a, arg_b)?;
                }
            }
            (
                rty::TyKind::Ptr(_, _)
                | rty::TyKind::Discr(_, _)
                | rty::TyKind::Downcast(_, _, _, _, _)
                | rty::TyKind::Blocked(_)
                | rty::TyKind::Uninit,
                _,
            ) => {
                bug!("unexpected type {a:?}");
            }
            _ => {
                bug!("incompatible types `{a:?}` `{b:?}`");
            }
        }
        Ok(())
    }

    fn zip_bty(&mut self, a: &rty::BaseTy, b: &ty::Ty) -> QueryResult {
        match (a, b.kind()) {
            (rty::BaseTy::Int(ity_a), ty::TyKind::Int(ity_b)) => {
                debug_assert_eq!(ity_a, ity_b);
            }
            (rty::BaseTy::Uint(uity_a), ty::TyKind::Uint(uity_b)) => {
                debug_assert_eq!(uity_a, uity_b);
            }
            (rty::BaseTy::Bool, ty::TyKind::Bool) => {}
            (rty::BaseTy::Str, ty::TyKind::Str) => {}
            (rty::BaseTy::Char, ty::TyKind::Char) => {}
            (rty::BaseTy::Float(fty_a), ty::TyKind::Float(fty_b)) => {
                debug_assert_eq!(fty_a, fty_b);
            }
            (rty::BaseTy::Slice(ty_a), ty::TyKind::Slice(ty_b)) => {
                self.zip_ty(ty_a, ty_b)?;
            }
            (rty::BaseTy::Adt(adt_def_a, args_a), ty::TyKind::Adt(adt_def_b, args_b)) => {
                debug_assert_eq!(adt_def_a.did(), adt_def_b.did());
                debug_assert_eq!(args_a.len(), args_b.len());
                for (arg_a, arg_b) in iter::zip(args_a, args_b) {
                    self.zip_generic_arg(arg_a, arg_b)?;
                }
            }
            (rty::BaseTy::RawPtr(ty_a, mutbl_a), ty::TyKind::RawPtr(ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.zip_ty(ty_a, ty_b)?;
            }
            (rty::BaseTy::Ref(re_a, ty_a, mutbl_a), ty::TyKind::Ref(re_b, ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.zip_ty(ty_a, ty_b)?;
                self.zip_region(re_a, re_b);
            }
            (rty::BaseTy::Tuple(tys_a), ty::TyKind::Tuple(tys_b)) => {
                debug_assert_eq!(tys_a.len(), tys_b.len());
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.zip_ty(ty_a, ty_b)?;
                }
            }
            (rty::BaseTy::Array(ty_a, len_a), ty::TyKind::Array(ty_b, len_b)) => {
                self.zip_const(len_a, len_b)?;
                self.zip_ty(ty_a, ty_b)?;
            }
            (rty::BaseTy::Never, ty::TyKind::Never) => {}
            (rty::BaseTy::Param(pty_a), ty::TyKind::Param(pty_b)) => {
                debug_assert_eq!(pty_a, pty_b);
            }
            (
                rty::BaseTy::Dynamic(poly_trait_refs, re_a),
                ty::TyKind::Dynamic(poly_trait_refs_b, re_b),
            ) => {
                self.zip_region(re_a, re_b);
                debug_assert_eq!(poly_trait_refs.len(), poly_trait_refs_b.len());
            }
            (rty::BaseTy::Closure(..), _) => {
                bug!("unexpected closure {a:?}");
            }
            (rty::BaseTy::Coroutine(..), _) => {
                bug!("unexpected coroutine {a:?}");
            }
            _ => {
                bug!("incompatible types `{a:?}` `{b:?}`");
            }
        }
        Ok(())
    }

    fn zip_generic_arg(&mut self, a: &rty::GenericArg, b: &ty::GenericArg) -> QueryResult {
        match (a, b) {
            (rty::GenericArg::Ty(ty_a), ty::GenericArg::Ty(ty_b)) => self.zip_ty(ty_a, ty_b)?,
            (rty::GenericArg::Base(ctor_a), ty::GenericArg::Ty(ty_b)) => {
                self.enter_rty_binder(ctor_a, |this, sty_a| this.zip_bty(&sty_a.bty, ty_b))?;
            }
            (rty::GenericArg::Lifetime(re_a), ty::GenericArg::Lifetime(re_b)) => {
                self.zip_region(re_a, re_b);
            }
            (rty::GenericArg::Const(ct_a), ty::GenericArg::Const(ct_b)) => {
                self.zip_const(ct_a, ct_b)?;
            }
            _ => {
                bug!("incompatible generic args `{a:?}` `{b:?}`");
            }
        }
        Ok(())
    }

    fn zip_const(&mut self, a: &rty::Const, b: &ty::Const) -> QueryResult {
        match (&a.kind, &b.kind) {
            (rty::ConstKind::Infer(ty::InferConst::Var(cid)), _) => {
                self.const_holes.insert(*cid, b.clone());
            }
            (rty::ConstKind::Param(param_const_a), ty::ConstKind::Param(param_const_b)) => {
                debug_assert_eq!(param_const_a, param_const_b)
            }
            (rty::ConstKind::Value(ty_a, val_a), ty::ConstKind::Value(ty_b, val_b)) => {
                debug_assert_eq!(ty_a, ty_b);
                debug_assert_eq!(val_a, val_b)
            }
            _ => bug!("incompatible consts"),
        }
        Ok(())
    }

    fn zip_region(&mut self, a: &rty::Region, b: &ty::Region) {
        if let rty::Region::ReVar(vid) = a {
            let re = self.adjust_binders(b);
            self.region_holes.insert(*vid, re);
        }
    }

    fn adjust_binders<T: TypeFoldable>(&self, t: &T) -> T {
        t.shift_in_escaping(self.rty_index.as_u32() - self.ty_index.as_u32())
    }

    fn enter_binders<A, B, R>(
        &mut self,
        a: &rty::Binder<A>,
        b: ty::Binder<B>,
        f: impl FnOnce(&mut Self, &A, &B) -> R,
    ) -> R {
        self.rty_index.shift_in(1);
        self.ty_index.shift_in(1);
        let r = f(self, a.as_ref().skip_binder(), b.as_ref().skip_binder());
        self.rty_index.shift_out(1);
        self.ty_index.shift_out(1);
        r
    }

    fn enter_rty_binder<T, R>(
        &mut self,
        t: &rty::Binder<T>,
        f: impl FnOnce(&mut Self, &T) -> R,
    ) -> R {
        self.rty_index.shift_in(1);
        let r = f(self, t.as_ref().skip_binder());
        self.rty_index.shift_out(1);
        r
    }

    fn replace_holes<T: TypeFoldable>(&self, t: &T) -> T {
        t.fold_with(&mut BottomUpFolder {
            ty_op: |ty| {
                if let rty::TyKind::Hole(fhir_id) = ty.kind() {
                    self.type_holes
                        .get(fhir_id)
                        .cloned()
                        .unwrap_or_else(|| bug!("unfilled type hole {fhir_id:?}"))
                } else {
                    ty
                }
            },
            lt_op: |r| {
                if let rty::Region::ReVar(vid) = r {
                    self.region_holes
                        .get(&vid)
                        .copied()
                        .unwrap_or_else(|| bug!("unfilled region hole {vid:?}"))
                } else {
                    r
                }
            },
            ct_op: |c| {
                if let rty::ConstKind::Infer(InferConst::Var(cid)) = c.kind {
                    self.const_holes
                        .get(&cid)
                        .cloned()
                        .unwrap_or_else(|| bug!("unfilled const hole {cid:?}"))
                } else {
                    c
                }
            },
        })
    }
}

struct TyZipper<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    owner_id: LocalDefId,
    locs: UnordMap<rty::Loc, rty::Ty>,
    type_holes: UnordMap<FhirId, rty::Ty>,
    region_holes: UnordMap<rty::RegionVid, rty::Region>,
    const_holes: UnordMap<rty::ConstVid, rty::Const>,
    a_index: DebruijnIndex,
    b_index: DebruijnIndex,
}

impl<'genv, 'tcx> TyZipper<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, owner_id: LocalDefId) -> Self {
        Self {
            genv,
            owner_id,
            locs: UnordMap::default(),
            type_holes: Default::default(),
            region_holes: Default::default(),
            const_holes: Default::default(),
            a_index: INNERMOST,
            b_index: INNERMOST,
        }
    }

    fn zip_fn_sig(
        &mut self,
        decl: &fhir::FnDecl,
        a: &rty::FnSig,
        b: &rty::FnSig,
    ) -> Result<(), ErrorGuaranteed> {
        if a.inputs().len() != b.inputs().len() {
            Err(self.emit(errors::IncompatiblParamCount::new(self.genv, decl, self.owner_id)))?;
        }
        for (i, (ty_a, ty_b)) in iter::zip(a.inputs(), b.inputs()).enumerate() {
            self.zip_input(decl, i, ty_a, ty_b)?;
        }
        self.enter_binders(a.output(), b.output(), |this, output_a, output_b| {
            this.zip_output(decl, output_a, output_b)
        })
    }

    fn zip_input(
        &mut self,
        decl: &fhir::FnDecl,
        pos: usize,
        a: &rty::Ty,
        b: &rty::Ty,
    ) -> Result<(), ErrorGuaranteed> {
        match self.zip_ty(a, b) {
            Ok(_) => Ok(()),
            Err(err) => {
                let rust_ty = self.expect_fn_decl().inputs[pos];
                let spec_span = decl.inputs[pos].span;
                Err(self.emit(errors::IncompatibleRefinement {
                    span: spec_span,
                    def_descr: self.genv.tcx().def_descr(self.owner_id.to_def_id()),
                    expected_span: rust_ty.span,
                    expected_ty: rustc_hir_pretty::ty_to_string(&self.genv.tcx(), &rust_ty),
                }))
            }
        }
    }

    fn expect_fn_decl(&self) -> &'tcx hir::FnDecl<'tcx> {
        self.genv
            .tcx()
            .hir_node_by_def_id(self.owner_id)
            .fn_decl()
            .unwrap()
    }

    fn zip_output(
        &mut self,
        decl: &fhir::FnDecl,
        a: &rty::FnOutput,
        b: &rty::FnOutput,
    ) -> Result<(), ErrorGuaranteed> {
        if let Err(err) = self.zip_ty(&a.ret, &b.ret) {
            let expected_output = self.expect_fn_decl().output;
            let expected_ty = match expected_output {
                rustc_hir::FnRetTy::DefaultReturn(_) => "()".to_string(),
                rustc_hir::FnRetTy::Return(ty) => {
                    rustc_hir_pretty::ty_to_string(&self.genv.tcx(), ty)
                }
            };
            let spec_span = decl.output.ret.span;
            Err(self.emit(errors::IncompatibleRefinement {
                span: spec_span,
                def_descr: self.genv.tcx().def_descr(self.owner_id.to_def_id()),
                expected_span: expected_output.span(),
                expected_ty,
            }))?;
        }
        for ensures in &a.ensures {
            if let rty::Ensures::Type(path, ty_a) = ensures {
                let loc = path.to_loc().unwrap();
                let ty_b = self.locs.get(&loc).unwrap().clone();
                self.zip_ty(ty_a, &ty_b);
            }
        }
        Ok(())
    }

    fn zip_ty(&mut self, a: &rty::Ty, b: &rty::Ty) -> Result<(), Error> {
        match (a.kind(), b.kind()) {
            (rty::TyKind::Hole(fhir_id), _) => {
                let b = self.adjust_binders(b);
                self.type_holes.insert(*fhir_id, b);
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
            (rty::TyKind::Alias(kind_a, aty_a), rty::TyKind::Alias(kind_b, aty_b)) => {
                assert_eq_or_incompatible(kind_a, kind_b)?;
                assert_eq_or_incompatible(aty_a.def_id, aty_b.def_id)?;
                assert_eq_or_incompatible(aty_a.args.len(), aty_b.args.len())?;
                for (arg_a, arg_b) in iter::zip(&aty_a.args, &aty_b.args) {
                    self.zip_generic_arg(arg_a, arg_b)?;
                }
                Ok(())
            }
            (
                rty::TyKind::Ptr(_, _)
                | rty::TyKind::Discr(_, _)
                | rty::TyKind::Downcast(_, _, _, _, _)
                | rty::TyKind::Blocked(_)
                | rty::TyKind::Uninit,
                _,
            ) => {
                bug!("unexpected type {a:?}");
            }
            _ => Err(Error::Incompatible),
        }
    }

    fn zip_bty(&mut self, a: &rty::BaseTy, b: &rty::BaseTy) -> Result<(), Error> {
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
            (rty::BaseTy::Tuple(tys_a), rty::BaseTy::Tuple(tys_b)) => {
                assert_eq_or_incompatible(tys_a.len(), tys_b.len())?;
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.zip_ty(ty_a, ty_b)?;
                }
                Ok(())
            }
            (rty::BaseTy::Array(ty_a, len_a), rty::BaseTy::Array(ty_b, len_b)) => {
                assert_eq_or_incompatible(len_a, len_b)?;
                self.zip_ty(ty_a, ty_b)
            }
            (rty::BaseTy::Never, rty::BaseTy::Never) => Ok(()),
            (rty::BaseTy::Param(pty_a), rty::BaseTy::Param(pty_b)) => {
                assert_eq_or_incompatible(pty_a, pty_b)
            }
            (rty::BaseTy::Closure(..) | rty::BaseTy::Coroutine(..), _) => {
                bug!("unexpected type `{a:?}`");
            }
            _ => Err(Error::Incompatible),
        }
    }

    fn zip_generic_arg(&mut self, a: &rty::GenericArg, b: &rty::GenericArg) -> Result<(), Error> {
        match (a, b) {
            (rty::GenericArg::Ty(ty_a), rty::GenericArg::Ty(ty_b)) => self.zip_ty(ty_a, ty_b),
            (rty::GenericArg::Base(ctor_a), rty::GenericArg::Base(ctor_b)) => {
                self.enter_binders(ctor_a, ctor_b, |this, sty_a, sty_b| {
                    this.zip_bty(&sty_a.bty, &sty_b.bty)
                })
            }
            (rty::GenericArg::Lifetime(re_a), rty::GenericArg::Lifetime(re_b)) => {
                self.zip_region(re_a, re_b);
                Ok(())
            }
            (rty::GenericArg::Const(ct_a), rty::GenericArg::Const(ct_b)) => {
                assert_eq_or_incompatible(ct_a, ct_b)
            }
            _ => Err(Error::Incompatible),
        }
    }

    fn zip_region(&mut self, a: &rty::Region, b: &ty::Region) {
        if let rty::Region::ReVar(vid) = a {
            let re = self.adjust_binders(b);
            self.region_holes.insert(*vid, re);
        }
    }

    fn enter_binders<T, R>(
        &mut self,
        a: &rty::Binder<T>,
        b: &rty::Binder<T>,
        f: impl FnOnce(&mut Self, &T, &T) -> R,
    ) -> R {
        self.enter_a_binder(a, |this, a| this.enter_b_binder(b, |this, b| f(this, a, b)))
    }

    fn enter_a_binder<T, R>(
        &mut self,
        t: &rty::Binder<T>,
        f: impl FnOnce(&mut Self, &T) -> R,
    ) -> R {
        self.a_index.shift_in(1);
        let r = f(self, t.as_ref().skip_binder());
        self.a_index.shift_out(1);
        r
    }

    fn enter_b_binder<T, R>(
        &mut self,
        t: &rty::Binder<T>,
        f: impl FnOnce(&mut Self, &T) -> R,
    ) -> R {
        self.b_index.shift_in(1);
        let r = f(self, t.as_ref().skip_binder());
        self.b_index.shift_out(1);
        r
    }

    fn adjust_binders<T: TypeFoldable>(&self, t: &T) -> T {
        if self.a_index >= self.b_index {
            t.shift_in_escaping(self.a_index.as_u32() - self.b_index.as_u32())
        } else {
            t.shift_out_escaping(self.b_index.as_u32() - self.a_index.as_u32())
        }
    }

    fn replace_holes<T: TypeFoldable>(&self, t: &T) -> T {
        t.fold_with(&mut BottomUpFolder {
            ty_op: |ty| {
                if let rty::TyKind::Hole(fhir_id) = ty.kind() {
                    self.type_holes
                        .get(fhir_id)
                        .cloned()
                        .unwrap_or_else(|| bug!("unfilled type hole {fhir_id:?}"))
                } else {
                    ty
                }
            },
            lt_op: |r| {
                if let rty::Region::ReVar(vid) = r {
                    self.region_holes
                        .get(&vid)
                        .copied()
                        .unwrap_or_else(|| bug!("unfilled region hole {vid:?}"))
                } else {
                    r
                }
            },
            ct_op: |c| {
                if let rty::ConstKind::Infer(InferConst::Var(cid)) = c.kind {
                    self.const_holes
                        .get(&cid)
                        .cloned()
                        .unwrap_or_else(|| bug!("unfilled const hole {cid:?}"))
                } else {
                    c
                }
            },
        })
    }

    fn emit<'b>(&'b self, err: impl Diagnostic<'b>) -> ErrorGuaranteed {
        self.genv.sess().emit_err(err)
    }
}

fn assert_eq_or_incompatible<T: Eq>(a: T, b: T) -> Result<(), Error> {
    if a != b {
        return Err(Error::Incompatible);
    }
    Ok(())
}

enum Error {
    Incompatible,
    GenericArgCount,
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_middle::{fhir, global_env::GlobalEnv};
    use rustc_hir::{self as hir, def_id::LocalDefId};
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incompatible_refinement, code = E0999)]
    pub(super) struct IncompatibleRefinement {
        #[primary_span]
        #[label]
        pub(super) span: Span,
        #[label(fhir_analysis_expected_label)]
        pub(super) expected_span: Span,
        pub(super) expected_ty: String,
        pub(super) def_descr: &'static str,
        // #[note]
        // pub(super) has_note: bool,
        // pub(super) note: String,
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incompatible_param_count, code = E0999)]
    pub(super) struct IncompatiblParamCount {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
        expected: usize,
        def_descr: &'static str,
    }

    impl IncompatiblParamCount {
        pub(super) fn new(genv: GlobalEnv, decl: &fhir::FnDecl, def_id: LocalDefId) -> Self {
            let def_descr = genv.tcx().def_descr(def_id.to_def_id());

            let span = if decl.inputs.len() > 0 {
                decl.inputs[decl.inputs.len() - 1]
                    .span
                    .with_lo(decl.inputs[0].span.lo())
            } else {
                decl.span
            };

            let expected_decl = genv.tcx().hir_node_by_def_id(def_id).fn_decl().unwrap();
            let expected_span = if expected_decl.inputs.len() > 0 {
                expected_decl.inputs[expected_decl.inputs.len() - 1]
                    .span
                    .with_lo(expected_decl.inputs[0].span.lo())
            } else {
                genv.tcx().def_span(def_id)
            };

            Self {
                span,
                found: decl.inputs.len(),
                expected_span,
                expected: expected_decl.inputs.len(),
                def_descr,
            }
        }
    }
}

// trait Trait {
//     fn method(x: Vec<(i32, i32)>, y: i32);
// }

// impl Trait for i32 {
//     fn method(x: Vec<(i32, i64)>) {
//         todo!()
//     }
// }

// struct S<T> {
//     f: T,
// }

// fn foo(x: S) {}
