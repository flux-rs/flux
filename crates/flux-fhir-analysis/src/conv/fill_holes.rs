use std::iter;

use flux_common::bug;
use flux_errors::Errors;
use flux_middle::{
    fhir,
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    rty::{
        self,
        fold::{BottomUpFolder, TypeFoldable},
        refining::Refiner,
    },
    rustc::{
        lowering::{self, UnsupportedReason},
        ty::{self, FieldIdx, VariantIdx},
    },
};
use rustc_ast::Mutability;
use rustc_data_structures::unord::UnordMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_type_ir::{DebruijnIndex, InferConst, INNERMOST};

pub(crate) fn type_alias(
    genv: GlobalEnv,
    alias: &fhir::TyAlias,
    ty: &rty::Ty,
    def_id: LocalDefId,
) -> QueryResult<rty::Ty> {
    let rust_ty = genv.lower_type_of(def_id)?.skip_binder();
    let generics = genv.generics_of(def_id)?;
    let expected = Refiner::default(genv, &generics).refine_ty(&rust_ty)?;
    let mut zipper = Zipper::new(genv, def_id.to_def_id());

    if zipper.zip_ty(ty, &expected).is_err() {
        zipper
            .errors
            .emit(errors::IncompatibleRefinement::type_alias(genv, def_id.to_def_id(), alias));
    }

    zipper.errors.into_result()?;

    Ok(zipper.holes.replace_holes(ty))
}

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

    let mut zipper = Zipper::new(genv, def_id.to_def_id());
    zipper.enter_binders(fn_sig, &expected, |zipper, fn_sig, expected| {
        zipper.zip_fn_sig(decl, fn_sig, expected)
    });

    zipper.errors.into_result()?;

    Ok(zipper.holes.replace_holes(fn_sig))
}

pub(crate) fn variants(
    genv: GlobalEnv,
    variants: &[rty::PolyVariant],
    adt_def_id: LocalDefId,
) -> QueryResult<Vec<rty::PolyVariant>> {
    let adt_def_id = genv.resolve_maybe_extern_id(adt_def_id.to_def_id());
    let generics = genv.generics_of(adt_def_id)?;
    let refiner = Refiner::default(genv, &generics);
    let mut zipper = Zipper::new(genv, adt_def_id);
    // TODO check same number of variants
    for (i, variant) in variants.iter().enumerate() {
        let variant_idx = VariantIdx::from_usize(i);
        let expected = refiner.refine_variant_def(adt_def_id, variant_idx)?;
        zipper.zip_variant(variant, &expected, variant_idx);
    }

    zipper.errors.into_result()?;

    Ok(variants
        .iter()
        .map(|v| zipper.holes.replace_holes(v))
        .collect())
}

struct Zipper<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    owner_id: DefId,
    locs: UnordMap<rty::Loc, rty::Ty>,
    holes: Holes,
    a_index: DebruijnIndex,
    b_index: DebruijnIndex,
    errors: Errors<'genv>,
}

#[derive(Default)]
struct Holes {
    types: UnordMap<rty::TyVid, rty::Ty>,
    regions: UnordMap<rty::RegionVid, rty::Region>,
    consts: UnordMap<rty::ConstVid, rty::Const>,
}

impl Holes {
    fn replace_holes<T: TypeFoldable>(&self, t: &T) -> T {
        t.fold_with(&mut BottomUpFolder {
            ty_op: |ty| {
                if let rty::TyKind::Infer(vid) = ty.kind() {
                    self.types
                        .get(vid)
                        .cloned()
                        .unwrap_or_else(|| bug!("unfilled type hole {vid:?}"))
                } else {
                    ty
                }
            },
            lt_op: |r| {
                if let rty::Region::ReVar(vid) = r {
                    self.regions
                        .get(&vid)
                        .copied()
                        .unwrap_or_else(|| bug!("unfilled region hole {vid:?}"))
                } else {
                    r
                }
            },
            ct_op: |c| {
                if let rty::ConstKind::Infer(InferConst::Var(cid)) = c.kind {
                    self.consts
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

impl<'genv, 'tcx> Zipper<'genv, 'tcx> {
    fn new(genv: GlobalEnv<'genv, 'tcx>, owner_id: DefId) -> Self {
        Self {
            genv,
            owner_id,
            locs: UnordMap::default(),
            holes: Default::default(),
            a_index: INNERMOST,
            b_index: INNERMOST,
            errors: Errors::new(genv.sess()),
        }
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
        })
    }

    fn zip_fn_sig(&mut self, decl: &fhir::FnDecl, a: &rty::FnSig, b: &rty::FnSig) {
        if a.inputs().len() != b.inputs().len() {
            self.errors
                .emit(errors::IncompatiblParamCount::new(self.genv, decl, self.owner_id));
            return;
        }
        for (i, (ty_a, ty_b)) in iter::zip(a.inputs(), b.inputs()).enumerate() {
            if self.zip_ty(ty_a, ty_b).is_err() {
                self.errors.emit(errors::IncompatibleRefinement::fn_input(
                    self.genv,
                    self.owner_id,
                    decl,
                    i,
                ));
            }
        }
        self.enter_binders(a.output(), b.output(), |this, output_a, output_b| {
            this.zip_output(decl, output_a, output_b)
        })
    }

    fn zip_output(&mut self, decl: &fhir::FnDecl, a: &rty::FnOutput, b: &rty::FnOutput) {
        if self.zip_ty(&a.ret, &b.ret).is_err() {
            self.errors.emit(errors::IncompatibleRefinement::fn_output(
                self.genv,
                self.owner_id,
                decl,
            ));
        }
        // Skip ensure clauses if errors because we may not have a type for all locations
        if self.errors.has_errors() {
            return;
        }
        for ensures in &a.ensures {
            if let rty::Ensures::Type(path, ty_a) = ensures {
                let loc = path.to_loc().unwrap();
                let ty_b = self.locs.get(&loc).unwrap().clone();
                self.zip_ty(ty_a, &ty_b);
            }
        }
    }

    fn zip_ty(&mut self, a: &rty::Ty, b: &rty::Ty) -> Result<(), Error> {
        match (a.kind(), b.kind()) {
            (rty::TyKind::Infer(vid), _) => {
                let b = self.adjust_binders(b);
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
                self.zip_const(len_a, len_b)?;
                self.zip_ty(ty_a, ty_b)
            }
            (rty::BaseTy::Never, rty::BaseTy::Never) => Ok(()),
            (rty::BaseTy::Param(pty_a), rty::BaseTy::Param(pty_b)) => {
                assert_eq_or_incompatible(pty_a, pty_b)
            }
            (rty::BaseTy::Dynamic(_, re_a), rty::BaseTy::Dynamic(_, re_b)) => {
                // FIXME(nilehmann) we should check the existentials predicates
                self.zip_region(re_a, re_b);
                Ok(())
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
                self.zip_const(ct_a, ct_b)
            }
            _ => Err(Error::Incompatible),
        }
    }

    fn zip_const(&mut self, a: &rty::Const, b: &ty::Const) -> Result<(), Error> {
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
            _ => Err(Error::Incompatible),
        }
    }

    fn zip_region(&mut self, a: &rty::Region, b: &ty::Region) {
        if let rty::Region::ReVar(vid) = a {
            let re = self.adjust_binders(b);
            self.holes.regions.insert(*vid, re);
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
}

fn assert_eq_or_incompatible<T: Eq>(a: T, b: T) -> Result<(), Error> {
    if a != b {
        return Err(Error::Incompatible);
    }
    Ok(())
}

fn local_id_for_maybe_extern(genv: GlobalEnv, def_id: DefId) -> LocalDefId {
    genv.get_local_id_for_extern(def_id)
        .unwrap_or_else(|| def_id.expect_local())
}

enum Error {
    Incompatible,
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_middle::{
        fhir,
        global_env::GlobalEnv,
        rustc::ty::{FieldIdx, VariantIdx},
    };
    use rustc_hir::def_id::DefId;
    use rustc_span::{Span, DUMMY_SP};

    use super::local_id_for_maybe_extern;

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incompatible_refinement, code = E0999)]
    pub(super) struct IncompatibleRefinement {
        #[primary_span]
        #[label]
        span: Span,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
        expected_ty: String,
        def_descr: &'static str,
    }

    impl IncompatibleRefinement {
        pub(super) fn type_alias(
            genv: GlobalEnv,
            def_id: DefId,
            type_alias: &fhir::TyAlias,
        ) -> Self {
            let tcx = genv.tcx();
            Self {
                span: type_alias.ty.span,
                def_descr: tcx.def_descr(def_id),
                expected_span: tcx.def_span(def_id),
                expected_ty: format!("{}", tcx.type_of(def_id).skip_binder()),
            }
        }

        pub(super) fn fn_input(
            genv: GlobalEnv,
            def_id: DefId,
            decl: &fhir::FnDecl,
            pos: usize,
        ) -> Self {
            let expected_decl = genv
                .tcx()
                .hir_node_by_def_id(local_id_for_maybe_extern(genv, def_id))
                .fn_decl()
                .unwrap();

            let expected_ty = expected_decl.inputs[pos];
            Self {
                span: decl.inputs[pos].span,
                def_descr: genv.tcx().def_descr(def_id),
                expected_span: expected_ty.span,
                expected_ty: rustc_hir_pretty::ty_to_string(&genv.tcx(), &expected_ty),
            }
        }

        pub(super) fn fn_output(genv: GlobalEnv, def_id: DefId, decl: &fhir::FnDecl) -> Self {
            let expected_decl = genv
                .tcx()
                .hir_node_by_def_id(local_id_for_maybe_extern(genv, def_id))
                .fn_decl()
                .unwrap();

            let expected_ty = match expected_decl.output {
                rustc_hir::FnRetTy::DefaultReturn(_) => "()".to_string(),
                rustc_hir::FnRetTy::Return(ty) => rustc_hir_pretty::ty_to_string(&genv.tcx(), ty),
            };
            let spec_span = decl.output.ret.span;
            Self {
                span: spec_span,
                def_descr: genv.tcx().def_descr(def_id),
                expected_span: expected_decl.output.span(),
                expected_ty,
            }
        }

        pub(super) fn field(
            genv: GlobalEnv,
            adt_def_id: DefId,
            variant_idx: VariantIdx,
            field_idx: FieldIdx,
        ) -> Self {
            let tcx = genv.tcx();
            let adt_def = tcx.adt_def(adt_def_id);
            let field_def = &adt_def.variant(variant_idx).fields[field_idx];

            let local_id = local_id_for_maybe_extern(genv, adt_def_id);
            let item = genv.map().expect_item(local_id).unwrap();
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
                expected_span: tcx.def_span(field_def.did),
                expected_ty: format!("{}", tcx.type_of(field_def.did).skip_binder()),
            }
        }
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
        pub(super) fn new(genv: GlobalEnv, decl: &fhir::FnDecl, def_id: DefId) -> Self {
            let def_descr = genv.tcx().def_descr(def_id);

            let span = if decl.inputs.len() > 0 {
                decl.inputs[decl.inputs.len() - 1]
                    .span
                    .with_lo(decl.inputs[0].span.lo())
            } else {
                decl.span
            };

            let expected_span = if let Some(local_id) = def_id.as_local()
                && let expected_decl = genv.tcx().hir_node_by_def_id(local_id).fn_decl().unwrap()
                && expected_decl.inputs.len() > 0
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
            adt_def_id: DefId,
            variant_idx: VariantIdx,
        ) -> Self {
            let adt_def = genv.tcx().adt_def(adt_def_id);
            let expected_variant = adt_def.variant(variant_idx);

            let local_id = local_id_for_maybe_extern(genv, adt_def_id);

            // Get the span of the variant if this is an enum. Structs cannot have produce a field
            // count mismatch.
            let span = if let Ok(fhir::Node::Item(item)) = genv.map().node(local_id)
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
