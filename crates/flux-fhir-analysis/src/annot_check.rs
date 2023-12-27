//! Check if an [`fhir`] annotation is a valid refinement of the corresponding rust declaration.
//!
//! To check if an [`fhir`] is valid, we first [`lift`] the `hir` declaration into [`fhir`] and then
//! "zip" them together.
//!
//! [`lift`]: flux_middle::fhir::lift
//! [`fhir`]: flux_middle::fhir
use std::iter;

use flux_common::{bug, iter::IterExt};
use flux_errors::ErrorGuaranteed;
use flux_middle::{
    fhir::{
        self,
        lift::{self, LiftCtxt},
        Res, WfckResults,
    },
    global_env::GlobalEnv,
};
use rustc_data_structures::unord::UnordMap;
use rustc_errors::IntoDiagnostic;
use rustc_hir::OwnerId;

pub fn check_fn_sig(
    genv: &GlobalEnv,
    wfckresults: &mut WfckResults,
    owner_id: OwnerId,
    fn_sig: &fhir::FnSig,
) -> Result<(), ErrorGuaranteed> {
    if fn_sig.lifted {
        return Ok(());
    }
    let self_ty = lift::lift_self_ty(genv.tcx, genv.sess, owner_id)?;
    let expected_fn_sig = &lift::lift_fn(genv.tcx, genv.sess, owner_id)?.1.fn_sig;
    Zipper::new(genv, wfckresults, self_ty.as_ref()).zip_fn_sig(fn_sig, expected_fn_sig)
}

pub fn check_alias(
    genv: &GlobalEnv,
    wfckresults: &mut WfckResults,
    ty_alias: &fhir::TyAlias,
) -> Result<(), ErrorGuaranteed> {
    if ty_alias.lifted {
        return Ok(());
    }
    let (.., expected_ty_alias) = lift::lift_type_alias(genv.tcx, genv.sess, ty_alias.owner_id)?;
    Zipper::new(genv, wfckresults, None).zip_ty(&ty_alias.ty, &expected_ty_alias.ty)
}

pub fn check_struct_def(
    genv: &GlobalEnv,
    wfckresults: &mut WfckResults,
    struct_def: &fhir::StructDef,
) -> Result<(), ErrorGuaranteed> {
    match &struct_def.kind {
        fhir::StructKind::Transparent { fields } => {
            let mut liftcx = LiftCtxt::new(genv.tcx, genv.sess, struct_def.owner_id, None);
            fields.iter().try_for_each_exhaust(|field| {
                if field.lifted {
                    return Ok(());
                }
                let self_ty = lift::lift_self_ty(genv.tcx, genv.sess, struct_def.owner_id)?;
                Zipper::new(genv, wfckresults, self_ty.as_ref())
                    .zip_ty(&field.ty, &liftcx.lift_field_def_id(field.def_id)?.ty)
            })
        }
        _ => Ok(()),
    }
}

pub fn check_enum_def(
    genv: &GlobalEnv,
    wfckresults: &mut WfckResults,
    enum_def: &fhir::EnumDef,
) -> Result<(), ErrorGuaranteed> {
    let tcx = genv.tcx;
    let sess = genv.sess;
    let mut liftcx = LiftCtxt::new(tcx, sess, enum_def.owner_id, None);
    enum_def.variants.iter().try_for_each_exhaust(|variant| {
        if variant.lifted {
            return Ok(());
        }
        let self_ty = lift::lift_self_ty(genv.tcx, sess, enum_def.owner_id)?;
        Zipper::new(genv, wfckresults, self_ty.as_ref())
            .zip_enum_variant(variant, &liftcx.lift_enum_variant_id(variant.def_id)?)
    })
}

struct Zipper<'zip, 'tcx> {
    genv: &'zip GlobalEnv<'zip, 'tcx>,
    wfckresults: &'zip mut WfckResults,
    locs: LocsMap<'zip>,
    self_ty: Option<&'zip fhir::Ty>,
}

type LocsMap<'a> = UnordMap<fhir::Name, &'a fhir::Ty>;

impl<'zip, 'tcx> Zipper<'zip, 'tcx> {
    fn new(
        genv: &'zip GlobalEnv<'zip, 'tcx>,
        wfckresults: &'zip mut WfckResults,
        self_ty: Option<&'zip fhir::Ty>,
    ) -> Self {
        Self { genv, wfckresults, locs: LocsMap::default(), self_ty }
    }

    fn zip_enum_variant(
        &mut self,
        variant: &fhir::VariantDef,
        expected_variant: &'zip fhir::VariantDef,
    ) -> Result<(), ErrorGuaranteed> {
        if variant.fields.len() != expected_variant.fields.len() {
            return Err(
                self.emit_err(errors::FieldCountMismatch::from_variants(variant, expected_variant))
            );
        }
        iter::zip(&variant.fields, &expected_variant.fields).try_for_each_exhaust(
            |(field, expected_field)| self.zip_ty(&field.ty, &expected_field.ty),
        )?;

        self.zip_bty(&variant.ret.bty, &expected_variant.ret.bty)
    }

    fn zip_fn_sig(
        &mut self,
        fn_sig: &fhir::FnSig,
        expected_fn_sig: &'zip fhir::FnSig,
    ) -> Result<(), ErrorGuaranteed> {
        if fn_sig.args.len() != expected_fn_sig.args.len() {
            return Err(self.emit_err(errors::FunArgCountMismatch::new(fn_sig, expected_fn_sig)));
        }
        self.zip_tys(&fn_sig.args, &expected_fn_sig.args)?;
        self.zip_constraints(&fn_sig.requires)?;

        self.zip_ty(&fn_sig.output.ret, &expected_fn_sig.output.ret)?;
        self.zip_constraints(&fn_sig.output.ensures)
    }

    fn zip_constraints(&mut self, constrs: &[fhir::Constraint]) -> Result<(), ErrorGuaranteed> {
        constrs.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, ty, _) = constr {
                self.zip_ty(ty, self.locs[&loc.name])
            } else {
                Ok(())
            }
        })
    }

    fn zip_tys(
        &mut self,
        tys: &[fhir::Ty],
        expected_tys: &'zip [fhir::Ty],
    ) -> Result<(), ErrorGuaranteed> {
        iter::zip(tys, expected_tys)
            .try_for_each_exhaust(|(ty, expected)| self.zip_ty(ty, expected))
    }

    fn zip_ty(
        &mut self,
        ty: &fhir::Ty,
        expected_ty: &'zip fhir::Ty,
    ) -> Result<(), ErrorGuaranteed> {
        match (&ty.kind, &expected_ty.kind) {
            (fhir::TyKind::Constr(_, ty) | fhir::TyKind::Exists(.., ty), _) => {
                self.zip_ty(ty, expected_ty)
            }
            (
                fhir::TyKind::BaseTy(bty) | fhir::TyKind::Indexed(bty, _),
                fhir::TyKind::BaseTy(expected_bty),
            ) => self.zip_bty(bty, expected_bty),
            (fhir::TyKind::Ptr(lft, loc), fhir::TyKind::Ref(expected_lft, expected_mut_ty)) => {
                if expected_mut_ty.mutbl.is_mut() {
                    self.zip_lifetime(*lft, *expected_lft);
                    self.locs.insert(loc.name, &expected_mut_ty.ty);
                    Ok(())
                } else {
                    Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty).with_note(
                            "only mutable reference can be refined with a strong reference",
                        ),
                    ))
                }
            }
            (fhir::TyKind::Ref(lft, mut_ty), fhir::TyKind::Ref(expected_lft, expected_mut_ty)) => {
                if mut_ty.mutbl != expected_mut_ty.mutbl {
                    return Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty)
                            .with_note("types differ in mutability"),
                    ));
                }
                self.zip_lifetime(*lft, *expected_lft);
                self.zip_ty(&mut_ty.ty, &expected_mut_ty.ty)
            }
            (fhir::TyKind::Tuple(tys), fhir::TyKind::Tuple(expected_tys)) => {
                if tys.len() != expected_tys.len() {
                    return Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty)
                            .with_note("tuples have different length"),
                    ));
                }
                self.zip_tys(tys, expected_tys)
            }
            (fhir::TyKind::Array(ty, len), fhir::TyKind::Array(expected_ty, expected_len)) => {
                if len.val != expected_len.val {
                    return Err(self.emit_err(errors::ArrayLenMismatch::new(len, expected_len)));
                }
                self.zip_ty(ty, expected_ty)
            }
            (
                fhir::TyKind::RawPtr(ty, mutbl),
                fhir::TyKind::RawPtr(expected_ty, expected_mutbl),
            ) => {
                if mutbl != expected_mutbl {
                    return Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty)
                            .with_note("types differ in mutability"),
                    ));
                }
                self.zip_ty(ty, expected_ty)
            }
            (fhir::TyKind::Never, fhir::TyKind::Never) => Ok(()),
            (fhir::TyKind::Hole(fhir_id), _) => {
                self.wfckresults
                    .type_holes_mut()
                    .insert(*fhir_id, expected_ty.clone());
                Ok(())
            }
            (
                fhir::TyKind::OpaqueDef(item_id, args, _, _),
                fhir::TyKind::OpaqueDef(exp_item_id, exp_args, _, _),
            ) => {
                if item_id != exp_item_id {
                    return Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty)
                            .with_note("impl trait: types differ in impl id!"),
                    ));
                }
                if args.len() != exp_args.len() {
                    return Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty)
                            .with_note("impl trait: types differ in number of args!"),
                    ));
                }
                for (arg, exp_arg) in args.iter().zip(exp_args) {
                    self.zip_generic_arg(arg, exp_arg)?;
                }
                Ok(())
            }

            _ => Err(self.emit_err(errors::InvalidRefinement::from_tys(ty, expected_ty))),
        }
    }

    fn zip_generic_arg(
        &mut self,
        arg1: &fhir::GenericArg,
        arg2: &'zip fhir::GenericArg,
    ) -> Result<(), ErrorGuaranteed> {
        match (arg1, arg2) {
            (fhir::GenericArg::Type(ty1), fhir::GenericArg::Type(ty2)) => self.zip_ty(ty1, ty2),
            (fhir::GenericArg::Lifetime(lft1), fhir::GenericArg::Lifetime(lft2)) => {
                self.zip_lifetime(*lft1, *lft2);
                Ok(())
            }
            _ => bug!(),
        }
    }

    fn zip_lifetime(&mut self, lft: fhir::Lifetime, expected_lft: fhir::Lifetime) {
        let fhir::Lifetime::Hole(fhir_id) = lft else {
            return;
        };

        match expected_lft {
            fhir::Lifetime::Resolved(res) => {
                self.wfckresults.lifetime_holes_mut().insert(fhir_id, res);
            }
            fhir::Lifetime::Hole(_) => {
                bug!("unexpected hole in lifted lifetime");
            }
        }
    }

    fn zip_bty(
        &mut self,
        bty: &fhir::BaseTy,
        expected_bty: &'zip fhir::BaseTy,
    ) -> Result<(), ErrorGuaranteed> {
        match (&bty.kind, &expected_bty.kind) {
            (fhir::BaseTyKind::Path(qpath), fhir::BaseTyKind::Path(expected_qpath)) => {
                self.zip_qpath(qpath, expected_qpath)
            }
            (fhir::BaseTyKind::Slice(ty), fhir::BaseTyKind::Slice(expected_ty)) => {
                self.zip_ty(ty, expected_ty)
            }
            _ => Err(self.emit_err(errors::InvalidRefinement::from_btys(bty, expected_bty))),
        }
    }

    fn zip_qpath(
        &mut self,
        qpath: &fhir::QPath,
        expected_qpath: &'zip fhir::QPath,
    ) -> Result<(), ErrorGuaranteed> {
        match (qpath, expected_qpath) {
            (fhir::QPath::Resolved(None, path), fhir::QPath::Resolved(None, expected_path)) => {
                self.zip_path(path, expected_path)
            }
            (
                fhir::QPath::Resolved(Some(self_ty), path),
                fhir::QPath::Resolved(Some(expected_self_ty), expected_path),
            ) => {
                self.zip_ty(self_ty, expected_self_ty)?;
                self.zip_path(path, expected_path)
            }
            _ => Err(self.emit_err(errors::InvalidRefinement::from_qpaths(qpath, expected_qpath))),
        }
    }

    fn is_same_res(genv: &GlobalEnv, res: Res, expected: Res) -> bool {
        if res == expected {
            return true;
        };
        if let Res::Def(res_kind, res_did) = res
            && let Res::Def(expected_kind, expected_did) = expected
            && let Some(extern_id) = genv.map().get_extern(res_did)
            && res_kind == expected_kind
            && extern_id.to_def_id() == expected_did
        {
            return true;
        }
        false
    }

    fn zip_path(
        &mut self,
        path: &fhir::Path,
        expected_path: &'zip fhir::Path,
    ) -> Result<(), ErrorGuaranteed> {
        if !Self::is_same_res(self.genv, path.res, expected_path.res) {
            if let fhir::Res::SelfTyAlias { .. } = expected_path.res
                && let Some(self_ty) = self.self_ty
                && let Some(expected_path) = self_ty.as_path()
            {
                return self.zip_path(path, expected_path);
            }
            return Err(self.emit_err(errors::InvalidRefinement::from_paths(path, expected_path)));
        }
        if path.args.len() != expected_path.args.len() {
            return Err(self.emit_err(errors::GenericArgCountMismatch::new(path, expected_path)));
        }

        iter::zip(&path.args, &expected_path.args)
            .try_for_each_exhaust(|(arg, expected)| self.zip_generic_arg(arg, expected))
    }

    #[track_caller]
    fn emit_err<'a>(&'a self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
        self.genv.sess.emit_err(err)
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::fhir;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_invalid_refinement, code = "FLUX")]
    pub(super) struct InvalidRefinement {
        #[primary_span]
        #[label]
        span: Span,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
        expected_ty: String,
        #[note]
        has_note: Option<()>,
        note: String,
    }

    impl InvalidRefinement {
        pub(super) fn from_tys(ty: &fhir::Ty, expected_ty: &fhir::Ty) -> Self {
            Self {
                span: ty.span,
                expected_span: expected_ty.span,
                expected_ty: format!("{expected_ty:?}"),
                has_note: None,
                note: String::new(),
            }
        }

        pub(super) fn from_paths(path: &fhir::Path, expected_path: &fhir::Path) -> Self {
            Self {
                span: path.span,
                expected_span: expected_path.span,
                expected_ty: format!("{expected_path:?}"),
                has_note: None,
                note: String::new(),
            }
        }

        pub(super) fn from_btys(bty: &fhir::BaseTy, expected_bty: &fhir::BaseTy) -> Self {
            Self {
                span: bty.span,
                expected_span: expected_bty.span,
                expected_ty: format!("{expected_bty:?}"),
                has_note: None,
                note: String::new(),
            }
        }

        pub(super) fn from_qpaths(qpath: &fhir::QPath, expected_qpath: &fhir::QPath) -> Self {
            Self {
                span: qpath.span(),
                expected_span: expected_qpath.span(),
                expected_ty: format!("{expected_qpath:?}"),
                has_note: None,
                note: String::new(),
            }
        }

        pub(super) fn with_note(self, note: impl ToString) -> Self {
            Self { has_note: Some(()), note: note.to_string(), ..self }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_fun_arg_count_mismatch, code = "FLUX")]
    pub(super) struct FunArgCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        args: usize,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
        expected_args: usize,
    }

    impl FunArgCountMismatch {
        pub(super) fn new(fn_sig: &fhir::FnSig, expected_fn_sig: &fhir::FnSig) -> Self {
            Self {
                span: fn_sig.span,
                args: fn_sig.args.len(),
                expected_span: expected_fn_sig.span,
                expected_args: expected_fn_sig.args.len(),
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_generic_argument_count_mismatch, code = "FLUX")]
    pub(super) struct GenericArgCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        expected: usize,
        def_descr: &'static str,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
    }

    impl GenericArgCountMismatch {
        pub(super) fn new(path: &fhir::Path, expected_path: &fhir::Path) -> Self {
            GenericArgCountMismatch {
                span: path.span,
                found: path.args.len(),
                expected: expected_path.args.len(),
                def_descr: path.res.descr(),
                expected_span: expected_path.span,
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_array_len_mismatch, code = "FLUX")]
    pub(super) struct ArrayLenMismatch {
        #[primary_span]
        #[label]
        span: Span,
        len: usize,
        #[label(fhir_analysis_expected_label)]
        expected_span: Span,
        expected_len: usize,
    }

    impl ArrayLenMismatch {
        pub(super) fn new(len: &fhir::ArrayLen, expected_len: &fhir::ArrayLen) -> Self {
            Self {
                span: len.span,
                len: len.val,
                expected_span: expected_len.span,
                expected_len: expected_len.val,
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_field_count_mismatch, code = "FLUX")]
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
        pub(super) fn from_variants(
            variant: &fhir::VariantDef,
            expected_variant: &fhir::VariantDef,
        ) -> Self {
            Self {
                span: variant.span,
                fields: variant.fields.len(),
                expected_span: expected_variant.span,
                expected_fields: expected_variant.fields.len(),
            }
        }
    }
}
