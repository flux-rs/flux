use std::iter;

use flux_common::iter::IterExt;
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::{early_ctxt::EarlyCtxt, fhir};
use rustc_errors::IntoDiagnostic;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

pub fn check_fn_sig(
    early_cx: &EarlyCtxt,
    def_id: LocalDefId,
    fn_sig: &fhir::FnSig,
) -> Result<(), ErrorGuaranteed> {
    Zipper::new(early_cx.tcx, early_cx.sess, def_id)
        .zip_fn_sig(fn_sig, &fhir::lift::lift_fn_sig(early_cx, def_id)?)
}

struct Zipper<'zip, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'zip FluxSession,
    locs: LocsMap<'zip>,
    /// [`LocalDefId`] of the definition being zipped, this could either be a field on a struct,
    /// a variant on a enum, or a function.
    def_id: LocalDefId,
}

type LocsMap<'a> = FxHashMap<fhir::Name, &'a fhir::Ty>;

impl<'zip, 'tcx> Zipper<'zip, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, sess: &'zip FluxSession, def_id: LocalDefId) -> Self {
        Self { tcx, sess, def_id, locs: LocsMap::default() }
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
        fn_sig.requires.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, ty) = constr {
                self.zip_ty(ty, self.locs[&loc.name])
            } else {
                Ok(())
            }
        })?;

        self.zip_fn_output(&fn_sig.output, &expected_fn_sig.output)
    }

    fn zip_fn_output(
        &mut self,
        output: &fhir::FnOutput,
        expected_output: &'zip fhir::FnOutput,
    ) -> Result<(), ErrorGuaranteed> {
        self.zip_ty(&output.ret, &expected_output.ret)?;
        output.ensures.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, ty) = constr {
                if let Some(expected_ty) = self.locs.get(&loc.name) {
                    self.zip_ty(ty, expected_ty)
                } else {
                    todo!()
                }
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
            (fhir::TyKind::Constr(_, ty), _) => self.zip_ty(ty, expected_ty),
            (
                fhir::TyKind::BaseTy(bty)
                | fhir::TyKind::Indexed(bty, _)
                | fhir::TyKind::Exists(bty, ..),
                fhir::TyKind::BaseTy(expected_bty),
            ) => self.zip_bty(ty, bty, expected_ty, expected_bty),
            (fhir::TyKind::Ptr(loc), fhir::TyKind::Ref(expected_rk, expected_ref_ty)) => {
                if let fhir::RefKind::Mut = expected_rk {
                    self.locs.insert(loc.name, expected_ref_ty);
                    Ok(())
                } else {
                    Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty).with_note(
                            "only mutable reference can be refined with a strong reference",
                        ),
                    ))
                }
            }
            (fhir::TyKind::Ref(rk, ref_ty), fhir::TyKind::Ref(expected_rk, expected_ref_ty)) => {
                if rk != expected_rk {
                    return Err(self.emit_err(
                        errors::InvalidRefinement::from_tys(ty, expected_ty)
                            .with_note("types differ in mutability"),
                    ));
                }
                self.zip_ty(ref_ty, expected_ref_ty)
            }
            (fhir::TyKind::Tuple(tys), fhir::TyKind::Tuple(expected_tys)) => {
                if tys.len() != expected_tys.len() {
                    todo!()
                }
                self.zip_tys(tys, expected_tys)
            }
            (fhir::TyKind::Array(ty, len), fhir::TyKind::Array(expected_ty, expected_len)) => {
                if len != expected_len {
                    todo!()
                }
                self.zip_ty(ty, expected_ty)
            }
            (
                fhir::TyKind::RawPtr(ty, mutbl),
                fhir::TyKind::RawPtr(expected_ty, expected_mutbl),
            ) => {
                if mutbl != expected_mutbl {
                    todo!()
                }
                self.zip_ty(ty, expected_ty)
            }
            (fhir::TyKind::Never, fhir::TyKind::Never) => Ok(()),
            _ => Err(self.emit_err(errors::InvalidRefinement::from_tys(ty, expected_ty))),
        }
    }

    fn zip_bty(
        &mut self,
        ty: &fhir::Ty,
        bty: &fhir::BaseTy,
        expected_ty: &fhir::Ty,
        expected_bty: &'zip fhir::BaseTy,
    ) -> Result<(), ErrorGuaranteed> {
        match (&bty.kind, &expected_bty.kind) {
            (fhir::BaseTyKind::Path(path), fhir::BaseTyKind::Path(expected_path)) => {
                self.zip_path(ty, path, expected_ty, expected_path)
            }
            (fhir::BaseTyKind::Slice(ty), fhir::BaseTyKind::Slice(expected_ty)) => {
                self.zip_ty(ty, expected_ty)
            }
            _ => todo!(),
        }
    }

    fn zip_path(
        &mut self,
        ty: &fhir::Ty,
        path: &fhir::Path,
        expected_ty: &fhir::Ty,
        expected_path: &'zip fhir::Path,
    ) -> Result<(), ErrorGuaranteed> {
        if path.res != expected_path.res {
            return Err(self.emit_err(errors::InvalidRefinement::from_tys(ty, expected_ty)));
        }
        let len = path.generics.len();
        let expected_len = expected_path.generics.len();
        if len != expected_len {
            todo!()
            // return self.emit_err(errors::GenericArgCountMismatch::from_hir_path(
            //     self.tcx, def_id, path, hir_path,
            // ));
        }

        iter::zip(&path.generics, &expected_path.generics)
            .try_for_each_exhaust(|(arg, expected)| self.zip_ty(arg, expected))
    }

    fn emit_err<'a>(&'a self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
        self.sess.emit_err(err)
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::fhir;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(annot_check::invalid_refinement, code = "FLUX")]
    pub(super) struct InvalidRefinement<'a> {
        #[primary_span]
        #[label]
        span: Span,
        #[label(annot_check::expected_label)]
        expected_span: Span,
        expected_ty: &'a fhir::Ty,
        #[note]
        has_note: Option<()>,
        note: String,
    }

    impl<'a> InvalidRefinement<'a> {
        pub(super) fn from_tys(ty: &fhir::Ty, expected_ty: &'a fhir::Ty) -> Self {
            Self {
                span: ty.span,
                expected_span: expected_ty.span,
                expected_ty,
                has_note: None,
                note: String::new(),
            }
        }

        pub(super) fn with_note(self, note: impl ToString) -> Self {
            Self { has_note: Some(()), note: note.to_string(), ..self }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::fun_arg_count_mismatch, code = "FLUX")]
    pub(super) struct FunArgCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        args: usize,
        #[label(annot_check::expected_label)]
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
}
