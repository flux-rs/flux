use std::iter;

use flux_common::iter::IterExt;
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::{early_ctxt::EarlyCtxt, fhir};
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
            ) => self.zip_bty(bty, expected_bty),
            (fhir::TyKind::Ptr(loc), fhir::TyKind::Ref(expected_rk, expected_ty)) => {
                if let fhir::RefKind::Mut = expected_rk {
                    self.locs.insert(loc.name, expected_ty);
                    Ok(())
                } else {
                    todo!()
                }
            }
            (fhir::TyKind::Ref(rk, ty), fhir::TyKind::Ref(expected_rk, expected_ty)) => {
                if rk != expected_rk {
                    todo!()
                }
                self.zip_ty(ty, expected_ty)
            }
            (fhir::TyKind::Tuple(tys), fhir::TyKind::Tuple(expected_tys)) => {
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
            _ => todo!(),
        }
    }

    fn zip_bty(
        &mut self,
        bty: &fhir::BaseTy,
        expected_bty: &'zip fhir::BaseTy,
    ) -> Result<(), ErrorGuaranteed> {
        match (&bty.kind, &expected_bty.kind) {
            (fhir::BaseTyKind::Path(path), fhir::BaseTyKind::Path(expected_path)) => {
                self.zip_path(path, expected_path)
            }
            (fhir::BaseTyKind::Slice(ty), fhir::BaseTyKind::Slice(expected_ty)) => {
                self.zip_ty(ty, expected_ty)
            }
            _ => todo!(),
        }
    }

    fn zip_path(
        &mut self,
        path: &fhir::Path,
        expected_path: &'zip fhir::Path,
    ) -> Result<(), ErrorGuaranteed> {
        if path.res != expected_path.res {
            todo!()
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
}
