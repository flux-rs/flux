use std::iter;

use flux_common::iter::IterExt;
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::rustc::ty::Mutability;
use flux_syntax::surface::{self, Res};
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

struct Zipper<'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'sess FluxSession,
    /// [`LocalDefId`] of the definition being checked, this could either be a field on a struct,
    /// a variant on a enum, or a function.
    def_id: LocalDefId,
}

impl<'sess, 'tcx> Zipper<'sess, 'tcx> {
    fn zip_ty(
        &self,
        ty: surface::Ty,
        hir_ty: &hir::Ty,
    ) -> Result<surface::Ty<Res>, ErrorGuaranteed> {
        let kind = match (ty.kind, &hir_ty.kind) {
            (surface::TyKind::Base(bty), _) => surface::TyKind::Base(self.zip_bty(bty, hir_ty)?),
            (surface::TyKind::Indexed { bty, indices }, _) => {
                surface::TyKind::Indexed { bty: self.zip_bty(bty, hir_ty)?, indices }
            }
            (surface::TyKind::Exists { bind, bty, pred }, _) => {
                surface::TyKind::Exists { bind, bty: self.zip_bty(bty, hir_ty)?, pred }
            }
            (surface::TyKind::Constr(pred, ty), _) => {
                surface::TyKind::Constr(pred, Box::new(self.zip_ty(*ty, hir_ty)?))
            }
            (surface::TyKind::Ref(rk, ty), hir::TyKind::Ref(_, mut_ty)) => {
                self.zip_mutability(rk, mut_ty.mutbl)?;
                surface::TyKind::Ref(rk, Box::new(self.zip_ty(*ty, mut_ty.ty)?))
            }
            (surface::TyKind::Tuple(tys), hir::TyKind::Tup(hir_tys)) => {
                let tys = iter::zip(tys, *hir_tys)
                    .map(|(ty, hir_ty)| self.zip_ty(ty, hir_ty))
                    .try_collect_exhaust()?;
                surface::TyKind::Tuple(tys)
            }
            (surface::TyKind::Array(ty, len), hir::TyKind::Array(hir_ty, hir_len)) => {
                self.zip_array_len(len, *hir_len)?;
                surface::TyKind::Array(Box::new(self.zip_ty(*ty, hir_ty)?), len)
            }
            _ => {
                todo!()
            }
        };
        Ok(surface::Ty { kind, span: ty.span })
    }

    fn zip_bty(
        &self,
        bty: surface::BaseTy,
        hir_ty: &hir::Ty,
    ) -> Result<surface::BaseTy<Res>, ErrorGuaranteed> {
        match (bty, &hir_ty.kind) {
            (surface::BaseTy::Path(path), hir::TyKind::Path(qpath)) => {
                let path = self.zip_path(path, qpath)?;
                Ok(surface::BaseTy::Path(path))
            }
            (surface::BaseTy::Slice(ty), hir::TyKind::Slice(hir_ty)) => {
                Ok(surface::BaseTy::Slice(Box::new(self.zip_ty(*ty, hir_ty)?)))
            }
            _ => {
                todo!()
            }
        }
    }

    fn zip_path(
        &self,
        path: surface::Path,
        hir_path: &hir::QPath,
    ) -> Result<surface::Path<Res>, ErrorGuaranteed> {
        let hir::QPath::Resolved(None, hir_path) = hir_path else {
            todo!()
            // return Err(self.sess.emit_err(errors::UnsupportedSignature::new(
            //     qpath.span(),
            //     "unsupported type",
            // )));
        };
        match hir_path.res {
            hir::def::Res::Def(_, _) => todo!(),
            hir::def::Res::PrimTy(_) => todo!(),
            hir::def::Res::SelfTyParam { trait_ } => todo!(),
            hir::def::Res::SelfTyAlias { alias_to, forbid_generic, is_trait_impl } => todo!(),
            hir::def::Res::SelfCtor(_)
            | hir::def::Res::Local(_)
            | hir::def::Res::ToolMod
            | hir::def::Res::NonMacroAttr(_)
            | hir::def::Res::Err => todo!(),
        }
    }

    fn zip_mutability(
        &self,
        rk: surface::RefKind,
        mutbl: Mutability,
    ) -> Result<(), ErrorGuaranteed> {
        todo!()
    }

    fn zip_array_len(
        &self,
        len: surface::ArrayLen,
        hir_len: hir::ArrayLen,
    ) -> Result<(), ErrorGuaranteed> {
        todo!()
    }
}
