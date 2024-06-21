use std::iter;

use flux_common::bug;
use rustc_ast::Mutability;

use crate::{rty, rustc::ty};

struct Zipper {}

impl Zipper {
    fn zip_ty(&mut self, a: &rty::Ty, b: &ty::Ty) {
        match (a.kind(), b.kind()) {
            (rty::TyKind::Indexed(bty, _), _) => {
                self.zip_bty(bty, b);
            }
            (rty::TyKind::Exists(ctor), _) => self.zip_ty(ctor.as_ref().skip_binder(), b),
            (rty::TyKind::Constr(_, ty), _) => self.zip_ty(ty, b),
            (rty::TyKind::StrgRef(re_a, _, ty_a), ty::TyKind::Ref(re_b, ty_b, Mutability::Mut)) => {
                self.zip_region(re_a, re_b);
                self.zip_ty(ty_a, ty_b);
            }
            (rty::TyKind::Param(pty_a), ty::TyKind::Param(pty_b)) => {
                debug_assert_eq!(pty_a, pty_b);
            }
            (rty::TyKind::Alias(kind_a, aty_a), ty::TyKind::Alias(kind_b, aty_b)) => {
                debug_assert_eq!(kind_a, kind_b);
                debug_assert_eq!(aty_a.def_id, aty_b.def_id);
                debug_assert_eq!(aty_a.args.len(), aty_b.args.len());
                for (arg_a, arg_b) in iter::zip(&aty_a.args, &aty_b.args) {
                    self.zip_generic_arg(arg_a, arg_b);
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
                bug!("incompatible types `{a:?}` `{b:?}`")
            }
        }
    }

    fn zip_bty(&mut self, a: &rty::BaseTy, b: &ty::Ty) {
        match (a, b.kind()) {
            (rty::BaseTy::Int(ity_a), ty::TyKind::Int(ity_b)) => {
                debug_assert_eq!(ity_a, ity_b)
            }
            (rty::BaseTy::Uint(uity_a), ty::TyKind::Uint(uity_b)) => {
                debug_assert_eq!(uity_a, uity_b)
            }
            (rty::BaseTy::Bool, ty::TyKind::Bool) => {}
            (rty::BaseTy::Str, ty::TyKind::Str) => {}
            (rty::BaseTy::Char, ty::TyKind::Char) => {}
            (rty::BaseTy::Float(fty_a), ty::TyKind::Float(fty_b)) => {
                debug_assert_eq!(fty_a, fty_b);
            }
            (rty::BaseTy::Slice(ty_a), ty::TyKind::Slice(ty_b)) => {
                self.zip_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Adt(adt_def_a, args_a), ty::TyKind::Adt(adt_def_b, args_b)) => {
                debug_assert_eq!(adt_def_a.did(), adt_def_b.did());
                debug_assert_eq!(args_a.len(), args_b.len());
                for (arg_a, arg_b) in iter::zip(args_a, args_b) {
                    self.zip_generic_arg(arg_a, arg_b);
                }
            }
            (rty::BaseTy::RawPtr(ty_a, mutbl_a), ty::TyKind::RawPtr(ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.zip_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Ref(re_a, ty_a, mutbl_a), ty::TyKind::Ref(re_b, ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.zip_ty(ty_a, ty_b);
                self.zip_region(re_a, re_b);
            }
            (rty::BaseTy::Tuple(tys_a), ty::TyKind::Tuple(tys_b)) => {
                debug_assert_eq!(tys_a.len(), tys_b.len());
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.zip_ty(ty_a, ty_b);
                }
            }
            (rty::BaseTy::Array(ty_a, len_a), ty::TyKind::Array(ty_b, len_b)) => {
                debug_assert_eq!(len_a, len_b);
                self.zip_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Never, ty::TyKind::Never) => {}
            (rty::BaseTy::Closure(..), _) => {
                bug!("unexpected closure {a:?}")
            }
            (rty::BaseTy::Coroutine(..), _) => {
                bug!("unexpected coroutine {a:?}")
            }
            (rty::BaseTy::Param(pty_a), ty::TyKind::Param(pty_b)) => {
                debug_assert_eq!(pty_a, pty_b);
            }
            _ => {
                bug!("incompatible types `{a:?}` `{b:?}`")
            }
        }
    }

    fn zip_generic_arg(&mut self, a: &rty::GenericArg, b: &ty::GenericArg) {
        match (a, b) {
            (rty::GenericArg::Ty(ty_a), ty::GenericArg::Ty(ty_b)) => self.zip_ty(ty_a, ty_b),
            (rty::GenericArg::Base(ctor_a), ty::GenericArg::Ty(ty_b)) => {
                self.zip_bty(ctor_a.as_bty_skipping_binder(), ty_b);
            }
            (rty::GenericArg::Lifetime(re_a), ty::GenericArg::Lifetime(re_b)) => {
                self.zip_region(re_a, re_b);
            }
            (rty::GenericArg::Const(ct_a), ty::GenericArg::Const(ct_b)) => {
                debug_assert_eq!(ct_a, ct_b);
            }
            _ => {
                bug!("incompatible generic args `{a:?}` `{b:?}`")
            }
        }
    }

    fn zip_region(&mut self, a: &rty::Region, b: &ty::Region) {}
}
