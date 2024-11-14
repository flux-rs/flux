use std::{collections::hash_map, iter};

use flux_common::bug;
use flux_rustc_bridge::ty;
use rustc_data_structures::unord::UnordMap;

use super::fold::TypeFoldable;
use crate::{rty, rty::fold::TypeFolder};

/// See `flux_refineck::type_env::TypeEnv::assign`
pub fn ty_match_regions(a: &rty::Ty, b: &ty::Ty) -> rty::Ty {
    let a = replace_regions_with_unique_vars(a);
    let mut subst = RegionSubst::default();
    subst.ty_infer_from_ty(&a, b);
    subst.apply(&a)
}

pub fn rty_match_regions(a: &rty::Ty, b: &rty::Ty) -> rty::Ty {
    let a = replace_regions_with_unique_vars(a);
    let mut subst = RegionSubst::default();
    subst.rty_infer_from_ty(&a, b);
    subst.apply(&a)
}

/// Replace all regions with a [`ReVar`] assigning each a unique [`RegionVid`]. This is used
/// to have a unique identifier for each position such that we can infer a region substitution.
fn replace_regions_with_unique_vars(ty: &rty::Ty) -> rty::Ty {
    struct Replacer {
        next_rvid: u32,
    }
    impl TypeFolder for Replacer {
        fn fold_region(&mut self, re: &rty::Region) -> rty::Region {
            if let rty::ReBound(..) = re {
                *re
            } else {
                let rvid = self.next_rvid;
                self.next_rvid += 1;
                rty::ReVar(rty::RegionVid::from_u32(rvid))
            }
        }
    }

    ty.fold_with(&mut Replacer { next_rvid: 0 })
}

#[derive(Default, Debug)]
struct RegionSubst {
    map: UnordMap<rty::RegionVid, rty::Region>,
}

impl RegionSubst {
    fn apply<T: TypeFoldable>(&self, t: &T) -> T {
        struct Folder<'a>(&'a RegionSubst);
        impl TypeFolder for Folder<'_> {
            fn fold_region(&mut self, re: &rty::Region) -> rty::Region {
                // FIXME the map should always contain a region
                if let rty::ReVar(rvid) = re
                    && let Some(region) = self.0.map.get(rvid)
                {
                    *region
                } else {
                    *re
                }
            }
        }
        t.fold_with(&mut Folder(self))
    }

    fn infer_from_region(&mut self, a: rty::Region, b: rty::Region) {
        let rty::ReVar(var) = a else { return };
        match self.map.entry(var) {
            hash_map::Entry::Occupied(entry) => {
                if entry.get() != &b {
                    bug!("ambiguous region substitution: {:?} -> [{:?}, {:?}]", a, entry.get(), b);
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(b);
            }
        }
    }
}

impl RegionSubst {
    fn ty_infer_from_fn_sig(&mut self, a: &rty::FnSig, b: &ty::FnSig) {
        debug_assert_eq!(a.inputs().len(), b.inputs().len());
        for (ty_a, ty_b) in iter::zip(a.inputs(), b.inputs()) {
            self.ty_infer_from_ty(ty_a, ty_b);
        }
        self.ty_infer_from_ty(&a.output().skip_binder_ref().ret, b.output());
    }

    fn ty_infer_from_ty(&mut self, a: &rty::Ty, b: &ty::Ty) {
        match (a.kind(), b.kind()) {
            (rty::TyKind::Exists(ty_a), _) => {
                self.ty_infer_from_ty(ty_a.as_ref().skip_binder(), b);
            }
            (rty::TyKind::Constr(_, ty_a), _) => {
                self.ty_infer_from_ty(ty_a, b);
            }
            (rty::TyKind::Indexed(bty_a, _), _) => {
                self.ty_infer_from_bty(bty_a, b);
            }
            (rty::TyKind::Ptr(rty::PtrKind::Mut(re_a), _), ty::TyKind::Ref(re_b, _, mutbl)) => {
                debug_assert!(mutbl.is_mut());
                self.infer_from_region(*re_a, *re_b);
            }
            (rty::TyKind::StrgRef(re_a, ..), ty::TyKind::Ref(re_b, _, mutbl)) => {
                debug_assert!(mutbl.is_mut());
                self.infer_from_region(*re_a, *re_b);
            }
            _ => {}
        }
    }

    fn ty_infer_from_bty(&mut self, a: &rty::BaseTy, ty: &ty::Ty) {
        match (a, ty.kind()) {
            (rty::BaseTy::Adt(_, args_a), ty::TyKind::Adt(_, args_b)) => {
                self.ty_infer_from_generic_args(args_a, args_b);
            }
            (rty::BaseTy::Array(ty_a, _), ty::TyKind::Array(ty_b, _)) => {
                self.ty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Ref(re_a, ty_a, mutbl_a), ty::TyKind::Ref(re_b, ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.infer_from_region(*re_a, *re_b);
                self.ty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Tuple(fields_a), ty::TyKind::Tuple(fields_b)) => {
                debug_assert_eq!(fields_a.len(), fields_b.len());
                for (ty_a, ty_b) in iter::zip(fields_a, fields_b) {
                    self.ty_infer_from_ty(ty_a, ty_b);
                }
            }
            (rty::BaseTy::Slice(ty_a), ty::TyKind::Slice(ty_b)) => {
                self.ty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::FnPtr(poly_sig_a), ty::TyKind::FnPtr(poly_sig_b)) => {
                self.ty_infer_from_fn_sig(
                    poly_sig_a.skip_binder_ref(),
                    poly_sig_b.skip_binder_ref(),
                );
            }
            (rty::BaseTy::RawPtr(ty_a, mutbl_a), ty::TyKind::RawPtr(ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.ty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Dynamic(preds_a, re_a), ty::TyKind::Dynamic(preds_b, re_b)) => {
                debug_assert_eq!(preds_a.len(), preds_b.len());
                self.infer_from_region(*re_a, *re_b);
                for (pred_a, pred_b) in iter::zip(preds_a, preds_b) {
                    self.ty_infer_from_existential_pred(pred_a, pred_b);
                }
            }
            _ => {}
        }
    }

    fn ty_infer_from_existential_pred(
        &mut self,
        a: &rty::PolyExistentialPredicate,
        b: &ty::PolyExistentialPredicate,
    ) {
        match (a.as_ref().skip_binder(), b.as_ref().skip_binder()) {
            (
                rty::ExistentialPredicate::Trait(trait_ref_a),
                ty::ExistentialPredicate::Trait(trait_ref_b),
            ) => {
                debug_assert_eq!(trait_ref_a.def_id, trait_ref_b.def_id);
                self.ty_infer_from_generic_args(&trait_ref_a.args, &trait_ref_b.args);
            }
            (
                rty::ExistentialPredicate::Projection(proj_a),
                ty::ExistentialPredicate::Projection(proj_b),
            ) => {
                debug_assert_eq!(proj_a.def_id, proj_b.def_id);
                self.ty_infer_from_generic_args(&proj_a.args, &proj_b.args);
                self.ty_infer_from_bty(proj_a.term.as_bty_skipping_binder(), &proj_b.term);
            }
            _ => {}
        }
    }

    fn ty_infer_from_generic_args(&mut self, a: &rty::GenericArgs, b: &ty::GenericArgs) {
        debug_assert_eq!(a.len(), b.len());
        for (arg_a, arg_b) in iter::zip(a, b) {
            self.ty_infer_from_generic_arg(arg_a, arg_b);
        }
    }

    fn ty_infer_from_generic_arg(&mut self, a: &rty::GenericArg, b: &ty::GenericArg) {
        match (a, b) {
            (rty::GenericArg::Base(ctor_a), ty::GenericArg::Ty(ty_b)) => {
                self.ty_infer_from_bty(ctor_a.as_bty_skipping_binder(), ty_b);
            }
            (rty::GenericArg::Ty(ty_a), ty::GenericArg::Ty(ty_b)) => {
                self.ty_infer_from_ty(ty_a, ty_b);
            }
            (rty::GenericArg::Lifetime(re_a), ty::GenericArg::Lifetime(re_b)) => {
                self.infer_from_region(*re_a, *re_b);
            }
            _ => {}
        }
    }
}

impl RegionSubst {
    fn rty_infer_from_fn_sig(&mut self, a: &rty::FnSig, b: &rty::FnSig) {
        debug_assert_eq!(a.inputs().len(), b.inputs().len());
        for (ty_a, ty_b) in iter::zip(a.inputs(), b.inputs()) {
            self.rty_infer_from_ty(ty_a, ty_b);
        }
        self.rty_infer_from_ty(
            &a.output().skip_binder_ref().ret,
            &b.output().skip_binder_ref().ret,
        );
    }

    fn rty_infer_from_ty(&mut self, a: &rty::Ty, b: &rty::Ty) {
        match (a.kind(), b.kind()) {
            (rty::TyKind::Exists(ctor_a), _) => {
                self.rty_infer_from_ty(ctor_a.skip_binder_ref(), b);
            }
            (_, rty::TyKind::Exists(ctor_b)) => {
                self.rty_infer_from_ty(a, ctor_b.skip_binder_ref());
            }
            (rty::TyKind::Constr(_, ty_a), _) => self.rty_infer_from_ty(ty_a, b),
            (_, rty::TyKind::Constr(_, ty_b)) => self.rty_infer_from_ty(a, ty_b),
            (rty::TyKind::Indexed(bty_a, _), rty::TyKind::Indexed(bty_b, _)) => {
                self.rty_infer_from_bty(bty_a, bty_b);
            }
            (rty::TyKind::StrgRef(re_a, _, ty_a), rty::TyKind::StrgRef(re_b, _, ty_b)) => {
                self.infer_from_region(*re_a, *re_b);
                self.rty_infer_from_ty(ty_a, ty_b);
            }
            _ => {}
        }
    }

    fn rty_infer_from_bty(&mut self, a: &rty::BaseTy, b: &rty::BaseTy) {
        match (a, b) {
            (rty::BaseTy::Slice(ty_a), rty::BaseTy::Slice(ty_b)) => {
                self.rty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Adt(adt_def_a, args_a), rty::BaseTy::Adt(adt_def_b, args_b)) => {
                debug_assert_eq!(adt_def_a.did(), adt_def_b.did());
                for (arg_a, arg_b) in iter::zip(args_a, args_b) {
                    self.rty_infer_from_generic_arg(arg_a, arg_b);
                }
            }
            (rty::BaseTy::RawPtr(ty_a, mutbl_a), rty::BaseTy::RawPtr(ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.rty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Ref(re_a, ty_a, mutbl_a), rty::BaseTy::Ref(re_b, ty_b, mutbl_b)) => {
                debug_assert_eq!(mutbl_a, mutbl_b);
                self.infer_from_region(*re_a, *re_b);
                self.rty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::FnPtr(poly_sig_a), rty::BaseTy::FnPtr(poly_sig_b)) => {
                self.rty_infer_from_fn_sig(
                    poly_sig_a.skip_binder_ref(),
                    poly_sig_b.skip_binder_ref(),
                );
            }
            (rty::BaseTy::Tuple(tys_a), rty::BaseTy::Tuple(tys_b)) => {
                for (ty_a, ty_b) in iter::zip(tys_a, tys_b) {
                    self.rty_infer_from_ty(ty_a, ty_b);
                }
            }
            (rty::BaseTy::Alias(_, aty_a), rty::BaseTy::Alias(_, aty_b)) => {
                for (arg_a, arg_b) in iter::zip(&aty_a.args, &aty_b.args) {
                    self.rty_infer_from_generic_arg(arg_a, arg_b);
                }
            }
            (rty::BaseTy::Array(ty_a, _), rty::BaseTy::Array(ty_b, _)) => {
                self.rty_infer_from_ty(ty_a, ty_b);
            }
            (rty::BaseTy::Dynamic(preds_a, re_a), rty::BaseTy::Dynamic(preds_b, re_b)) => {
                for (pred_a, pred_b) in iter::zip(preds_a, preds_b) {
                    self.rty_infer_from_existential_pred(pred_a, pred_b);
                }
                self.infer_from_region(*re_a, *re_b);
            }
            _ => {}
        }
    }

    fn rty_infer_from_generic_arg(&mut self, a: &rty::GenericArg, b: &rty::GenericArg) {
        match (a, b) {
            (rty::GenericArg::Ty(ty_a), rty::GenericArg::Ty(ty_b)) => {
                self.rty_infer_from_ty(ty_a, ty_b);
            }
            (rty::GenericArg::Base(ctor_a), rty::GenericArg::Base(ctor_b)) => {
                self.rty_infer_from_bty(
                    ctor_a.as_bty_skipping_binder(),
                    ctor_b.as_bty_skipping_binder(),
                );
            }
            (rty::GenericArg::Lifetime(re_a), rty::GenericArg::Lifetime(re_b)) => {
                self.infer_from_region(*re_a, *re_b);
            }
            _ => {}
        }
    }

    fn rty_infer_from_existential_pred(
        &mut self,
        a: &rty::Binder<rty::ExistentialPredicate>,
        b: &rty::Binder<rty::ExistentialPredicate>,
    ) {
        match (a.skip_binder_ref(), b.skip_binder_ref()) {
            (
                rty::ExistentialPredicate::Trait(trait_ref_a),
                rty::ExistentialPredicate::Trait(trait_ref_b),
            ) => {
                debug_assert_eq!(trait_ref_a.def_id, trait_ref_b.def_id);
                for (arg_a, arg_b) in iter::zip(&trait_ref_a.args, &trait_ref_b.args) {
                    self.rty_infer_from_generic_arg(arg_a, arg_b);
                }
            }
            (
                rty::ExistentialPredicate::Projection(proj_a),
                rty::ExistentialPredicate::Projection(proj_b),
            ) => {
                debug_assert_eq!(proj_a.def_id, proj_b.def_id);
                for (arg_a, arg_b) in iter::zip(&proj_a.args, &proj_b.args) {
                    self.rty_infer_from_generic_arg(arg_a, arg_b);
                }
                self.rty_infer_from_bty(
                    proj_a.term.as_bty_skipping_binder(),
                    proj_b.term.as_bty_skipping_binder(),
                );
            }
            _ => {}
        }
    }
}
