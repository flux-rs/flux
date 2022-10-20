use std::{collections::HashMap, iter};

use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::rustc::ty::{self as rustc_ty, Mutability};
use flux_syntax::surface::{
    Arg, EnumDef, FnSig, Ident, Path, RefKind, Res, Ty, TyKind, VariantDef, VariantRet,
};
use itertools::Itertools;
use rustc_span::{Span, Symbol};

use crate::table_resolver::{
    errors::{
        ArgCountMismatch, DefaultReturnMismatch, FieldCountMismatch, RefKindMismatch, TypeMismatch,
        UnresolvedLocation,
    },
    Resolver,
};

type Locs = HashMap<Symbol, rustc_ty::Ty>;

pub struct ZipResolver<'genv, 'tcx> {
    sess: &'genv FluxSession,
    resolver: &'genv Resolver<'genv, 'tcx>,
}

impl<'genv, 'tcx> ZipResolver<'genv, 'tcx> {
    pub fn new(sess: &'genv FluxSession, resolver: &'genv Resolver<'genv, 'tcx>) -> Self {
        ZipResolver { sess, resolver }
    }

    pub fn zip_enum_def(
        &self,
        enum_def: EnumDef,
        rust_enum_def: &rustc_ty::EnumDef,
    ) -> Result<EnumDef<Res>, ErrorGuaranteed> {
        let variants = iter::zip(enum_def.variants, &rust_enum_def.variants)
            .map(|(variant, rust_variant)| self.zip_variant_def(variant, rust_variant))
            .collect_vec();

        let variants: Result<Vec<VariantDef<Res>>, ErrorGuaranteed> =
            variants.into_iter().collect();

        let variants = variants?;

        Ok(EnumDef {
            def_id: enum_def.def_id,
            refined_by: enum_def.refined_by,
            invariants: enum_def.invariants,
            variants,
        })
    }

    fn zip_variant_def(
        &self,
        variant_def: VariantDef,
        rust_variant_def: &rustc_ty::VariantDef,
    ) -> Result<VariantDef<Res>, ErrorGuaranteed> {
        let flux_fields = variant_def.fields.len();
        let rust_fields = rust_variant_def.fields.len();
        if flux_fields != rust_fields {
            return Err(self.sess.emit_err(FieldCountMismatch::new(
                variant_def.span,
                rust_fields,
                flux_fields,
            )));
        }
        let fields = iter::zip(variant_def.fields, rust_variant_def.fields.iter())
            .map(|(ty, rust_ty)| self.zip_ty(ty, rust_ty))
            .collect_vec();
        let fields: Result<Vec<Ty<Res>>, ErrorGuaranteed> = fields.into_iter().collect();
        let fields = fields?;

        let ret = self.zip_variant_ret(variant_def.ret, &rust_variant_def.ret)?;
        Ok(VariantDef { fields, ret, span: variant_def.span })
    }

    fn zip_variant_ret(
        &self,
        ret: VariantRet,
        rust_ty: &rustc_ty::Ty,
    ) -> Result<VariantRet<Res>, ErrorGuaranteed> {
        let path = self.zip_path(ret.path, rust_ty)?;
        Ok(VariantRet { path, indices: ret.indices })
    }

    /// `zip_fn_sig(b_sig, d_sig)` combines the refinements of the `b_sig` and the resolved elements
    /// of the (trivial/default) `dsig:DefFnSig` to compute a (refined) `DefFnSig`
    pub fn zip_fn_sig(
        &self,
        sig: FnSig,
        rust_sig: &rustc_ty::FnSig,
    ) -> Result<FnSig<Res>, ErrorGuaranteed> {
        let mut locs = Locs::new();
        let args = self.zip_args(sig.span, sig.args, rust_sig.inputs(), &mut locs)?;

        Ok(FnSig {
            args,
            returns: self.zip_return_ty(sig.span, sig.returns, &rust_sig.output())?,
            ensures: self.zip_ty_locs(sig.ensures, &locs)?,
            requires: sig.requires,
            span: sig.span,
        })
    }

    fn zip_return_ty(
        &self,
        span: Span,
        ty: Option<Ty>,
        rust_ty: &rustc_ty::Ty,
    ) -> Result<Option<Ty<Res>>, ErrorGuaranteed> {
        let ty = match (ty, rust_ty.kind()) {
            (Some(ty), _) => Some(self.zip_ty(ty, rust_ty)?),
            (None, rustc_ty::TyKind::Tuple(tys)) if tys.is_empty() => None,
            (_, _) => {
                return Err(self
                    .sess
                    .emit_err(DefaultReturnMismatch { span, rust_type: format!("{rust_ty:?}") }))
            }
        };
        Ok(ty)
    }

    /// `zip_ty_locs` traverses the bare-outputs and zips with the location-types saved in `locs`
    fn zip_ty_locs(
        &self,
        bindings: Vec<(Ident, Ty)>,
        locs: &Locs,
    ) -> Result<Vec<(Ident, Ty<Res>)>, ErrorGuaranteed> {
        let mut res = vec![];
        for (ident, ty) in bindings {
            if let Some(rust_ty) = locs.get(&ident.name) {
                let dt = self.zip_ty(ty, rust_ty)?;
                res.push((ident, dt));
            } else {
                return Err(self.sess.emit_err(UnresolvedLocation::new(ident)));
            }
        }
        Ok(res)
    }

    /// `zip_ty_binds` traverses the inputs `bs` and `ds` and
    /// saves the types of the references in `locs`
    fn zip_args(
        &self,
        span: Span,
        binds: Vec<Arg>,
        rust_tys: &[rustc_ty::Ty],
        locs: &mut Locs,
    ) -> Result<Vec<Arg<Res>>, ErrorGuaranteed> {
        let rust_args = rust_tys.len();
        let flux_args = binds.len();
        if rust_args != flux_args {
            return Err(self
                .sess
                .emit_err(ArgCountMismatch::new(span, rust_args, flux_args)));
        }

        let binds = iter::zip(binds, rust_tys)
            .map(|(arg, rust_ty)| self.zip_arg(arg, rust_ty))
            .collect_vec();

        let binds: Result<Vec<Arg<Res>>, ErrorGuaranteed> = binds.into_iter().collect();

        match binds {
            Ok(binds) => {
                for (arg, rust_ty) in iter::zip(&binds, rust_tys) {
                    if let (
                        Arg::StrgRef(bind, _),
                        rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut),
                    ) = (arg, rust_ty.kind())
                    {
                        locs.insert(bind.name, rust_ty.clone());
                    }
                }
                Ok(binds)
            }
            Err(e) => Err(e),
        }
    }

    fn zip_arg(&self, arg: Arg, rust_ty: &rustc_ty::Ty) -> Result<Arg<Res>, ErrorGuaranteed> {
        match (arg, rust_ty.kind()) {
            (Arg::Ty(ty), _) => Ok(Arg::Ty(self.zip_ty(ty, rust_ty)?)),
            (Arg::Constr(bind, path, pred), _) => {
                Ok(Arg::Constr(bind, self.zip_path(path, rust_ty)?, pred))
            }
            (Arg::StrgRef(bind, ty), rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut)) => {
                Ok(Arg::StrgRef(bind, self.zip_ty(ty, rust_ty)?))
            }
            _ => panic!("incompatible types `{rust_ty:?}`"),
        }
    }

    fn zip_ty(&self, ty: Ty, rust_ty: &rustc_ty::Ty) -> Result<Ty<Res>, ErrorGuaranteed> {
        let kind = match (ty.kind, rust_ty.kind()) {
            (TyKind::Path(path), _) => TyKind::Path(self.zip_path(path, rust_ty)?),
            (TyKind::Indexed { path, indices }, _) => {
                TyKind::Indexed { path: self.zip_path(path, rust_ty)?, indices }
            }
            (TyKind::Exists { bind, path, pred }, _) => {
                TyKind::Exists { bind, path: self.zip_path(path, rust_ty)?, pred }
            }
            (TyKind::Constr(pred, ty), _) => {
                TyKind::Constr(pred, Box::new(self.zip_ty(*ty, rust_ty)?))
            }
            (TyKind::Ref(rk, ref_ty), rustc_ty::TyKind::Ref(rust_ty, mutability)) => {
                TyKind::Ref(
                    self.zip_mutability(ty.span, rk, *mutability)?,
                    Box::new(self.zip_ty(*ref_ty, rust_ty)?),
                )
            }
            (TyKind::Unit, rustc_ty::TyKind::Tuple(tys)) if tys.is_empty() => TyKind::Unit,
            (TyKind::Array(ty, len), rustc_ty::TyKind::Array(rust_ty, _)) => {
                TyKind::Array(Box::new(self.zip_ty(*ty, rust_ty)?), len)
            }
            (TyKind::Slice(ty), rustc_ty::TyKind::Slice(rust_ty)) => {
                TyKind::Slice(Box::new(self.zip_ty(*ty, rust_ty)?))
            }

            _ => panic!("incompatible types: `{rust_ty:?}`"),
        };
        Ok(Ty { kind, span: ty.span })
    }

    fn zip_path(&self, path: Path, rust_ty: &rustc_ty::Ty) -> Result<Path<Res>, ErrorGuaranteed> {
        let (res, rust_args) = match rust_ty.kind() {
            rustc_ty::TyKind::Adt(def_id, substs) => (Res::Adt(*def_id), &substs[..]),
            rustc_ty::TyKind::Uint(uint_ty) => (Res::Uint(*uint_ty), [].as_slice()),
            rustc_ty::TyKind::Bool => (Res::Bool, [].as_slice()),
            rustc_ty::TyKind::Float(float_ty) => (Res::Float(*float_ty), [].as_slice()),
            rustc_ty::TyKind::Int(int_ty) => (Res::Int(*int_ty), [].as_slice()),
            rustc_ty::TyKind::Param(param_ty) => (Res::Param(*param_ty), [].as_slice()),
            rustc_ty::TyKind::Str => todo!(),

            rustc_ty::TyKind::Array(_, _)
            | rustc_ty::TyKind::Never
            | rustc_ty::TyKind::Ref(_, _)
            | rustc_ty::TyKind::Tuple(_)
            | rustc_ty::TyKind::Slice(_) => {
                return Err(self.sess.emit_err(TypeMismatch::new(rust_ty, path.ident)))
            }
        };

        let path_res = self.resolver.resolve_ident(path.ident)?;
        if path_res != res {
            return Err(self.sess.emit_err(TypeMismatch::new(rust_ty, path.ident)));
        }

        let path_args_len = path.args.len();
        // Assume that the rust_args are of the form [path_args + default_args]
        // i.e. default args all come _after_ the supplied path_args.
        let rust_args_len = rust_args.len();
        let default_args_len = rust_args_len - path_args_len;
        assert!(default_args_len <= rust_args_len);

        // zip the supplied args
        let args = iter::zip(path.args, rust_args)
            .map(|(arg, rust_arg)| self.zip_generic_arg(arg, rust_arg))
            .collect_vec();

        match args.into_iter().collect() {
            Ok(args) => Ok(Path { ident: res, args, span: path.span }),
            Err(e) => Err(e),
        }
    }

    fn zip_mutability(
        &self,
        span: Span,
        ref_kind: RefKind,
        mutability: rustc_ty::Mutability,
    ) -> Result<RefKind, ErrorGuaranteed> {
        match (ref_kind, mutability) {
            (RefKind::Mut, Mutability::Mut) => Ok(RefKind::Mut),
            (RefKind::Shr, Mutability::Not) => Ok(RefKind::Shr),
            _ => {
                Err(self
                    .sess
                    .emit_err(RefKindMismatch::new(span, ref_kind, mutability)))
            }
        }
    }

    fn zip_generic_arg(
        &self,
        arg: Ty,
        rust_arg: &rustc_ty::GenericArg,
    ) -> Result<Ty<Res>, ErrorGuaranteed> {
        match rust_arg {
            rustc_ty::GenericArg::Ty(ty) => self.zip_ty(arg, ty),
        }
    }
}
