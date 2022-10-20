use std::{collections::HashMap, iter};

use flux_common::iter::IterExt;
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::rustc::ty::{self as rustc_ty, Mutability};
use flux_syntax::surface::{
    Arg, EnumDef, FnSig, Ident, Path, RefKind, Res, Ty, TyKind, VariantDef,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol};

type Locs = HashMap<Symbol, rustc_ty::Ty>;

pub struct ZipChecker<'genv, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'genv FluxSession,
}

impl<'genv, 'tcx> ZipChecker<'genv, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'genv FluxSession) -> Self {
        ZipChecker { tcx, sess }
    }

    pub fn zip_enum_def(
        &self,
        enum_def: &EnumDef<Res>,
        rust_enum_def: &rustc_ty::EnumDef,
    ) -> Result<(), ErrorGuaranteed> {
        iter::zip(&enum_def.variants, &rust_enum_def.variants).try_for_each_exhaust(
            |(variant, rust_variant)| self.zip_variant_def(variant, rust_variant),
        )
    }

    fn zip_variant_def(
        &self,
        variant_def: &VariantDef<Res>,
        rust_variant_def: &rustc_ty::VariantDef,
    ) -> Result<(), ErrorGuaranteed> {
        let flux_fields = variant_def.fields.len();
        let rust_fields = rust_variant_def.fields.len();
        if flux_fields != rust_fields {
            return Err(self.sess.emit_err(errors::FieldCountMismatch::new(
                variant_def.span,
                rust_fields,
                flux_fields,
            )));
        }
        iter::zip(&variant_def.fields, rust_variant_def.fields.iter())
            .try_for_each_exhaust(|(ty, rust_ty)| self.zip_ty(ty, rust_ty))?;

        self.zip_path(&variant_def.ret.path, &rust_variant_def.ret)
    }

    /// `zip_fn_sig(b_sig, d_sig)` combines the refinements of the `b_sig` and the resolved elements
    /// of the (trivial/default) `dsig:DefFnSig` to compute a (refined) `DefFnSig`
    pub fn zip_fn_sig(
        &self,
        sig: &FnSig<Res>,
        rust_sig: &rustc_ty::FnSig,
    ) -> Result<(), ErrorGuaranteed> {
        let mut locs = Locs::new();
        self.zip_args(sig.span, &sig.args, rust_sig.inputs(), &mut locs)?;
        self.zip_return_ty(sig.span, &sig.returns, &rust_sig.output())?;
        self.zip_ty_locs(&sig.ensures, &locs)
    }

    fn zip_return_ty(
        &self,
        span: Span,
        ty: &Option<Ty<Res>>,
        rust_ty: &rustc_ty::Ty,
    ) -> Result<(), ErrorGuaranteed> {
        match (ty, rust_ty.kind()) {
            (Some(ty), _) => self.zip_ty(ty, rust_ty),
            (None, rustc_ty::TyKind::Tuple(tys)) if tys.is_empty() => Ok(()),
            (_, _) => {
                Err(self.sess.emit_err(errors::DefaultReturnMismatch {
                    span,
                    rust_type: format!("{rust_ty:?}"),
                }))
            }
        }
    }

    /// `zip_ty_locs` traverses the bare-outputs and zips with the location-types saved in `locs`
    fn zip_ty_locs(
        &self,
        bindings: &[(Ident, Ty<Res>)],
        locs: &Locs,
    ) -> Result<(), ErrorGuaranteed> {
        for (ident, ty) in bindings {
            if let Some(rust_ty) = locs.get(&ident.name) {
                self.zip_ty(ty, rust_ty)?;
            } else {
                return Err(self.sess.emit_err(errors::UnresolvedLocation::new(*ident)));
            }
        }
        Ok(())
    }

    /// `zip_ty_binds` traverses the inputs `bs` and `ds` and
    /// saves the types of the references in `locs`
    fn zip_args(
        &self,
        span: Span,
        binds: &[Arg<Res>],
        rust_tys: &[rustc_ty::Ty],
        locs: &mut Locs,
    ) -> Result<(), ErrorGuaranteed> {
        let rust_args = rust_tys.len();
        let flux_args = binds.len();
        if rust_args != flux_args {
            return Err(self
                .sess
                .emit_err(errors::ArgCountMismatch::new(span, rust_args, flux_args)));
        }

        iter::zip(binds, rust_tys).try_for_each_exhaust(|(arg, rust_ty)| {
            self.zip_arg(arg, rust_ty)?;
            if let (Arg::StrgRef(bind, _), rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut)) =
                (arg, rust_ty.kind())
            {
                locs.insert(bind.name, rust_ty.clone());
            }
            Ok(())
        })
    }

    fn zip_arg(&self, arg: &Arg<Res>, rust_ty: &rustc_ty::Ty) -> Result<(), ErrorGuaranteed> {
        match (arg, rust_ty.kind()) {
            (Arg::Ty(ty), _) => self.zip_ty(ty, rust_ty),
            (Arg::Constr(_, path, _), _) => self.zip_path(path, rust_ty),
            (Arg::StrgRef(_, ty), rustc_ty::TyKind::Ref(rust_ty, Mutability::Mut)) => {
                self.zip_ty(ty, rust_ty)
            }
            _ => panic!("incompatible types `{rust_ty:?}`"),
        }
    }

    fn zip_ty(&self, ty: &Ty<Res>, rust_ty: &rustc_ty::Ty) -> Result<(), ErrorGuaranteed> {
        match (&ty.kind, rust_ty.kind()) {
            (TyKind::Path(path), _) => self.zip_path(path, rust_ty),
            (TyKind::Indexed { path, .. }, _) => self.zip_path(path, rust_ty),
            (TyKind::Exists { path, .. }, _) => self.zip_path(path, rust_ty),
            (TyKind::Constr(_, ty), _) => self.zip_ty(ty, rust_ty),
            (TyKind::Ref(rk, ref_ty), rustc_ty::TyKind::Ref(rust_ty, mutability)) => {
                self.zip_ty(ref_ty, rust_ty)?;
                self.zip_mutability(ty.span, *rk, *mutability)
            }
            (TyKind::Unit, rustc_ty::TyKind::Tuple(tys)) if tys.is_empty() => Ok(()),
            (TyKind::Array(ty, _), rustc_ty::TyKind::Array(rust_ty, _)) => self.zip_ty(ty, rust_ty),
            (TyKind::Slice(ty), rustc_ty::TyKind::Slice(rust_ty)) => self.zip_ty(ty, rust_ty),
            _ => {
                Err(self
                    .sess
                    .emit_err(errors::TypeMismatch::from_span(self.tcx, rust_ty, ty.span)))
            }
        }
    }

    fn zip_path(&self, path: &Path<Res>, rust_ty: &rustc_ty::Ty) -> Result<(), ErrorGuaranteed> {
        let (res, rust_args) = match rust_ty.kind() {
            rustc_ty::TyKind::Adt(def_id, substs) => (Res::Adt(*def_id), &substs[..]),
            rustc_ty::TyKind::Uint(uint_ty) => (Res::Uint(*uint_ty), [].as_slice()),
            rustc_ty::TyKind::Bool => (Res::Bool, [].as_slice()),
            rustc_ty::TyKind::Float(float_ty) => (Res::Float(*float_ty), [].as_slice()),
            rustc_ty::TyKind::Int(int_ty) => (Res::Int(*int_ty), [].as_slice()),
            rustc_ty::TyKind::Param(param_ty) => (Res::Param(*param_ty), [].as_slice()),
            rustc_ty::TyKind::Str => (Res::Str, [].as_slice()),

            rustc_ty::TyKind::Array(_, _)
            | rustc_ty::TyKind::Never
            | rustc_ty::TyKind::Ref(_, _)
            | rustc_ty::TyKind::Tuple(_)
            | rustc_ty::TyKind::Slice(_) => {
                return Err(self
                    .sess
                    .emit_err(errors::TypeMismatch::from_span(self.tcx, rust_ty, path.span)))
            }
        };

        if path.ident != res {
            return Err(self
                .sess
                .emit_err(errors::TypeMismatch::from_span(self.tcx, rust_ty, path.span)));
        }

        let path_args_len = path.args.len();
        // Assume that the rust_args are of the form [path_args + default_args]
        // i.e. default args all come _after_ the supplied path_args.
        let rust_args_len = rust_args.len();
        let default_args_len = rust_args_len - path_args_len;
        assert!(default_args_len <= rust_args_len);

        // zip the supplied args
        iter::zip(&path.args, rust_args)
            .try_for_each_exhaust(|(arg, rust_arg)| self.zip_generic_arg(arg, rust_arg))
    }

    fn zip_mutability(
        &self,
        span: Span,
        ref_kind: RefKind,
        mutability: rustc_ty::Mutability,
    ) -> Result<(), ErrorGuaranteed> {
        match (ref_kind, mutability) {
            (RefKind::Mut, Mutability::Mut) => Ok(()),
            (RefKind::Shr, Mutability::Not) => Ok(()),
            _ => {
                Err(self
                    .sess
                    .emit_err(errors::RefKindMismatch::new(span, ref_kind, mutability)))
            }
        }
    }

    fn zip_generic_arg(
        &self,
        arg: &Ty<Res>,
        rust_arg: &rustc_ty::GenericArg,
    ) -> Result<(), ErrorGuaranteed> {
        match rust_arg {
            rustc_ty::GenericArg::Ty(ty) => self.zip_ty(arg, ty),
        }
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::rustc::ty::{self as rustc_ty, Mutability};
    use flux_syntax::surface::RefKind;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span};

    #[derive(Diagnostic)]
    #[diag(resolver::mismatched_fields, code = "FLUX")]
    pub struct FieldCountMismatch {
        #[primary_span]
        pub span: Span,
        pub rust_fields: usize,
        pub flux_fields: usize,
    }

    impl FieldCountMismatch {
        pub fn new(span: Span, rust_fields: usize, flux_fields: usize) -> Self {
            Self { span, rust_fields, flux_fields }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::mismatched_args, code = "FLUX")]
    pub struct ArgCountMismatch {
        #[primary_span]
        pub span: Span,
        pub rust_args: usize,
        pub flux_args: usize,
    }

    impl ArgCountMismatch {
        pub fn new(span: Span, rust_args: usize, flux_args: usize) -> Self {
            Self { span, rust_args, flux_args }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::mismatched_type, code = "FLUX")]
    pub struct TypeMismatch {
        #[primary_span]
        #[label]
        pub span: Span,
        pub rust_type: String,
        pub flux_type: String,
    }

    impl TypeMismatch {
        pub fn from_span(tcx: TyCtxt, rust_ty: &rustc_ty::Ty, flux_ty_span: Span) -> Self {
            let flux_type = tcx
                .sess
                .source_map()
                .span_to_snippet(flux_ty_span)
                .unwrap_or_else(|_| "{unknown}".to_string());
            let rust_type = format!("{rust_ty:?}");
            Self { span: flux_ty_span, rust_type, flux_type }
        }

        // pub fn from_ident(rust_ty: &rustc_ty::Ty, flux_type: Ident) -> Self {
        //     let span = flux_type.span;
        //     let flux_type = format!("{flux_type}");
        //     let rust_type = format!("{rust_ty:?}");
        //     Self { span, rust_type, flux_type }
        // }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::mutability_mismatch, code = "FLUX")]
    pub struct RefKindMismatch {
        #[primary_span]
        pub span: Span,
        pub flux_ref: &'static str,
        pub rust_ref: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(resolver::default_return_mismatch, code = "FLUX")]
    pub struct DefaultReturnMismatch {
        #[primary_span]
        pub span: Span,
        pub rust_type: String,
    }

    impl RefKindMismatch {
        pub fn new(span: Span, ref_kind: RefKind, mutability: Mutability) -> Self {
            Self {
                span,
                flux_ref: match ref_kind {
                    RefKind::Mut => "&mut",
                    RefKind::Shr => "&",
                },
                rust_ref: match mutability {
                    Mutability::Mut => "&mut",
                    Mutability::Not => "&",
                },
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::unresolved_location, code = "FLUX")]
    pub struct UnresolvedLocation {
        #[primary_span]
        #[label]
        pub span: Span,
        pub loc: Ident,
    }

    impl UnresolvedLocation {
        pub fn new(ident: Ident) -> Self {
            Self { span: ident.span, loc: ident }
        }
    }
}
