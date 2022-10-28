use std::{collections::HashMap, iter};

use flux_common::iter::IterExt;
use flux_errors::{ErrorGuaranteed, FluxSession};
use flux_middle::rustc::ty::{self as rustc_ty, Mutability};
use flux_syntax::surface::{
    Arg, EnumDef, FnSig, Ident, Path, RefKind, Res, StructDef, Ty, TyKind, VariantDef,
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

    pub fn zip_struct_def(
        &self,
        struct_def: &StructDef<Res>,
        rust_adt_def: &rustc_ty::AdtDef,
    ) -> Result<(), ErrorGuaranteed> {
        let rust_variant_def = &rust_adt_def.variants[0];
        iter::zip(&struct_def.fields, rust_variant_def.fields.iter()).try_for_each_exhaust(
            |(ty, rust_ty)| {
                if let Some(ty) = ty {
                    self.zip_ty(ty, rust_ty)?
                }
                Ok(())
            },
        )
    }

    pub fn zip_enum_def(
        &self,
        enum_def: &EnumDef<Res>,
        rust_adt_def: &rustc_ty::AdtDef,
    ) -> Result<(), ErrorGuaranteed> {
        iter::zip(&enum_def.variants, &rust_adt_def.variants).try_for_each_exhaust(
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
                flux_fields,
                self.tcx.def_span(rust_variant_def.def_id),
                rust_fields,
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
        rust_sig: &rustc_ty::PolyFnSig,
        def_span: Span,
    ) -> Result<(), ErrorGuaranteed> {
        let rust_sig = rust_sig.as_ref().skip_binder();
        let mut locs = Locs::new();
        self.zip_args(&sig.args, rust_sig.inputs(), sig.span, def_span, &mut locs)?;
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
        binds: &[Arg<Res>],
        rust_tys: &[rustc_ty::Ty],
        flux_span: Span,
        def_span: Span,
        locs: &mut Locs,
    ) -> Result<(), ErrorGuaranteed> {
        let rust_args = rust_tys.len();
        let flux_args = binds.len();
        if rust_args != flux_args {
            return Err(self.sess.emit_err(errors::ArgCountMismatch::new(
                flux_span, flux_args, def_span, rust_args,
            )));
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
        match (&path.ident, rust_ty.kind()) {
            (Res::Adt(def_id1), rustc_ty::TyKind::Adt(def_id2, substs)) if def_id1 == def_id2 => {
                let generics = self.tcx.generics_of(def_id1);
                let max_args = generics.own_counts().types;
                let default_args = generics.own_defaults().types;
                let min_args = max_args - default_args;

                let found = path.args.len();
                if found < min_args {
                    Err(self
                        .sess
                        .emit_err(errors::TooFewArgs::new(path.span, found, min_args)))
                } else if found > max_args {
                    Err(self
                        .sess
                        .emit_err(errors::TooManyArgs::new(path.span, found, max_args)))
                } else {
                    // zip the supplied args
                    self.zip_generic_args(&path.args, substs)
                }
            }
            (Res::Uint(uint_ty1), rustc_ty::TyKind::Uint(uint_ty2)) if uint_ty1 == uint_ty2 => {
                Ok(())
            }
            (Res::Bool, rustc_ty::TyKind::Bool) => Ok(()),
            (Res::Float(float_ty1), rustc_ty::TyKind::Float(float_ty2))
                if float_ty1 == float_ty2 =>
            {
                Ok(())
            }
            (Res::Int(int_ty1), rustc_ty::TyKind::Int(int_ty2)) if int_ty1 == int_ty2 => Ok(()),
            (Res::Param(param_ty1), rustc_ty::TyKind::Param(param_ty2))
                if param_ty1 == param_ty2 =>
            {
                Ok(())
            }
            (Res::Str, rustc_ty::TyKind::Str) => Ok(()),
            (Res::Char, rustc_ty::TyKind::Char) => Ok(()),
            _ => {
                Err(self
                    .sess
                    .emit_err(errors::TypeMismatch::from_span(self.tcx, rust_ty, path.span)))
            }
        }
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

    fn zip_generic_args(
        &self,
        args: &[Ty<Res>],
        rust_args: &[rustc_ty::GenericArg],
    ) -> Result<(), ErrorGuaranteed> {
        let rust_args = rust_args.iter().filter_map(|rust_arg| {
            match rust_arg {
                rustc_ty::GenericArg::Ty(ty) => Some(ty),
                rustc_ty::GenericArg::Lifetime(_) => None,
            }
        });
        iter::zip(args, rust_args)
            .into_iter()
            .try_for_each_exhaust(|(arg, rust_arg)| self.zip_ty(arg, rust_arg))
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::rustc::ty::{self as rustc_ty, Mutability};
    use flux_syntax::surface::RefKind;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span};

    #[derive(Diagnostic)]
    #[diag(resolver::field_count_mismatch, code = "FLUX")]
    pub struct FieldCountMismatch {
        #[primary_span]
        #[label]
        pub flux_span: Span,
        pub flux_fields: usize,
        #[label(resolver::rust_label)]
        pub rust_span: Span,
        pub rust_fields: usize,
    }

    impl FieldCountMismatch {
        pub fn new(
            flux_span: Span,
            flux_fields: usize,
            rust_span: Span,
            rust_fields: usize,
        ) -> Self {
            Self { flux_span, flux_fields, rust_span, rust_fields }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::arg_count_mismatch, code = "FLUX")]
    pub struct ArgCountMismatch {
        #[primary_span]
        #[label]
        pub flux_span: Span,
        pub flux_args: usize,
        #[label(resolver::rust_label)]
        pub rust_span: Span,
        pub rust_args: usize,
    }

    impl ArgCountMismatch {
        pub fn new(flux_span: Span, flux_args: usize, rust_span: Span, rust_args: usize) -> Self {
            Self { flux_span, flux_args, rust_args, rust_span }
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

    #[derive(Diagnostic)]
    #[diag(resolver::too_few_arguments, code = "FLUX")]
    pub struct TooFewArgs {
        #[primary_span]
        pub span: Span,
        pub found: usize,
        pub min: usize,
    }

    impl TooFewArgs {
        pub fn new(span: Span, found: usize, min: usize) -> Self {
            Self { span, found, min }
        }
    }

    #[derive(Diagnostic)]
    #[diag(resolver::too_many_arguments, code = "FLUX")]
    pub struct TooManyArgs {
        #[primary_span]
        pub span: Span,
        pub found: usize,
        pub max: usize,
    }

    impl TooManyArgs {
        pub fn new(span: Span, found: usize, max: usize) -> Self {
            Self { span, found, max }
        }
    }
}
