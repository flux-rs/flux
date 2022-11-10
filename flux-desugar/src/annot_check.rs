use std::{collections::HashMap, iter};

use flux_common::iter::IterExt;
use flux_errors::{ErrorGuaranteed, FluxSession, ResultExt};
use flux_middle::rustc::{
    lowering,
    ty::{self as rustc_ty, Mutability},
};
use flux_syntax::surface::{
    Arg, EnumDef, FnSig, Ident, Path, RefKind, Res, StructDef, Ty, TyKind, VariantDef,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol};

pub fn check_struct_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    struct_def: &StructDef<Res>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = struct_def.def_id.to_def_id();
    let rust_adt_def = lowering::lower_adt_def(tcx, sess, tcx.adt_def(def_id))?;
    let rust_variant_def = &rust_adt_def.variants[0];
    iter::zip(&struct_def.fields, rust_variant_def.fields()).try_for_each_exhaust(
        |(ty, (rust_ty, field_def_id))| {
            if let Some(ty) = ty {
                ZipChecker::new(tcx, sess, *field_def_id).zip_ty(ty, rust_ty)?
            }
            Ok(())
        },
    )
}

pub fn check_enum_def(
    tcx: TyCtxt,
    sess: &FluxSession,
    enum_def: &EnumDef<Res>,
) -> Result<(), ErrorGuaranteed> {
    let def_id = enum_def.def_id.to_def_id();
    let rust_adt_def = lowering::lower_adt_def(tcx, sess, tcx.adt_def(def_id))?;

    iter::zip(&enum_def.variants, &rust_adt_def.variants).try_for_each_exhaust(
        |(variant, rust_variant)| {
            ZipChecker::new(tcx, sess, rust_variant.def_id).zip_variant_def(variant, rust_variant)
        },
    )
}

pub fn check_fn_sig(
    tcx: TyCtxt,
    sess: &FluxSession,
    def_id: DefId,
    fn_sig: &FnSig<Res>,
) -> Result<(), ErrorGuaranteed> {
    let rust_sig = lowering::lower_fn_sig_of(tcx, def_id).emit(sess)?;
    let rust_sig = rust_sig.as_ref().skip_binder();

    let ck = ZipChecker::new(tcx, sess, def_id);
    let mut locs = Locs::new();
    ck.zip_args(&fn_sig.args, rust_sig.inputs(), fn_sig.span, &mut locs)?;
    ck.zip_return_ty(fn_sig.span, &fn_sig.returns, &rust_sig.output())?;
    ck.zip_ty_locs(&fn_sig.ensures, &locs)
}

struct ZipChecker<'genv, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'genv FluxSession,
    /// DefId of the definition being checked, this could either be a field on a struct,
    /// a variant on a enum, or a function.
    def_id: DefId,
}

type Locs = HashMap<Symbol, rustc_ty::Ty>;

impl<'genv, 'tcx> ZipChecker<'genv, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'genv FluxSession, def_id: DefId) -> Self {
        ZipChecker { tcx, sess, def_id }
    }

    fn zip_variant_def(
        &self,
        variant_def: &VariantDef<Res>,
        rust_variant_def: &rustc_ty::VariantDef,
    ) -> Result<(), ErrorGuaranteed> {
        let flux_fields = variant_def.fields.len();
        let rust_fields = rust_variant_def.field_tys.len();
        if flux_fields != rust_fields {
            return Err(self.sess.emit_err(errors::FieldCountMismatch::new(
                variant_def.span,
                flux_fields,
                self.tcx.def_span(rust_variant_def.def_id),
                rust_fields,
            )));
        }
        iter::zip(&variant_def.fields, rust_variant_def.field_tys.iter())
            .try_for_each_exhaust(|(ty, rust_ty)| self.zip_ty(ty, rust_ty))?;

        self.zip_path(&variant_def.ret.path, &rust_variant_def.ret)
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
                Err(self.sess.emit_err(errors::DefaultReturnMismatch::new(
                    self.tcx,
                    span,
                    rust_ty,
                    self.def_id,
                )))
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
        locs: &mut Locs,
    ) -> Result<(), ErrorGuaranteed> {
        let rust_args = rust_tys.len();
        let flux_args = binds.len();
        if rust_args != flux_args {
            return Err(self.sess.emit_err(errors::ArgCountMismatch::new(
                flux_span,
                flux_args,
                self.tcx.def_span(self.def_id),
                rust_args,
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
            (Arg::Ty(_, ty), _) => self.zip_ty(ty, rust_ty),
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
            (TyKind::Array(ty, _), rustc_ty::TyKind::Array(rust_ty, _)) => self.zip_ty(ty, rust_ty),
            (TyKind::Slice(ty), rustc_ty::TyKind::Slice(rust_ty)) => self.zip_ty(ty, rust_ty),
            (TyKind::Tuple(tys), rustc_ty::TyKind::Tuple(rust_tys))
                if tys.len() == rust_tys.len() =>
            {
                iter::zip(tys, rust_tys)
                    .try_for_each_exhaust(|(ty, rust_ty)| self.zip_ty(ty, rust_ty))?;
                Ok(())
            }
            _ => {
                Err(self.sess.emit_err(errors::InvalidRefinement::new(
                    self.tcx,
                    ty.span,
                    rust_ty,
                    self.def_id,
                )))
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
                    Err(self.sess.emit_err(errors::TooFewArgs::new(
                        self.tcx, path.span, found, min_args, *def_id1,
                    )))
                } else if found > max_args {
                    Err(self.sess.emit_err(errors::TooManyArgs::new(
                        self.tcx, path.span, found, max_args, *def_id1,
                    )))
                } else {
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
                Err(self.sess.emit_err(errors::PathMismatch::new(
                    self.tcx,
                    rust_ty,
                    path.span,
                    self.def_id,
                )))
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
                Err(self.sess.emit_err(errors::MutabilityMismatch::new(
                    self.tcx,
                    span,
                    self.def_id,
                )))
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
    use flux_macros::{Diagnostic, Subdiagnostic};
    use flux_middle::rustc::ty as rustc_ty;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span};

    #[derive(Diagnostic)]
    #[diag(annot_check::field_count_mismatch, code = "FLUX")]
    pub struct FieldCountMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        flux_fields: usize,
        #[label(annot_check::rust_label)]
        rust_span: Span,
        rust_fields: usize,
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
    #[diag(annot_check::arg_count_mismatch, code = "FLUX")]
    pub struct ArgCountMismatch {
        #[primary_span]
        #[label]
        flux_span: Span,
        flux_args: usize,
        #[label(annot_check::rust_label)]
        rust_span: Span,
        rust_args: usize,
    }

    impl ArgCountMismatch {
        pub fn new(flux_span: Span, flux_args: usize, rust_span: Span, rust_args: usize) -> Self {
            Self { flux_span, flux_args, rust_args, rust_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::path_mismatch, code = "FLUX")]
    pub struct PathMismatch {
        #[primary_span]
        #[label]
        span: Span,
        rust_type: String,
        flux_type: String,
        #[subdiagnostic]
        def: InvalidRefinementForDef,
    }

    impl PathMismatch {
        pub fn new(tcx: TyCtxt, rust_ty: &rustc_ty::Ty, flux_ty_span: Span, def_id: DefId) -> Self {
            let def = InvalidRefinementForDef::new(tcx, def_id);
            let flux_type = tcx
                .sess
                .source_map()
                .span_to_snippet(flux_ty_span)
                .unwrap_or_else(|_| "{unknown}".to_string());
            let rust_type = format!("{rust_ty:?}");
            Self { span: flux_ty_span, rust_type, flux_type, def }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::invalid_refinement, code = "FLUX")]
    pub struct InvalidRefinement {
        #[primary_span]
        #[label]
        span: Span,
        rust_type: String,
        #[subdiagnostic]
        def: InvalidRefinementForDef,
    }

    impl InvalidRefinement {
        pub fn new(tcx: TyCtxt, flux_ty_span: Span, rust_ty: &rustc_ty::Ty, def_id: DefId) -> Self {
            let def = InvalidRefinementForDef::new(tcx, def_id);
            let rust_type = format!("{rust_ty:?}");
            Self { span: flux_ty_span, rust_type, def }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::mutability_mismatch, code = "FLUX")]
    pub struct MutabilityMismatch {
        #[primary_span]
        #[label]
        span: Span,
        #[subdiagnostic]
        def: InvalidRefinementForDef,
    }

    impl MutabilityMismatch {
        pub fn new(tcx: TyCtxt, span: Span, def_id: DefId) -> Self {
            let def = InvalidRefinementForDef::new(tcx, def_id);
            Self { span, def }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::default_return_mismatch, code = "FLUX")]
    pub struct DefaultReturnMismatch {
        #[primary_span]
        #[label]
        span: Span,
        rust_type: String,
        #[subdiagnostic]
        def: InvalidRefinementForDef,
    }

    impl DefaultReturnMismatch {
        pub fn new(tcx: TyCtxt, span: Span, rust_ty: &rustc_ty::Ty, def_id: DefId) -> Self {
            let def = InvalidRefinementForDef::new(tcx, def_id);
            let rust_type = format!("{rust_ty:?}");
            Self { span, rust_type, def }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::unresolved_location, code = "FLUX")]
    pub struct UnresolvedLocation {
        #[primary_span]
        #[label]
        span: Span,
        loc: Ident,
    }

    impl UnresolvedLocation {
        pub fn new(ident: Ident) -> Self {
            Self { span: ident.span, loc: ident }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::too_few_arguments, code = "FLUX")]
    pub struct TooFewArgs {
        #[primary_span]
        #[label]
        pub span: Span,
        pub found: usize,
        pub min: usize,
        #[subdiagnostic]
        def: DefinitionSpanNote,
    }

    impl TooFewArgs {
        pub fn new(tcx: TyCtxt, span: Span, found: usize, min: usize, def_id: DefId) -> Self {
            let def = DefinitionSpanNote::new(tcx, def_id);
            Self { span, found, min, def }
        }
    }

    #[derive(Diagnostic)]
    #[diag(annot_check::too_many_arguments, code = "FLUX")]
    pub struct TooManyArgs {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        max: usize,
        #[subdiagnostic]
        def: DefinitionSpanNote,
    }

    impl TooManyArgs {
        pub fn new(tcx: TyCtxt, span: Span, found: usize, max: usize, def_id: DefId) -> Self {
            let def = DefinitionSpanNote::new(tcx, def_id);
            Self { span, found, max, def }
        }
    }

    #[derive(Subdiagnostic)]
    #[label(annot_check::invalid_refinement_for_def)]
    struct InvalidRefinementForDef {
        #[primary_span]
        span: Span,
        def_kind: &'static str,
    }

    impl InvalidRefinementForDef {
        fn new(tcx: TyCtxt, def_id: DefId) -> Self {
            let span = tcx
                .def_ident_span(def_id)
                .unwrap_or_else(|| tcx.def_span(def_id));
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            Self { span, def_kind }
        }
    }

    #[derive(Subdiagnostic)]
    #[note(annot_check::definition_span_note)]
    struct DefinitionSpanNote {
        #[primary_span]
        span: Span,
        def_kind: &'static str,
    }

    impl DefinitionSpanNote {
        fn new(tcx: TyCtxt, def_id: DefId) -> Self {
            let span = tcx
                .def_ident_span(def_id)
                .unwrap_or_else(|| tcx.def_span(def_id));
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            Self { span, def_kind }
        }
    }
}
