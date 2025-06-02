//! "Lift" HIR types into  FHIR types.

use flux_common::{bug, iter::IterExt, result::ErrorEmitter as _};
use flux_errors::ErrorGuaranteed;
use flux_middle::{
    def_id::MaybeExternId,
    fhir::{self, FhirId, FluxOwnerId},
    try_alloc_slice,
};
use rustc_hir::{self as hir, FnHeader, def_id::LocalDefId};
use rustc_span::Span;

use super::{DesugarCtxt, RustItemCtxt};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

impl<'genv> RustItemCtxt<'_, 'genv, '_> {
    pub fn lift_generics(&mut self) -> fhir::Generics<'genv> {
        let generics = self.genv.hir().get_generics(self.local_id()).unwrap();
        self.lift_generics_inner(generics)
    }

    pub fn lift_generic_param(&mut self, param: &hir::GenericParam) -> fhir::GenericParam<'genv> {
        let kind = match param.kind {
            hir::GenericParamKind::Lifetime { .. } => fhir::GenericParamKind::Lifetime,
            hir::GenericParamKind::Type { default, .. } => {
                fhir::GenericParamKind::Type { default: default.map(|ty| self.lift_ty(ty)) }
            }
            hir::GenericParamKind::Const { ty, .. } => {
                let ty = self.lift_ty(ty);
                fhir::GenericParamKind::Const { ty }
            }
        };
        fhir::GenericParam {
            def_id: self.genv.maybe_extern_id(param.def_id),
            name: param.name,
            kind,
        }
    }

    fn lift_generics_inner(&mut self, generics: &hir::Generics) -> fhir::Generics<'genv> {
        let params = self.genv.alloc_slice_fill_iter(
            generics
                .params
                .iter()
                .map(|param| self.lift_generic_param(param)),
        );

        fhir::Generics { params, refinement_params: &[], predicates: None }
    }

    fn lift_generic_bound(
        &mut self,
        bound: &hir::GenericBound,
    ) -> Result<fhir::GenericBound<'genv>> {
        match bound {
            hir::GenericBound::Trait(poly_trait_ref) => {
                Ok(fhir::GenericBound::Trait(self.lift_poly_trait_ref(*poly_trait_ref)?))
            }
            hir::GenericBound::Outlives(lft) => {
                let lft = self.lift_lifetime(lft);
                Ok(fhir::GenericBound::Outlives(lft))
            }
            _ => Err(self.emit_unsupported(&format!("unsupported generic bound: `{bound:?}`"))),
        }
    }

    fn lift_poly_trait_ref(
        &mut self,
        poly_trait_ref: hir::PolyTraitRef,
    ) -> Result<fhir::PolyTraitRef<'genv>> {
        let modifiers = match poly_trait_ref.modifiers {
            rustc_hir::TraitBoundModifiers {
                constness: rustc_hir::BoundConstness::Never,
                polarity: rustc_hir::BoundPolarity::Positive,
            } => fhir::TraitBoundModifier::None,
            rustc_hir::TraitBoundModifiers {
                constness: rustc_hir::BoundConstness::Never,
                polarity: rustc_hir::BoundPolarity::Maybe(_),
            } => fhir::TraitBoundModifier::Maybe,
            _ => {
                return Err(self.emit_unsupported(&format!(
                    "unsupported trait modifiers: `{:?}`",
                    poly_trait_ref.modifiers,
                )));
            }
        };
        let bound_generic_params = self.genv.alloc_slice_fill_iter(
            poly_trait_ref
                .bound_generic_params
                .iter()
                .map(|param| self.lift_generic_param(param)),
        );
        let trait_ref = self.lift_path(poly_trait_ref.trait_ref.path)?;
        Ok(fhir::PolyTraitRef {
            bound_generic_params,
            refine_params: &[],
            modifiers,
            trait_ref,
            span: poly_trait_ref.span,
        })
    }

    fn lift_opaque_ty(&mut self, opaque_ty: &hir::OpaqueTy) -> Result<fhir::OpaqueTy<'genv>> {
        let bounds =
            try_alloc_slice!(self.genv, &opaque_ty.bounds, |bound| self.lift_generic_bound(bound))?;

        Ok(fhir::OpaqueTy { def_id: MaybeExternId::Local(opaque_ty.def_id), bounds })
    }

    pub fn lift_fn_header(&mut self) -> FnHeader {
        let hir_id = self.genv.tcx().local_def_id_to_hir_id(self.local_id());
        self.genv
            .hir()
            .fn_sig_by_hir_id(hir_id)
            .expect("item does not have a `FnDecl`")
            .header
    }

    pub fn lift_fn_decl(&mut self) -> fhir::FnDecl<'genv> {
        let hir_id = self.genv.tcx().local_def_id_to_hir_id(self.local_id());
        let fn_sig = self
            .genv
            .hir()
            .fn_sig_by_hir_id(hir_id)
            .expect("item does not have a `FnDecl`");

        self.lift_fn_decl_inner(fn_sig.span, fn_sig.decl)
    }

    fn lift_fn_decl_inner(&mut self, span: Span, decl: &hir::FnDecl) -> fhir::FnDecl<'genv> {
        let inputs = self
            .genv
            .alloc_slice_fill_iter(decl.inputs.iter().map(|ty| self.lift_ty(ty)));

        let output =
            fhir::FnOutput { params: &[], ensures: &[], ret: self.lift_fn_ret_ty(&decl.output) };

        fhir::FnDecl { requires: &[], inputs, output, span, lifted: true }
    }

    fn lift_fn_ret_ty(&mut self, ret_ty: &hir::FnRetTy) -> fhir::Ty<'genv> {
        match ret_ty {
            hir::FnRetTy::DefaultReturn(_) => {
                let kind = fhir::TyKind::Tuple(&[]);
                fhir::Ty { kind, span: ret_ty.span() }
            }
            hir::FnRetTy::Return(ty) => self.lift_ty(ty),
        }
    }

    pub fn lift_type_alias(&mut self) -> fhir::Item<'genv> {
        let item = self.genv.hir().expect_item(self.local_id());
        let hir::ItemKind::TyAlias(ty, _) = item.kind else {
            bug!("expected type alias");
        };

        let generics = self.lift_generics();
        let ty = self.lift_ty(ty);
        let ty_alias = fhir::TyAlias { index: None, ty, span: item.span, lifted: true };
        fhir::Item { generics, kind: fhir::ItemKind::TyAlias(ty_alias), owner_id: self.owner }
    }

    pub fn lift_field_def(&mut self, field_def: &hir::FieldDef) -> fhir::FieldDef<'genv> {
        let ty = self.lift_ty(field_def.ty);
        fhir::FieldDef { ty, lifted: true }
    }

    pub fn lift_enum_variant(&mut self, variant: &hir::Variant) -> fhir::VariantDef<'genv> {
        let item = self.genv.hir().expect_item(self.local_id());
        let hir::ItemKind::Enum(_, generics) = &item.kind else { bug!("expected an enum") };

        let fields = self.genv.alloc_slice_fill_iter(
            variant
                .data
                .fields()
                .iter()
                .map(|field| self.lift_field_def(field)),
        );

        let ret = self.lift_variant_ret_inner(generics);

        fhir::VariantDef {
            def_id: variant.def_id,
            params: &[],
            fields,
            ret,
            span: variant.span,
            lifted: true,
        }
    }

    pub fn lift_variant_ret(&mut self) -> fhir::VariantRet<'genv> {
        let item = self.genv.hir().expect_item(self.local_id());
        let hir::ItemKind::Enum(_, generics) = &item.kind else { bug!("expected an enum") };
        self.lift_variant_ret_inner(generics)
    }

    fn lift_variant_ret_inner(&mut self, generics: &hir::Generics) -> fhir::VariantRet<'genv> {
        let kind = fhir::ExprKind::Record(&[]);
        fhir::VariantRet {
            enum_id: self.owner.resolved_id(),
            idx: fhir::Expr {
                kind,
                fhir_id: self.next_fhir_id(),
                span: generics.span.shrink_to_hi(),
            },
        }
    }

    pub fn lift_ty(&mut self, ty: &hir::Ty) -> fhir::Ty<'genv> {
        let kind = match ty.kind {
            hir::TyKind::Slice(ty) => {
                let ty = self.lift_ty(ty);
                let kind = fhir::BaseTyKind::Slice(self.genv.alloc(ty));
                let bty = fhir::BaseTy { kind, fhir_id: self.next_fhir_id(), span: ty.span };
                return fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: ty.span };
            }
            hir::TyKind::Array(ty, len) => {
                let ty = self.lift_ty(ty);
                fhir::TyKind::Array(self.genv.alloc(ty), self.lift_const_arg(len))
            }
            hir::TyKind::Ref(lft, mut_ty) => {
                fhir::TyKind::Ref(self.lift_lifetime(lft), self.lift_mut_ty(mut_ty))
            }
            hir::TyKind::BareFn(bare_fn) => {
                let bare_fn = self.lift_bare_fn(ty.span, bare_fn);
                fhir::TyKind::BareFn(self.genv.alloc(bare_fn))
            }
            hir::TyKind::Never => fhir::TyKind::Never,
            hir::TyKind::Tup(tys) => {
                let tys = self
                    .genv
                    .alloc_slice_fill_iter(tys.iter().map(|ty| self.lift_ty(ty)));
                fhir::TyKind::Tuple(tys)
            }
            hir::TyKind::Path(qpath) => {
                match self.lift_qpath(qpath) {
                    Ok(qpath) => {
                        let bty = fhir::BaseTy::from_qpath(qpath, self.next_fhir_id());
                        fhir::TyKind::BaseTy(bty)
                    }
                    Err(err) => fhir::TyKind::Err(err),
                }
            }
            hir::TyKind::Ptr(mut_ty) => {
                let ty = self.lift_ty(mut_ty.ty);
                fhir::TyKind::RawPtr(self.genv.alloc(ty), mut_ty.mutbl)
            }
            hir::TyKind::OpaqueDef(opaque_ty) => {
                match self.lift_opaque_ty(opaque_ty) {
                    Ok(opaque_ty) => {
                        let opaque_ty = self.insert_opaque_ty(opaque_ty);
                        fhir::TyKind::OpaqueDef(opaque_ty)
                    }
                    Err(err) => fhir::TyKind::Err(err),
                }
            }
            hir::TyKind::TraitObject(poly_traits, lt) => {
                let poly_traits = try_alloc_slice!(self.genv, poly_traits, |poly_trait| {
                    if poly_trait.modifiers != hir::TraitBoundModifiers::NONE {
                        return Err(self.emit_unsupported(&format!(
                            "unsupported type: `{}`",
                            rustc_hir_pretty::ty_to_string(&self.genv.tcx(), ty)
                        )));
                    }
                    self.lift_poly_trait_ref(*poly_trait)
                });
                match poly_traits {
                    Ok(poly_traits) => {
                        let lft = self.lift_lifetime(lt.pointer());
                        fhir::TyKind::TraitObject(poly_traits, lft, lt.tag())
                    }
                    Err(err) => fhir::TyKind::Err(err),
                }
            }
            _ => {
                fhir::TyKind::Err(self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::ty_to_string(&self.genv.tcx(), ty)
                )))
            }
        };
        fhir::Ty { kind, span: ty.span }
    }

    fn lift_bare_fn(&mut self, span: Span, bare_fn: &hir::BareFnTy) -> fhir::BareFnTy<'genv> {
        let generic_params = self.genv.alloc_slice_fill_iter(
            bare_fn
                .generic_params
                .iter()
                .map(|param| self.lift_generic_param(param)),
        );
        let decl = self.lift_fn_decl_inner(span, bare_fn.decl);
        fhir::BareFnTy {
            safety: bare_fn.safety,
            abi: bare_fn.abi,
            generic_params,
            decl: self.genv.alloc(decl),
            param_names: self.genv.alloc_slice(bare_fn.param_names),
        }
    }

    fn lift_lifetime(&self, lft: &hir::Lifetime) -> fhir::Lifetime {
        if let Some(resolved) = self.genv.tcx().named_bound_var(lft.hir_id) {
            fhir::Lifetime::Resolved(resolved)
        } else {
            self.mk_lft_hole()
        }
    }

    fn lift_mut_ty(&mut self, mut_ty: hir::MutTy) -> fhir::MutTy<'genv> {
        let ty = self.lift_ty(mut_ty.ty);
        fhir::MutTy { ty: self.genv.alloc(ty), mutbl: mut_ty.mutbl }
    }

    fn lift_qpath(&mut self, qpath: hir::QPath) -> Result<fhir::QPath<'genv>> {
        match qpath {
            hir::QPath::Resolved(qself, path) => {
                let qself = if let Some(ty) = qself {
                    let ty = self.lift_ty(ty);
                    Some(self.genv.alloc(ty))
                } else {
                    None
                };
                let path = self.lift_path(path)?;
                Ok(fhir::QPath::Resolved(qself, path))
            }
            hir::QPath::TypeRelative(qself, segment) => {
                let qself = self.lift_ty(qself);
                let segment = self.lift_path_segment(segment)?;
                Ok(fhir::QPath::TypeRelative(self.genv.alloc(qself), self.genv.alloc(segment)))
            }
            hir::QPath::LangItem(_, _) => {
                Err(self.emit_unsupported(&format!(
                    "unsupported type: `{}`",
                    rustc_hir_pretty::qpath_to_string(&self.genv.tcx(), &qpath)
                )))
            }
        }
    }

    fn lift_path(&mut self, path: &hir::Path) -> Result<fhir::Path<'genv>> {
        let Ok(res) = path.res.try_into() else {
            return Err(self.emit_unsupported(&format!("unsupported res: `{:?}`", path.res)));
        };
        let segments =
            try_alloc_slice!(self.genv, path.segments, |segment| self.lift_path_segment(segment))?;

        Ok(fhir::Path { res, fhir_id: self.next_fhir_id(), segments, refine: &[], span: path.span })
    }

    fn lift_path_segment(
        &mut self,
        segment: &hir::PathSegment,
    ) -> Result<fhir::PathSegment<'genv>> {
        let Ok(res) = segment.res.try_into() else {
            return Err(self.emit_unsupported(&format!("unsupported res: `{:?}`", segment.res)));
        };
        let (args, bindings) = {
            match segment.args {
                Some(args) => {
                    (
                        self.lift_generic_args(args.args)?,
                        self.lift_assoc_item_constraints(args.constraints)?,
                    )
                }
                None => ([].as_slice(), [].as_slice()),
            }
        };

        Ok(fhir::PathSegment { res, ident: segment.ident, args, constraints: bindings })
    }

    fn lift_generic_args(
        &mut self,
        args: &[hir::GenericArg<'_>],
    ) -> Result<&'genv [fhir::GenericArg<'genv>]> {
        try_alloc_slice!(self.genv, args, |arg| {
            match arg {
                hir::GenericArg::Lifetime(lft) => {
                    let lft = self.lift_lifetime(lft);
                    Ok(fhir::GenericArg::Lifetime(lft))
                }
                hir::GenericArg::Type(ty) => {
                    let ty = self.lift_ty(ty.as_unambig_ty());
                    Ok(fhir::GenericArg::Type(self.genv.alloc(ty)))
                }
                hir::GenericArg::Const(const_arg) => {
                    Ok(fhir::GenericArg::Const(self.lift_const_arg(const_arg.as_unambig_ct())))
                }
                hir::GenericArg::Infer(_) => {
                    Err(self.emit_unsupported("unsupported inference generic argument"))
                }
            }
        })
    }

    fn lift_assoc_item_constraints(
        &mut self,
        constraints: &[hir::AssocItemConstraint<'_>],
    ) -> Result<&'genv [fhir::AssocItemConstraint<'genv>]> {
        try_alloc_slice!(self.genv, constraints, |cstr| {
            let hir::AssocItemConstraintKind::Equality { term } = cstr.kind else {
                return Err(self.emit_unsupported("unsupported type binding"));
            };
            let hir::Term::Ty(term) = term else {
                return Err(self.emit_unsupported("unsupported type binding"));
            };
            let kind = fhir::AssocItemConstraintKind::Equality { term: self.lift_ty(term) };
            Ok(fhir::AssocItemConstraint { ident: cstr.ident, kind })
        })
    }

    fn lift_const_arg(&mut self, const_arg: &hir::ConstArg) -> fhir::ConstArg {
        fhir::ConstArg { kind: fhir::ConstArgKind::Infer, span: const_arg.span() }
    }

    #[track_caller]
    fn emit_unsupported(&self, note: &str) -> ErrorGuaranteed {
        let tcx = self.genv.tcx();
        let local_id = self.owner.local_id().def_id;
        let span = tcx.def_span(local_id);
        let def_kind = tcx.def_descr(local_id.to_def_id());
        self.emit(errors::UnsupportedHir { span, def_kind, note })
    }

    fn next_fhir_id(&self) -> FhirId {
        FhirId {
            owner: FluxOwnerId::Rust(self.owner.local_id()),
            local_id: self.local_id_gen.fresh(),
        }
    }

    fn local_id(&self) -> LocalDefId {
        self.owner.local_id().def_id
    }

    fn lift_fn_sig(&mut self, fn_sig: hir::FnSig) -> fhir::FnSig<'genv> {
        let decl = self.lift_fn_decl_inner(fn_sig.span, fn_sig.decl);
        fhir::FnSig {
            header: fn_sig.header,
            qualifiers: &[],
            reveals: &[],
            decl: self.genv.alloc(decl),
        }
    }

    pub fn lift_foreign_item(
        &mut self,
        foreign_item: hir::ForeignItem,
    ) -> Result<fhir::ForeignItem<'genv>> {
        let hir::ForeignItemKind::Fn(fnsig, _, _) = foreign_item.kind else {
            return Err(self.emit_unsupported("Static and type in extern_item are not supported."));
        };

        let lifted_fnsig = self.lift_fn_sig(fnsig);
        let fnsig = self.genv.alloc(lifted_fnsig);
        let lifted_generics = self.lift_generics();
        let generics = self.genv.alloc(lifted_generics);
        let kind = fhir::ForeignItemKind::Fn(*fnsig, generics);

        Ok(fhir::ForeignItem {
            ident: foreign_item.ident,
            kind,
            owner_id: MaybeExternId::Local(foreign_item.owner_id),
            span: foreign_item.span,
        })
    }
}

pub mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(desugar_unsupported_hir, code = E0999)]
    #[note]
    pub(super) struct UnsupportedHir<'a> {
        #[primary_span]
        #[label]
        pub span: Span,
        pub def_kind: &'static str,
        pub note: &'a str,
    }
}
